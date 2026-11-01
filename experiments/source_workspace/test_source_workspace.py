import copy
import hashlib
import json
from pathlib import Path
import unittest

from verify import backend, check_allocation, check_backend_pair, check_calls, check_input, verify, verify_reader


def fixture():
    # A smaller synthetic pool makes the retained backing distinct from the
    # four finite source calls. Real retained records exercise actual CBLAS.
    case={'i':2,'k':3,'j':4,'a':5,'b':6,'pad':1,'scalar':1}
    row={'kind':'workspace','buffer_bytes':8192,'page_bytes':4096,
         'observer_static_bytes':163869,'event_capacity':4096,'events':[]}
    trace={'kind':'source_cblas_calls','schema':1,'backend_events_observed':True,
           'observer_static_bytes':24596,'capacity':256,'calls':[]}
    events=row['events']
    phase=0

    def event(op,address=0,size=0):
        events.append(dict(sequence=len(events),phase=phase,operation=op,address=hex(address),bytes=size,ok=1,errno=0))

    def mark(p):
        nonlocal phase
        phase=p
        event('mark')

    for step in range(4):
        if step==0: mark(11)
        if step==2: mark(12);mark(13)
        lo=len(events)
        if step==0: event('mmap',0x10000,8192)
        event('borrow',0x10000,8192);event('return',0x10000,8192)
        trace['calls'].append(dict(sequence=step,phase=1 if step<2 else 3,scalar=1,order=102,
            transforms=[111,111],shape=[8,5,3] if step%2==0 else [10,6,4],
            leading=[13,6,14] if step%2==0 else [18,8,17],
            alpha=['3ff0000000000000','0000000000000000'],beta=['0000000000000000']*2,
            begin=lo,end=len(events)))
    mark(14);mark(18);event('shutdown_begin');event('munmap',0x10000,8192);event('shutdown_end');mark(19)
    return trace,row,case


class SourceCallReplay(unittest.TestCase):
    def test_all_calls_return_while_backing_remains_retained(self):
        trace,row,case=fixture()
        self.assertEqual(len(check_calls(trace,row,case,1)),4)
        observed=backend.replay(row)
        self.assertEqual(observed['before_shutdown'],dict(mmap_bytes=8192,malloc_requested_bytes=0,borrowed_capacity_bytes=0))

    def reject(self,mutate,pattern):
        trace,row,case=fixture()
        mutate(trace,row)
        with self.assertRaisesRegex(ValueError,pattern):check_calls(trace,row,case,1)

    def test_extra_call_cannot_be_hidden_by_repetition_label(self):
        self.reject(lambda t,r:t['calls'].pop(),'missing/extra')

    def test_loan_return_in_next_call_is_rejected(self):
        def mutate(t,r):
            t['calls'][0]['end']-=1
            t['calls'][1]['begin']-=1
        self.reject(mutate,'loan escaped')

    def test_backing_event_without_call_is_rejected(self):
        self.reject(lambda t,r:t['calls'][0].update(begin=2),'no actual CBLAS call')

    def test_duplicate_event_attribution_is_rejected(self):
        self.reject(lambda t,r:t['calls'][1].update(begin=1),'overlapping/reordered')

    def test_actual_leading_dimension_is_required(self):
        self.reject(lambda t,r:t['calls'][1]['leading'].__setitem__(0,10),'shape/layout')

    def test_actual_complex_coefficients_are_required(self):
        self.reject(lambda t,r:t['calls'][0]['alpha'].__setitem__(1,'3ff0000000000000'),'coefficients')

    def test_cold_call_cannot_be_relabelled_as_reuse(self):
        self.reject(lambda t,r:t['calls'][0].update(phase=3),'call identity')

    def test_out_of_bounds_event_cursor_is_rejected(self):
        self.reject(lambda t,r:t['calls'][-1].update(end=len(r['events'])+1),'interval bounds')

    def test_boolean_is_not_an_event_offset(self):
        self.reject(lambda t,r:t['calls'][0].update(begin=True),'event start')

    def test_unobserved_stock_events_are_null(self):
        trace,_,case=fixture()
        trace['backend_events_observed']=False
        for call in trace['calls']:call.update(begin=None,end=None)
        self.assertEqual(len(check_calls(trace,None,case,1)),4)
        trace['calls'][0].update(begin=0,end=0)
        with self.assertRaisesRegex(ValueError,'unobserved is not zero'):
            check_calls(trace,None,case,1)

    def test_empty_interval_is_possible_without_zero_retention(self):
        trace,row,case=fixture()
        call=trace['calls'][3]
        del row['events'][call['begin']:call['end']]
        call['end']=call['begin']
        for i,e in enumerate(row['events']):e['sequence']=i
        check_calls(trace,row,case,1)
        self.assertEqual(backend.replay(row)['before_shutdown']['mmap_bytes'],8192)

    def test_stdin_binding_rejects_other_checked_source(self):
        wire=b'{"version":8,"source":"original"}'
        command={'stdin':{'bytes':len(wire),'sha256':hashlib.sha256(wire).hexdigest()}}
        check_input(command,wire)
        with self.assertRaisesRegex(ValueError,'actual kernel input'):
            check_input(command,wire.replace(b'original',b'replaced'))

    def test_valid_extra_backend_allocation_cannot_hide_in_matched_pair(self):
        _,row,_=fixture()
        changed=copy.deepcopy(row)
        position=next(i for i,e in enumerate(changed['events']) if e['phase']==13 and e['operation']=='borrow')
        template=changed['events'][position]
        changed['events'][position:position]=[
            dict(template,operation='malloc',address='0x30000',bytes=4096),
            dict(template,operation='free',address='0x30000',bytes=0)]
        for i,e in enumerate(changed['events']):e['sequence']=i
        backend.replay(changed)  # Individually valid cleanup still changes cost.
        with self.assertRaisesRegex(ValueError,'backend cost mismatch'):
            check_backend_pair(row,changed)


class Overlay:
    """Rehash modified evidence so regressions reach semantic replay checks."""
    def __init__(self,reader):
        self.reader,self.names,self.changed=reader,reader.names,{}

    def read(self,name):return self.changed[name] if name in self.changed else self.reader.read(name)
    def json(self,name):return json.loads(self.read(name))

    def replace(self,name,value):
        data=(json.dumps(value,indent=2)+'\n').encode()
        self.changed[name]=data
        if name!='record.json':
            record=self.json('record.json')
            record['files'][name]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
            self.replace('record.json',record)


class RetainedSourceRecords(unittest.TestCase):
    root=Path(__file__).resolve().parent/'results'

    @classmethod
    def setUpClass(cls):
        cls.reader=backend.Reader(cls.root/'2026-11-01-macos/evidence.zip')

    def test_both_full_records_match_manifests(self):
        for platform in ('macos','linux'):
            with self.subTest(platform=platform):
                path=self.root/('2026-11-01-'+platform)
                manifest=json.loads((path/'artifact-manifest.json').read_text())
                data=(path/'evidence.zip').read_bytes()
                self.assertEqual(len(data),manifest['bytes'])
                self.assertEqual(hashlib.sha256(data).hexdigest(),manifest['sha256'])
                self.assertEqual(verify(path/'evidence.zip'),manifest['summary'])
                self.assertEqual(manifest['measured_head'],manifest['backend_head'])
                self.assertEqual(manifest['measured_status'],'')

    def test_rehashed_foreign_kernel_input_fails(self):
        reader=Overlay(self.reader)
        commands=reader.json('commands.json')
        next(c for c in commands if c['phase']=='kernel_emit')['stdin']['sha256']='0'*64
        reader.replace('commands.json',commands)
        with self.assertRaisesRegex(ValueError,'actual kernel input'):verify_reader(reader)

    def test_backend_digest_must_match_nested_calibration(self):
        reader=Overlay(self.reader)
        record=reader.json('record.json')
        record['backend_archives']['diagnostic']='0'*64
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'uncalibrated backend'):verify_reader(reader)

    def test_omitted_executable_fingerprint_fails(self):
        reader=Overlay(self.reader)
        record=reader.json('record.json')
        record['binaries'].pop(next(iter(record['binaries'])))
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'executable fingerprint coverage'):verify_reader(reader)

    def test_balanced_setup_churn_is_not_ignored(self):
        observations=self.reader.json('observations.json')
        row=next(r for r in observations['rows'] if r['implementation']=='generated' and r['scope']==1)
        case=next(c for c in self.reader.json('cases.json') if c['case']==row['case'])
        check_allocation(row,case)
        row['allocation']['phases']['setup']['kinds']['generated_ctor'].update(
            allocations=1,bytes=16,final_releases=1,released_bytes=16)
        with self.assertRaisesRegex(ValueError,'outside run: setup'):check_allocation(row,case)

    def test_full_heap_claim_is_rejected(self):
        reader=Overlay(self.reader)
        record=reader.json('record.json');record['claims']['total_heap']=True
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'unsupported claim'):verify_reader(reader)

    def test_archive_cannot_smuggle_an_unlisted_lake_file(self):
        reader=Overlay(self.reader)
        reader.names=reader.names|{'programs/unlisted/.lake/extra'}
        reader.changed['programs/unlisted/.lake/extra']=b'unlisted bytes'
        with self.assertRaisesRegex(ValueError,'only compact evidence'):verify_reader(reader)


if __name__=='__main__': unittest.main()
