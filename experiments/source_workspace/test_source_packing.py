import copy
import hashlib
import json
import os
from pathlib import Path
import unittest

from verify import backend, check_calls, packing, verify_reader
from test_source_workspace import Overlay, fixture as source_fixture
from experiments.openblas_packing.test_packing import fixture as backend_fixture


def fixture():
    trace, backing, case = source_fixture()
    observed, _, kernels = backend_fixture()
    trace['schema'] = 2
    observed['routes'], observed['calls'] = [], []
    for index, call in enumerate(trace['calls']):
        call['addresses'] = ['0x100000', '0x200000', '0x300000']
        m, n, k = call['shape']
        lda, ldb, ldc = call['leading']
        observed['routes'].append(dict(path='packed', components=2, m=m, n=n, k=k,
            ta=0, tb=0, a=call['addresses'][0], b=call['addresses'][1], c=call['addresses'][2],
            lda=lda, ldb=ldb, ldc=ldc, before=call['begin'], after=call['end']))
        for role, kernel, rows, cols, stride in ((0, 'zgemm_otcopy', k, m, lda),
                                                 (1, 'zgemm_oncopy', k, n, ldb)):
            observed['calls'].append(dict(kernel=kernel, role=role, components=2, m=rows, n=cols,
                lda=stride, source=call['addresses'][role], destination=hex(0x10000+role*4096),
                before=call['end']-1, after=call['end']-1, route=index))
    return trace, observed, backing, kernels, case


class SourcePacking(unittest.TestCase):
    def replay(self, trace, observed, backing, kernels):
        return packing.replay(trace, observed, backing, kernels, backend_fixture()[0]['metadata'])

    def reject(self, change, pattern):
        trace, observed, backing, kernels, _ = fixture()
        change(trace, observed)
        with self.assertRaisesRegex(ValueError, pattern): self.replay(trace, observed, backing, kernels)

    def test_source_addresses_bind_actual_backend_routes(self):
        trace, observed, backing, kernels, case = fixture()
        check_calls(trace, backing, case, 1, with_packing=True)
        result = self.replay(trace, observed, backing, kernels)
        self.assertEqual(result['routes'][0]['logical_payload_bytes'], [384, 240])
        self.assertEqual(result['routes'][2], result['routes'][0])

    def test_foreign_actual_pointer_is_rejected(self):
        self.reject(lambda t,p:t['calls'][0]['addresses'].__setitem__(0,'0x900000'), 'address binding')

    def test_call_span_cannot_be_shifted(self):
        self.reject(lambda t,p:t['calls'][0].update(begin=2), 'call span')

    def test_changed_coefficients_cannot_reuse_coverage(self):
        self.reject(lambda t,p:t['calls'][0]['alpha'].__setitem__(0,'0000000000000000'), 'coefficients')

    def test_transform_cannot_be_relabelled(self):
        self.reject(lambda t,p:t['calls'][0]['transforms'].__setitem__(0,112), 'transform')

    def test_other_phase_cannot_claim_the_same_calls(self):
        self.reject(lambda t,p:t['calls'][0].update(phase=3), 'phase')

    def test_missing_route_is_rejected(self):
        self.reject(lambda t,p:t['calls'].pop(), 'route coverage')

    def test_metadata_must_match_calibrated_backend(self):
        self.reject(lambda t,p:p['metadata']['declared_bytes'].update(alloc_lock=64), 'uncalibrated packing metadata')

    def test_old_call_schema_has_no_packing_authority(self):
        self.reject(lambda t,p:t.update(schema=1), 'address-bearing')

    def test_null_is_required_for_unobserved_stock(self):
        trace, observed, backing, kernels, case = fixture()
        trace['backend_events_observed'] = False
        for call in trace['calls']: call.update(begin=None,end=None)
        check_calls(trace,None,case,1,with_packing=True)
        self.assertIsNone(self.replay(trace,None,None,kernels))
        with self.assertRaisesRegex(ValueError,'absent from diagnostic'):
            self.replay(trace,None,backing,kernels)

    def test_addresses_are_not_compared_across_processes(self):
        trace, _, backing, _, case = fixture()
        other = copy.deepcopy(trace)
        other['calls'][0]['addresses'][0] = '0x500000'
        self.assertEqual(check_calls(trace,backing,case,1,with_packing=True),
                         check_calls(other,backing,case,1,with_packing=True))
        other['calls'][0]['addresses'][0] = '0x1'
        with self.assertRaisesRegex(ValueError,'address domain'):
            check_calls(other,backing,case,1,with_packing=True)


def footprint_fixture():
    _, observed, _, kernels, _ = fixture()
    rows = [{'packing':observed}]
    data = b'calibration source'
    digest = hashlib.sha256(data).hexdigest()
    unroll = {'D_M':8,'D_N':4,'Z_M':4,'Z_N':4}
    calibrated = {'repository':{'inputs':{packing.SOURCE:{'sha256':digest}}},
                  'builds':{v:{'unroll':unroll} for v in ('stock','diagnostic')}}
    binding = dict(schema=1,claims=packing.CLAIMS,build_dir='/record/.lake/source-packing',
                   binaries=[],footprints=[])
    record = dict(packing=binding,host={'cc':'/cc'},inputs={packing.SOURCE:digest},
                  prefixes={v:'/backend/'+v for v in ('stock','diagnostic')})
    commands = []
    definitions = {k['name']:k for k in kernels}
    for variant in ('stock','diagnostic'):
        for sanitized in (False,True):
            name = variant+'-calibration'+('-sanitized' if sanitized else '')
            binary = binding['build_dir']+'/'+name
            binding['binaries'].append(dict(variant=variant,sanitized=sanitized,name=name,bytes=1,sha256='0'*64))
            commands.append(dict(phase='source_packing_build',returncode=0,command=[record['host']['cc'],
                *packing.FLAGS,*['-DVP_'+k+'='+str(v) for k,v in sorted(unroll.items())],
                *(packing.SANITIZERS if sanitized else []),'/record/source/'+packing.SOURCE,
                record['prefixes'][variant]+'/lib/libopenblas.a','-lm','-lpthread','-o',binary]))
            for contract in sorted(packing.contracts(rows)):
                kernel,m,n,lda=contract
                definition=definitions[kernel]
                result=dict(kind='observed_kernel_footprint',kernel=kernel,m=m,n=n,lda=lda,
                    checked_input_words=lda*(m if definition['transpose'] else n)*definition['components'],
                    checked_output_words=m*n*definition['components'])
                binding['footprints'].append(dict(variant=variant,sanitized=sanitized,contract=list(contract),result=result))
                commands.append(dict(phase='source_packing_footprint',returncode=0,
                    command=[binary,*map(str,contract)],stdout=json.dumps(result)))
    class Reader:
        names=set()
        def read(self,name):
            assert name=='source/'+packing.SOURCE
            return data
    return Reader(),record,rows,calibrated,kernels,commands


class SourceFootprints(unittest.TestCase):
    def test_all_actual_shapes_and_strides_checked_on_four_binaries(self):
        result=packing.check_footprints(*footprint_fixture())
        self.assertEqual(result,dict(contracts=4,executions=16))

    def reject(self,change,pattern):
        args=footprint_fixture()
        change(args[1],args[5])
        with self.assertRaisesRegex(ValueError,pattern):packing.check_footprints(*args)

    def test_missing_footprint_rejected(self):
        self.reject(lambda r,c:r['packing']['footprints'].pop(),'footprint coverage')

    def test_duplicate_contract_cannot_fill_coverage(self):
        self.reject(lambda r,c:r['packing']['footprints'].__setitem__(1,copy.deepcopy(r['packing']['footprints'][0])),
                    'footprint identity')

    def test_actual_stride_must_match_execution(self):
        def change(r,c):
            next(x for x in c if x['phase']=='source_packing_footprint')['command'][-1]='999'
        self.reject(change,'footprint command/output')

    def test_sanitizer_flags_are_required(self):
        def change(r,c):
            next(x for x in c if '-fsanitize=address,undefined' in x['command'])['command'].remove('-fsanitize=address,undefined')
        self.reject(change,'compile/link receipt')

    def test_calibration_must_link_exact_backend(self):
        self.reject(lambda r,c:c[0]['command'].__setitem__(-5,'/foreign/libopenblas.a'),'compile/link receipt')

    def test_failed_footprint_is_rejected(self):
        self.reject(lambda r,c:next(x for x in c if x['phase']=='source_packing_footprint').update(returncode=1),
                    'footprint command/output')

    def test_relabelled_output_footprint_is_rejected(self):
        self.reject(lambda r,c:r['packing']['footprints'][0]['result'].update(checked_output_words=1),
                    'footprint command/output')


@unittest.skipUnless(os.environ.get('VASTITAS_SOURCE_PACKING_RECORD'),'full source packing record not supplied')
class FullSourcePacking(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reader=backend.Reader(Path(os.environ['VASTITAS_SOURCE_PACKING_RECORD']))

    def check(self,reader):
        return verify_reader(reader,allow_build_tree=self.reader.zip is None)

    def test_complete_execution_and_actual_footprint_replay(self):
        summary=self.check(self.reader)
        self.assertEqual(summary['selection'],'full')
        self.assertEqual(summary['cases'],12)
        self.assertGreater(summary['packing']['observed_footprints']['contracts'],0)
        self.assertFalse(summary['claims']['total_heap'])

    def test_rehashed_source_pointer_cannot_name_another_allocation(self):
        reader=Overlay(self.reader)
        rows=reader.json('observations.json')
        call=next(row for row in rows['rows'] if row['packing'] is not None)['calls']['calls'][0]
        call['addresses'][0]=hex(int(call['addresses'][0],16)+8)
        reader.replace('observations.json',rows)
        with self.assertRaisesRegex(ValueError,'address binding'):self.check(reader)

    def test_older_schema_cannot_silently_ignore_packing(self):
        reader=Overlay(self.reader)
        record=reader.json('record.json');record['schema']=2
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'packing needs schema 3'):self.check(reader)

    def test_backend_fixture_coverage_cannot_replace_source_footprints(self):
        reader=Overlay(self.reader)
        record=reader.json('record.json');record['packing']['footprints'].pop()
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'footprint coverage'):self.check(reader)
