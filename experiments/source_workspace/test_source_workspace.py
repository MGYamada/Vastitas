import copy
import hashlib
import json
from pathlib import Path
import unittest

from verify import backend, check_calls, check_input, verify


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


if __name__=='__main__': unittest.main()
