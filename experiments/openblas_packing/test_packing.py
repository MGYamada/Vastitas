import copy
import os
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from experiments.openblas_packing.verify import calibration, check_patch, replay, union_area, verify, workspace


def fixture():
    backing={'kind':'workspace','buffer_bytes':8192,'page_bytes':4096,
             'observer_static_bytes':163873,'event_capacity':4096,'events':[]}
    phase=0
    def event(op,ptr=0,size=0):
        backing['events'].append({'sequence':len(backing['events']),'phase':phase,
            'operation':op,'address':hex(ptr),'bytes':size,'ok':1,'errno':0})
    event('mmap',0x12000,8192)
    phase=10; event('mark')
    phase=11; event('mark'); event('borrow',0x12000,8192); event('return',0x12000,8192)
    phase=12; event('mark')
    phase=18; event('mark'); event('shutdown_begin'); event('munmap',0x12000,8192); event('shutdown_end')
    phase=19; event('mark')
    route={'path':'packed','components':1,'m':2,'n':2,'k':2,'ta':0,'tb':0,
           'a':'0x100000','b':'0x200000','c':'0x300000','lda':5,'ldb':5,'ldc':5,'before':3,'after':5}
    calls=[{'kernel':'dgemm_itcopy','role':0,'components':1,'m':2,'n':2,'lda':5,
            'source':'0x100000','destination':'0x12000','before':4,'after':4,'route':0},
           {'kernel':'dgemm_oncopy','role':1,'components':1,'m':2,'n':2,'lda':5,
            'source':'0x200000','destination':'0x12100','before':4,'after':4,'route':0}]
    metadata={'pool_entries':50,'memory_entry_bytes':64,'memory_array_bytes':3200,
              'release_entry_bytes':24,'release_array_bytes':1200,'declared_bytes':{
                  'memory':3200,'release_info':1200,'newmemory':8,'new_release_info':8,
                  'release_pos':4,'alloc_lock':8,'base_address':8,'memory_initialized':4,
                  'memory_overflowed':4,'hugetlb_allocated':4,'gotoblas_initialized':4}}
    packing={'kind':'packing','schema':1,'observer_static_bytes':1339420,'call_capacity':16384,
             'route_capacity':256,'metadata':metadata,'routes':[route],'calls':calls}
    kernels=calibration({'D_M':8,'D_N':4,'Z_M':4,'Z_N':4})['kernels']
    return packing,backing,kernels


class PackingReplay(unittest.TestCase):
    def test_exact_regions_and_logical_payload(self):
        result=replay(*fixture())
        self.assertEqual(result['routes'],[{'path':'packed','calls':2,'logical_payload_bytes':[32,32]}])
        self.assertEqual(result['declared_metadata_bytes'],4452)

    def reject(self,change,pattern):
        p,b,k=fixture(); change(p,b,k)
        with self.assertRaisesRegex(ValueError,pattern): replay(p,b,k)

    def test_repacking_is_charged_again(self):
        p,b,k=fixture(); p['calls'].insert(1,copy.deepcopy(p['calls'][0]))
        self.assertEqual(replay(p,b,k)['routes'][0]['logical_payload_bytes'],[64,32])

    def test_shortcut_cost_is_unavailable(self):
        p,b,k=fixture(); p['calls']=[]; p['routes'][0].update(path='gemv',m=1)
        self.assertIsNone(replay(p,b,k)['routes'][0]['logical_payload_bytes'])

    def test_empty_cannot_hide_workspace_operations(self):
        self.reject(lambda p,b,k:(p.update(calls=[]),p['routes'][0].update(path='empty',m=0)), 'empty route performed')

    def test_padding_is_not_an_input_region(self):
        self.reject(lambda p,b,k:p['calls'][0].update(source='0x100010'),'outside input rectangle')

    def test_stride_cannot_be_relabelled(self):
        self.reject(lambda p,b,k:p['calls'][0].update(lda=2),'source alignment/stride')

    def test_pointer_cannot_precede_input(self):
        self.reject(lambda p,b,k:p['calls'][0].update(source='0xffff8'),'source alignment/stride')

    def test_copy_must_fit_actual_loan(self):
        self.reject(lambda p,b,k:p['calls'][0].update(destination='0x13ff0'),'outside live loan')

    def test_returned_capacity_is_not_permission(self):
        self.reject(lambda p,b,k:[c.update(before=5,after=5) for c in p['calls']],'outside live loan')

    def test_copy_interval_cannot_hide_allocation(self):
        self.reject(lambda p,b,k:p['calls'][0].update(after=5),'copy interval/route')

    def test_missing_input_copy_fails_coverage(self):
        self.reject(lambda p,b,k:p['calls'].pop(0),'incomplete input packing coverage')

    def test_unknown_kernel_is_not_counted(self):
        self.reject(lambda p,b,k:p['calls'][0].update(kernel='fast_copy'),'uncalibrated packing kernel')

    def test_role_must_match_kernel_and_transpose(self):
        self.reject(lambda p,b,k:p['calls'][0].update(role=1),'packing role/kernel')
        self.reject(lambda p,b,k:p['routes'][0].update(ta=1),'packing role/kernel')

    def test_calibrated_real_kernel_cannot_count_complex_bytes(self):
        self.reject(lambda p,b,k:p['calls'][0].update(components=2),'copy domain')

    def test_copy_must_belong_to_actual_route(self):
        self.reject(lambda p,b,k:p['calls'][0].update(route=1),'packing route index')
        self.reject(lambda p,b,k:p['routes'][0].update(path='small'),'copy interval/route')

    def test_shutdown_is_outside_operation(self):
        self.reject(lambda p,b,k:p['routes'][0].update(after=10),'route crosses phase')

    def test_metadata_units_and_coverage(self):
        self.reject(lambda p,b,k:p['metadata'].update(memory_array_bytes=64),'metadata array units')
        self.reject(lambda p,b,k:p['metadata']['declared_bytes'].pop('alloc_lock'),'declared metadata coverage')

    def test_bool_count_is_not_an_integer_count(self):
        self.reject(lambda p,b,k:p['calls'][0].update(m=True),'invalid m')

    def test_huge_span_overflow_is_rejected(self):
        self.reject(lambda p,b,k:p['calls'][0].update(m=2**63),'outside live loan')

    def test_union_counts_overlap_once_but_keeps_holes(self):
        self.assertEqual(union_area([(0,0,2,2),(1,1,2,2)]),7)
        self.assertEqual(union_area([(0,0,2,1),(0,2,2,1)]),4)


class FullRecord(unittest.TestCase):
    @unittest.skipUnless(os.environ.get('VASTITAS_PACKING_RECORD'),'requires a freshly retained record')
    def test_exact_record(self):
        result=verify(Path(os.environ['VASTITAS_PACKING_RECORD']))
        self.assertEqual(result['executions'],1828)
        self.assertGreater(result['packing_calls'],0)
        self.assertFalse(result['timing'])

    @unittest.skipUnless(os.environ.get('VASTITAS_PACKING_RECORD'),'requires a freshly retained record')
    def test_missing_memory_hook_is_not_accepted_by_inverse_patch(self):
        base=workspace.Reader(Path(os.environ['VASTITAS_PACKING_RECORD']))
        class Changed:
            def read(self,name):
                data=base.read(name)
                if name=='inputs/upstream/diagnostic/driver/others/memory.c':
                    return data.replace(b'vobs_malloc(',b'malloc(',1)
                return data
        with self.assertRaisesRegex(ValueError,'backing hook coverage'): check_patch(Changed())

    @unittest.skipUnless(os.environ.get('VASTITAS_PACKING_RECORD'),'requires a freshly retained record')
    def test_wrong_copy_role_is_not_accepted_by_inverse_patch(self):
        base=workspace.Reader(Path(os.environ['VASTITAS_PACKING_RECORD']))
        class Changed:
            def read(self,name):
                data=base.read(name)
                if name=='inputs/upstream/diagnostic/driver/level3/level3.c':
                    return data.replace(b'VPACK_CALL(0,',b'VPACK_CALL(1,',1)
                return data
        with self.assertRaisesRegex(ValueError,'copy role hook coverage'): check_patch(Changed())


if __name__=='__main__': unittest.main()
