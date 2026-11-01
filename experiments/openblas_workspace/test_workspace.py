import copy
import unittest

from verify import check_calibration, replay


def fixture():
    row = {'kind':'workspace','buffer_bytes':8192,'page_bytes':4096,
           'observer_static_bytes':163873,'event_capacity':4096,'events':[]}
    events, phase = row['events'], 0

    def event(op, address=0, size=0):
        events.append({'sequence':len(events),'phase':phase,'operation':op,
                       'address':hex(address),'bytes':size,'ok':1,'errno':0})

    def mark(p):
        nonlocal phase
        phase = p
        event('mark')

    # Constructor allocation with alignment trimming on both sides. The pool
    # retains the middle 8192 bytes at 0x12000 after the borrowed region returns.
    event('mmap',0x10000,32768)
    event('munmap',0x10000,8192)
    event('munmap',0x14000,16384)
    event('borrow',0x12000,8192)
    event('return',0x12000,8192)
    mark(10)
    mark(11); event('borrow',0x12000,8192)
    mark(12); event('mmap',0x30000,8192); event('borrow',0x30000,8192)
    mark(13); event('return',0x12000,8192)
    mark(14); event('borrow',0x12000,8192)
    mark(15); event('return',0x30000,8192); event('return',0x12000,8192)
    mark(16); event('malloc',0x50000,12288); event('direct_borrow',0x50000,8192)
    mark(17); event('direct_return',0x50000,8192); event('free',0x50000)
    mark(18); event('shutdown_begin'); event('munmap',0x12000,8192); event('munmap',0x30000,8192); event('shutdown_end')
    mark(19)
    return row


class WorkspaceReplay(unittest.TestCase):
    def test_retained_capacity_and_transient_mapping_peak_are_different(self):
        result = replay(fixture())
        check_calibration(result)
        self.assertEqual(result['peak'],{'mmap_bytes':32768,'malloc_requested_bytes':12288,'borrowed_capacity_bytes':16384})
        self.assertEqual(result['before_shutdown'],{'mmap_bytes':16384,'malloc_requested_bytes':0,'borrowed_capacity_bytes':0})

    def reject(self, mutate, pattern):
        row = copy.deepcopy(fixture())
        mutate(row)
        with self.assertRaisesRegex(ValueError,pattern): replay(row)

    def test_missing_constructor_hook_is_not_zero_backing(self):
        def mutate(r):
            r['events'].pop(0)
            for i,e in enumerate(r['events']): e['sequence'] = i
        self.reject(mutate,'uncovered munmap')

    def test_unmapping_an_active_loan_fails(self):
        def mutate(r):
            e = next(e for e in r['events'] if e['phase'] == 13 and e['operation'] == 'return')
            e['operation'] = 'munmap'
        self.reject(mutate,'unmap during borrow')

    def test_returning_wrong_pointer_fails(self):
        def mutate(r):
            next(e for e in r['events'] if e['phase'] == 13 and e['operation'] == 'return')['address'] = '0x14000'
        self.reject(mutate,'unmatched/double return')

    def test_overlapping_pool_loans_fail(self):
        def mutate(r):
            next(e for e in r['events'] if e['phase'] == 12 and e['operation'] == 'borrow')['address'] = '0x12000'
        self.reject(mutate,'overlapping active loans')

    def test_partially_unobserved_unmap_fails(self):
        self.reject(lambda r:r['events'][1].update(bytes=36864),'uncovered munmap')

    def test_shutdown_must_release_retained_backing(self):
        def mutate(r):
            e = next(e for e in r['events'] if e['phase'] == 18 and e['operation'] == 'munmap')
            e.update(ok=0,errno=22)
        self.reject(mutate,'unreleased backing')

    def test_success_domain_is_not_boolean(self):
        self.reject(lambda r:r['events'][0].update(ok=True),'success domain')

    def test_log_overflow_or_truncation_fails(self):
        self.reject(lambda r:r.update(event_capacity=1),'event capacity')
        self.reject(lambda r:r['events'].pop(),'incomplete lifetime')

    def test_failed_mapping_is_not_counted_as_backing(self):
        row = fixture()
        failed = dict(row['events'][0],operation='mmap',address=hex(2**64-1),ok=0,errno=12)
        row['events'].insert(0,failed)
        for i,e in enumerate(row['events']): e['sequence'] = i
        result = replay(row)
        check_calibration(result)
        self.assertEqual(result['peak']['mmap_bytes'],32768)

    def test_marker_does_not_silently_change_phase(self):
        self.reject(lambda r:r['events'][1].update(phase=10),'unmarked phase')

    def test_live_capacity_cannot_be_relabelled_as_requested_size(self):
        def mutate(r):
            next(e for e in r['events'] if e['operation'] == 'direct_borrow')['bytes'] = 12288
        self.reject(mutate,'borrow domain')


if __name__ == '__main__':
    unittest.main()
