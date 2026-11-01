"""Mutation regressions over actual executable observations, never synthetic counters."""
import copy
import os
from pathlib import Path
import unittest
import zipfile

import observation


def load(name):
    path = os.environ.get(name)
    if path:
        return observation.calibration.base.stream(Path(path).read_text())
    retained = sorted((Path(__file__).resolve().parent / 'results').glob('*/evidence.zip'))
    record_path = os.environ.get('VASTITAS_HEAP_LIFETIME_RECORD') or (retained[0] if retained else None)
    if record_path:
        variant = 'lean' if name == 'VASTITAS_LIFETIME_LEAN_OBSERVATION' else 'native'
        path = Path(record_path)
        if path.is_dir():
            return observation.calibration.decode((path / f'runs/{variant}-1.json').read_bytes())
        with zipfile.ZipFile(path) as archive:
            return observation.calibration.decode(archive.read(f'runs/{variant}-1.json'))
    raise unittest.SkipTest('actual lifetime observation not supplied: ' + name)


class LeanLifetimeReplay(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = load('VASTITAS_LIFETIME_LEAN_OBSERVATION')
        cls.summary = observation.lean(cls.rows)

    def rejected(self, edit):
        rows = copy.deepcopy(self.rows)
        edit(rows)
        with self.assertRaises(ValueError):
            observation.lean(rows)

    def test_actual_public_api_fixture(self):
        self.assertEqual(self.summary['snapshots'], 18)
        self.assertGreater(self.summary['baseline_blocks'], 0)

    def test_balanced_extra_churn_is_not_explained_by_live_balance(self):
        def edit(rows):
            for row in rows[5:-1:2]:
                for side in ('before', 'after'):
                    for key, extra in dict(allocations=1, frees=1, allocated_requests=8,
                                          allocated_usable=8, freed_usable=8).items():
                        row[side][key] += extra
        self.rejected(edit)

    def test_transient_peak_cannot_be_replaced_by_end_live_bytes(self):
        def edit(rows):
            row = next(r for r in rows if r.get('kind') == 'heap_lifetime' and
                       r.get('workload') == 'array' and r.get('phase') == 'churn')
            for side in ('before', 'after'):
                row[side]['interval_peak_usable'] = row[side]['live_usable']
        self.rejected(edit)

    def test_startup_cannot_be_subtracted_from_all_counter_channels(self):
        def edit(rows):
            baseline = dict(rows[1]['after'])
            for row in rows[1:-1:2]:
                for side in ('before', 'after'):
                    for key in observation.METRICS:
                        subtraction = (baseline['live_usable'] if key in
                            ('peak_usable', 'interval_peak_usable') else baseline[key])
                        row[side][key] -= subtraction
        self.rejected(edit)

    def test_observer_allocation_is_visible_even_when_later_released(self):
        def edit(rows):
            after = rows[1]['after']
            after['allocations'] += 1
            after['frees'] += 1
            after['allocated_usable'] += 16
            after['freed_usable'] += 16
        self.rejected(edit)

    def test_before_and_after_cannot_hide_boolean_counts(self):
        def edit(rows):
            for side in ('before', 'after'):
                rows[1][side]['resizes'] = False
        self.rejected(edit)

    def test_reordered_or_missing_pair_is_rejected(self):
        self.rejected(lambda rows: rows.__setitem__(slice(1, 3), rows[1:3][::-1]))
        self.rejected(lambda rows: rows.pop(2))


class NativeLifetimeReplay(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = load('VASTITAS_LIFETIME_NATIVE_OBSERVATION')
        cls.summary = observation.native(cls.rows)

    def rejected(self, edit):
        rows = copy.deepcopy(self.rows)
        edit(rows)
        with self.assertRaises(ValueError):
            observation.native(rows)

    def test_actual_concurrent_and_heap_fixture(self):
        self.assertEqual(self.summary['workload_allocations'], 160000)
        self.assertEqual(self.summary['snapshots'], 11)

    def test_balanced_worker_under_count_is_rejected(self):
        def edit(rows):
            first = observation.NATIVE_PHASES.index('concurrent-churn')
            for row in rows[first:-1]:
                row['allocations'] -= 1
                row['frees'] -= 1
        self.rejected(edit)

    def test_dropping_bulk_destruction_or_rehoming_is_rejected(self):
        for field, phase in (('bulk_frees', 'heap-destroy'), ('rehomes', 'heap-delete')):
            def edit(rows, field=field, phase=phase):
                first = observation.NATIVE_PHASES.index(phase)
                for row in rows[first:-1]:
                    row[field] -= 1
            self.rejected(edit)

    def test_concurrent_peak_above_all_owned_pairs_is_rejected(self):
        def edit(rows):
            index = observation.NATIVE_PHASES.index('concurrent-churn')
            before = rows[index - 1]['live_usable']
            rows[index]['interval_peak_usable'] = before + rows[-1]['combined_bound'] + 1
        self.rejected(edit)

    def test_actual_usable_sizes_cannot_be_replaced_by_request_totals(self):
        self.rejected(lambda rows: rows[-1].__setitem__('churn_usable', 334472832))

    def test_unknown_cost_claim_or_smaller_workload_is_rejected(self):
        self.rejected(lambda rows: rows[-1].__setitem__('whole_process_peak', True))
        self.rejected(lambda rows: rows[-1].__setitem__('iterations', 9999))


if __name__ == '__main__':
    unittest.main()
