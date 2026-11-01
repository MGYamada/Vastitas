"""Mutate actual source receipts; rehash edits to reach semantic audits."""
import copy
import hashlib
import json
import os
from pathlib import Path
import unittest

import lifetimes
from test_source_workspace import Overlay
from verify import backend, Prefixed, verify_reader


def record_reader():
    path = os.environ.get('VASTITAS_SOURCE_HEAP_RECORD')
    if not path:
        candidate = Path(__file__).resolve().parent / 'results/2026-11-02-macos-lifetimes/evidence.zip'
        if candidate.exists():
            path = candidate
    if not path:
        raise unittest.SkipTest('actual source heap record not supplied')
    return backend.Reader(path)


class SourceHeapPhases(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reader = record_reader()
        cls.rows = cls.reader.json('observations.json')

    def row(self, *, failure=False):
        return copy.deepcopy(next(row for row in self.rows['failures' if failure else 'rows']
            if row['backend']=='stock-lifetimes' and row['scope']==0 and row['repetitions']==1
            and row['implementation']==('failure' if failure else 'generated')))

    def replay(self, row):
        return lifetimes.replay(row['heap_lifetimes'], row['allocation'], row['lean_allocator'])

    def test_all_actual_phases_reconcile_independent_channels(self):
        for row in self.rows['rows'] + self.rows['failures']:
            if row['heap_lifetimes'] is None:
                continue
            with self.subTest(key=(row['case'],row['backend'],row['implementation'],row['scope'],row['repetitions'])):
                summary = self.replay(row)
                self.assertGreater(summary['pre_cold']['allocations'], 0)
                self.assertGreater(summary['pre_cold']['live_usable'], 0)
                self.assertEqual(set(summary['phases']), {'cold','setup','run','cleanup'})

    def test_transient_peak_is_not_only_the_end_live_set(self):
        summary = self.replay(self.row())
        run = summary['phases']['run']
        self.assertEqual(run['live_usable_before'], run['live_usable_after'])
        self.assertGreater(run['peak_usable'], run['live_usable_after'])
        self.assertGreater(run['allocated_usable'], 0)
        self.assertEqual(run['allocated_usable'], run['freed_usable'])

    def test_release_of_preexisting_arguments_is_not_negative_allocation(self):
        summary = self.replay(self.row())
        setup = summary['phases']['setup']
        self.assertLess(setup['live_usable_after'], setup['live_usable_before'])
        self.assertGreater(setup['other']['released_usable'], 0)
        self.assertGreater(setup['allocated_usable'], 0)

    def test_missing_or_reordered_boundary_is_rejected(self):
        for mutate in (lambda rows:rows.pop(), lambda rows:rows.reverse()):
            row = self.row()
            mutate(row['heap_lifetimes']['snapshots'])
            with self.assertRaisesRegex(ValueError, 'boundary coverage|boundary order'):
                self.replay(row)

    def test_observation_itself_cannot_hide_heap_traffic(self):
        row = self.row()
        row['heap_lifetimes']['snapshots'][2]['after']['allocations'] += 1
        with self.assertRaisesRegex(ValueError, 'observer changes heap'):
            self.replay(row)

    def test_independent_heap_visitor_cannot_be_replaced_by_counter(self):
        row = self.row()
        row['heap_lifetimes']['snapshots'][2]['visited_usable'] -= 16
        with self.assertRaisesRegex(ValueError, 'independent source heap visitor'):
            self.replay(row)

    def test_phase_counters_cannot_disagree_with_global_traffic(self):
        row = self.row()
        for snapshot in row['lean_allocator']['snapshots'][6:]:
            snapshot['normal_count'] += 1
            snapshot['normal']['total'] += 16
        with self.assertRaisesRegex(ValueError, 'independent calling-thread counters'):
            self.replay(row)

    def test_additional_churn_remains_explicitly_unattributed(self):
        row = self.row()
        for snapshot in row['heap_lifetimes']['snapshots'][3:]:
            for side in ('before','after'):
                for key, delta in dict(allocations=1,frees=1,allocated_requests=16,
                                       allocated_usable=16,freed_usable=16).items():
                    snapshot[side][key] += delta
        for snapshot in row['lean_allocator']['snapshots'][6:]:
            snapshot['normal_count'] += 1
            snapshot['normal']['total'] += 16
            snapshot['requested']['total'] += 16
        other = self.replay(row)['phases']['run']['other']
        self.assertEqual(other, dict(allocations=1,allocation_requests=16,acquired_usable=16,
                                    frees=1,released_usable=16))

    def test_actual_failure_payload_must_be_allocated_and_released(self):
        row = self.row(failure=True)
        phase = self.replay(row)['phases']['run']
        self.assertEqual(phase['error_objects'], 2)
        self.assertEqual(phase['other']['frees'], 0)
        self.assertEqual(phase['other']['released_usable'], 0)
        # Removing a payload release must still balance the live counters and
        # visitor; even then the independent MI_STAT channel rejects the edit.
        for snapshot in row['heap_lifetimes']['snapshots'][3:]:
            snapshot['visited_blocks'] += 1
            snapshot['visited_usable'] += 16
            for side in ('before','after'):
                snapshot[side]['frees'] -= 1
                snapshot[side]['freed_usable'] -= 16
                snapshot[side]['live_blocks'] += 1
                snapshot[side]['live_usable'] += 16
                snapshot[side]['interval_peak_usable'] = max(snapshot[side]['interval_peak_usable'],
                                                           snapshot[side]['live_usable'])
        with self.assertRaisesRegex(ValueError, 'independent calling-thread counters'):
            self.replay(row)

    def test_boolean_or_hidden_observer_storage_is_rejected(self):
        for key, value in (('capacity', True),('observer_static_bytes', 112),('phase_storage_bytes', 1200)):
            row = self.row()
            row['heap_lifetimes'][key] = value
            with self.assertRaisesRegex(ValueError, 'profile/storage'):
                self.replay(row)


class SourceHeapProvenance(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reader = record_reader()
        cls.prefix = min(name.removesuffix('link.map') for name in cls.reader.names
                         if '/stock-lifetimes/link.map' in name)

    def check(self, reader):
        return verify_reader(reader, allow_build_tree=self.reader.zip is None)

    def calibration(self, reader):
        return lifetimes.check_calibration(reader, reader.json('record.json'), Prefixed)

    def program(self, reader):
        lifetimes.check_program(reader, reader.json('record.json'), self.prefix,
                                dict(backend='stock',runtime='lifetimes'))

    def replace_bytes(self, reader, name, data):
        reader.changed[name] = data
        record = reader.json('record.json')
        record['files'][name] = dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
        reader.replace('record.json',record)

    def test_complete_source_receipt_has_all_eight_configurations(self):
        summary = self.check(self.reader)
        per_case = 8 if 'streaming' in summary['selection'] else 12
        self.assertEqual(summary['records'], summary['cases']*8*per_case)
        self.assertEqual(summary['canonical_executions'], summary['cases']*8)
        self.assertEqual(summary['failure_cleanups'], summary['cases']*8)
        self.assertEqual(summary['heap_lifetimes']['boundary_pairs'], summary['cases']*2*(per_case+1)*5)
        self.assertEqual(summary['heap_lifetimes']['claims'],lifetimes.CLAIMS)
        self.assertFalse(summary['claims']['total_heap'])

    def test_foreign_runtime_or_observer_object_is_not_calibrated(self):
        for key, pattern in (('archive_sha256','uncalibrated source heap runtime'),
                             ('observer_sha256','uncalibrated source heap observer')):
            reader = Overlay(self.reader)
            record = reader.json('record.json')
            record['lean_lifetimes'][key] = '0'*64
            reader.replace('record.json',record)
            with self.assertRaisesRegex(ValueError,pattern):
                self.calibration(reader)

    def test_schema3_cannot_silently_ignore_lifetimes(self):
        reader = Overlay(self.reader)
        record = reader.json('record.json')
        record['schema'] = 3
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'heap lifetimes need schema 4'):
            self.check(reader)

    def test_control_runtime_cannot_claim_lifetime_observation(self):
        reader = Overlay(self.reader)
        rows = reader.json('observations.json')
        source = next(row for row in rows['rows'] if row['heap_lifetimes'] is not None)
        next(row for row in rows['rows'] if row['heap_lifetimes'] is None)['heap_lifetimes'] = source['heap_lifetimes']
        reader.replace('observations.json',rows)
        with self.assertRaisesRegex(ValueError,'unsupported runtime has no lifetime authority'):
            self.check(reader)

    def test_peak_cannot_be_relabelled_as_final_live_bytes(self):
        reader = Overlay(self.reader)
        rows = reader.json('observations.json')
        row = next(row for row in rows['rows'] if row['backend']=='stock-lifetimes'
                   and row['implementation']=='generated' and row['scope']==0 and row['repetitions']==1)
        for side in ('before','after'):
            state = row['heap_lifetimes']['snapshots'][3][side]
            state['interval_peak_usable'] = state['live_usable']
        reader.replace('observations.json',rows)
        with self.assertRaisesRegex(ValueError,'transient peak'):
            self.check(reader)

    def test_foreign_observer_cannot_use_valid_runtime_receipts(self):
        reader = Overlay(self.reader)
        name = self.prefix+'link.map'
        observer = reader.json('record.json')['lean_lifetimes']['observer_object'].encode()
        self.replace_bytes(reader,name,reader.read(name).replace(observer,b'/foreign/lifetime.o'))
        with self.assertRaisesRegex(ValueError,'calibrated observer'):
            self.program(reader)

    def test_phase_hooks_must_bracket_the_existing_observer(self):
        reader = Overlay(self.reader)
        name = self.prefix+'native/allocator.c'
        data = reader.read(name).replace(b'source_heap_before(index);',b'source_heap_after(index);',1)
        self.assertNotEqual(data, reader.read(name))
        self.replace_bytes(reader,name,data)
        with self.assertRaisesRegex(ValueError,'allocator observer source|hook coverage'):
            self.program(reader)

    def test_rehashed_heap_source_cannot_replace_reviewed_observer(self):
        reader = Overlay(self.reader)
        relative = 'experiments/source_workspace/heap.c'
        name = 'source/'+relative
        data = reader.read(name).replace(b'vastitas_heap_checkpoint()',b'vastitas_heap_snapshot()')
        self.replace_bytes(reader,name,data)
        record = reader.json('record.json')
        record['inputs'][relative] = hashlib.sha256(data).hexdigest()
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'unreviewed source heap observer'):
            self.calibration(reader)

    def test_scoped_observation_does_not_authorize_whole_process_claim(self):
        reader = Overlay(self.reader)
        record = reader.json('record.json')
        record['lean_lifetimes']['claims']['whole_process_accounting'] = True
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'unsupported source heap claim'):
            self.calibration(reader)


class RetainedSourceHeapExports(unittest.TestCase):
    def test_complete_exports_match_manifests_and_measured_inputs(self):
        root = Path(__file__).resolve().parent / 'results'
        inputs = []
        for suffix, expected in (
                ('macos-lifetimes', (12,1152,96,1560)),
                ('linux-lifetimes', (12,1152,96,1560)),
                ('macos-lifetimes-streaming', (4,256,32,360))):
            with self.subTest(record=suffix):
                directory = root / ('2026-11-02-'+suffix)
                manifest = json.loads((directory/'artifact-manifest.json').read_text())
                archive = directory/'evidence.zip'
                with archive.open('rb') as stream:
                    self.assertEqual(hashlib.file_digest(stream,'sha256').hexdigest(),manifest['sha256'])
                self.assertEqual(archive.stat().st_size,manifest['bytes'])
                reader = backend.Reader(archive)
                self.assertEqual(len(reader.names),manifest['members'])
                summary = verify_reader(reader)
                self.assertEqual(summary,manifest['summary'])
                self.assertEqual((summary['cases'],summary['records'],summary['failure_cleanups'],
                                  summary['heap_lifetimes']['boundary_pairs']),expected)
                record = reader.json('record.json')
                self.assertEqual(record['head'],manifest['measured_head'])
                self.assertEqual(record['head'],'8212d7d0a6720e37913b6d44d5932e8ff263ead8')
                self.assertEqual(record['status'],manifest['measured_status'])
                self.assertEqual(record['status'],'')
                self.assertEqual(len(record['inputs']),86)
                inputs.append(record['inputs'])
        self.assertTrue(all(value==inputs[0] for value in inputs[1:]))


if __name__ == '__main__':
    unittest.main()
