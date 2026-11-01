"""Offline provenance mutations over an actual retained calibration record."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

import verify

HERE = Path(__file__).resolve().parent


class RunnerBoundary(unittest.TestCase):
    def test_existing_output_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            sentinel = Path(directory) / 'sentinel'
            sentinel.write_text('keep')
            result = subprocess.run([sys.executable, HERE / 'run.py', '--out', directory], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'FileExistsError', result.stderr)
            self.assertEqual(sentinel.read_text(), 'keep')


class LifetimeRecord(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = os.environ.get('VASTITAS_HEAP_LIFETIME_RECORD')
        if not path:
            raise unittest.SkipTest('actual retained lifetime record not supplied')
        path = Path(path)
        if path.is_dir():
            cls.files = {p.relative_to(path).as_posix(): p.read_bytes() for p in path.rglob('*') if p.is_file()}
        else:
            with zipfile.ZipFile(path) as archive:
                cls.files = {name: archive.read(name) for name in archive.namelist()}
        cls.summary = verify.verify_files(cls.files.__getitem__, list(cls.files))

    def fixture(self):
        return dict(self.files), verify.decode(self.files['record.json'])

    def check(self, files, record):
        files['record.json'] = json.dumps(record).encode()
        return verify.verify_files(files.__getitem__, list(files))

    def rehash(self, files, record, name, data):
        files[name] = data
        record['files'][name] = dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))

    def test_complete_record_replays_without_executing_retained_code(self):
        with patch('subprocess.run', side_effect=AssertionError('replay must not execute programs')):
            summary = verify.verify_files(self.files.__getitem__, list(self.files))
        self.assertEqual(summary['runs'], 7)
        self.assertEqual(summary['lean_snapshots'], 54)
        self.assertEqual(summary['native_snapshots'], 44)
        self.assertGreater(summary['unchanged_runtime_objects'], 0)

    def test_rehashed_incomplete_hook_is_rejected(self):
        files, record = self.fixture()
        name = 'build/mimalloc-3.4.5/src/heap.c'
        data = files[name].replace(b'vastitas_heap_destroy(heap);', b'(void)heap;')
        self.assertNotEqual(data, files[name])
        self.rehash(files, record, name, data)
        receipts = verify.decode(files['patches.json'])
        receipts['src/heap.c']['after_sha256'] = hashlib.sha256(data).hexdigest()
        self.rehash(files, record, 'patches.json', json.dumps(receipts).encode())
        with self.assertRaises(ValueError): self.check(files, record)

    def test_rehashed_unrelated_allocator_change_is_rejected(self):
        files, record = self.fixture()
        name = 'build/mimalloc-3.4.5/src/free.c'
        self.rehash(files, record, name, files[name] + b'\n/* changed */\n')
        with self.assertRaises(ValueError): self.check(files, record)

    def test_rehashed_observer_source_is_not_trusted(self):
        files, record = self.fixture()
        relative = 'experiments/lean_allocation_lifetimes/lifetime.cpp'
        name = 'inputs/repository/' + relative
        data = files[name].replace(b'state.allocations, 1', b'state.allocations, 0')
        self.assertNotEqual(data, files[name])
        self.rehash(files, record, name, data)
        item = record['repository']['inputs'][relative]
        item['sha256'] = item['sha256_after'] = hashlib.sha256(data).hexdigest()
        with self.assertRaises(ValueError): self.check(files, record)

    def test_rendered_probe_cannot_drop_before_after_audit(self):
        files, record = self.fixture()
        name = 'build/probe.c'
        data = files[name].replace(b's->lifetime_before, &s->lifetime_after', b's->lifetime_before, &s->lifetime_before')
        self.assertNotEqual(data, files[name])
        self.rehash(files, record, name, data)
        with self.assertRaises(ValueError): self.check(files, record)

    def test_foreign_runtime_or_observer_linkage_is_rejected(self):
        for old, new in ((b'/runtime/libleanrt.a', b'/foreign/libleanrt.a'),
                         (b'/build/lifetime.o', b'/build/foreign.o')):
            files, record = self.fixture()
            name = 'build/lean-link.map'
            data = files[name].replace(old, new)
            self.assertNotEqual(data, files[name])
            self.rehash(files, record, name, data)
            with self.assertRaises(ValueError): self.check(files, record)

    def test_missing_retained_executable_is_rejected_even_after_inventory_edit(self):
        files, record = self.fixture()
        name = 'build/sanitized-probe'
        del files[name], record['files'][name]
        with self.assertRaises(ValueError): self.check(files, record)

    def test_changed_flags_environment_or_capacity_status_is_rejected(self):
        for mode in ('flag', 'environment', 'capacity'):
            files, record = self.fixture()
            commands = verify.decode(files['commands.json'])
            if mode == 'flag':
                command = next(c for c in commands if c['label'] == 'runtime-compile')
                command['argv'].append('-DMI_PADDING=1')
            elif mode == 'environment':
                command = next(c for c in commands if c['label'] == 'native-run-1')
                command['environment']['LD_PRELOAD'] = '/tmp/interposer.so'
            else:
                next(c for c in commands if c['label'] == 'native-capacity')['returncode'] = 0
            self.rehash(files, record, 'commands.json', json.dumps(commands).encode())
            with self.assertRaises(ValueError): self.check(files, record)

    def test_capacity_failure_requires_its_exact_diagnostic(self):
        files, record = self.fixture()
        command = next(c for c in verify.decode(files['commands.json']) if c['label'] == 'native-capacity')
        self.rehash(files, record, command['stderr'], b'unrelated failure\n')
        with self.assertRaises(ValueError): self.check(files, record)

    def test_missing_fresh_process_is_rejected(self):
        files, record = self.fixture()
        record['runs'].pop(0)
        with self.assertRaises(ValueError): self.check(files, record)

    def test_parsed_observations_cannot_disagree_with_raw_output(self):
        files, record = self.fixture()
        run = record['runs'][0]
        rows = verify.decode(files[run['parsed']])
        rows[1]['before']['allocations'] += 1
        self.rehash(files, record, run['parsed'], json.dumps(rows).encode())
        with self.assertRaises(ValueError): self.check(files, record)

    def test_complete_or_stock_performance_claims_are_rejected(self):
        for key in ('whole_process_accounting', 'stock_runtime_equivalence', 'timing', 'physical_backing_peak'):
            files, record = self.fixture()
            record['claims'][key] = True
            with self.assertRaises(ValueError): self.check(files, record)


if __name__ == '__main__':
    unittest.main()
