"""Negative checks for archive isolation and calibrated cost claims."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import zipfile

import verify

HERE = Path(__file__).resolve().parent


def ar(entries):
    result = bytearray(b'!<arch>\n')
    for name, payload in entries:
        header = f'{name + "/":<16}{0:<12}{0:<6}{0:<6}{100644:<8}{len(payload):<10}`\n'.encode()
        assert len(header) == 60
        result += header + payload + (b'\n' if len(payload) % 2 else b'')
    return bytes(result)


class ArchiveTests(unittest.TestCase):
    def test_one_object_only(self):
        stock = ar([('object.cpp.o', b'keep'), ('mimalloc.cpp.o', b'old')])
        changed = ar([('object.cpp.o', b'keep'), ('mimalloc.cpp.o', b'new')])
        self.assertEqual(len(verify.audit_replacement(stock, changed, b'new')), 2)
        for entries, obj in (([('object.cpp.o', b'changed'), ('mimalloc.cpp.o', b'new')], b'new'),
                             ([('object.cpp.o', b'keep'), ('mimalloc.cpp.o', b'old')], b'old'),
                             ([('object.cpp.o', b'keep'), ('mimalloc.cpp.o', b'new')], b'foreign'),
                             ([('mimalloc.cpp.o', b'new'), ('object.cpp.o', b'keep')], b'new'),
                             ([('object.cpp.o', b'keep'), ('mimalloc.cpp.o', b'new'), ('extra.o', b'x')], b'new')):
            with self.assertRaises(ValueError): verify.audit_replacement(stock, ar(entries), obj)

    def test_duplicate_truncated_and_nonobject_archives(self):
        good = ar([('mimalloc.cpp.o', b'abc')])
        for data in (good[:-1], good + b'x', b'!<thin>\n',
                     ar([('x.o', b'a'), ('x.o', b'b')]), ar([('unknown', b'a')])):
            with self.assertRaises(ValueError): verify.ar_objects(data)

    def test_bsd_and_gnu_long_names(self):
        name = b'a-long-object-name.cpp.o'
        payload = name + b'\0' + b'object'
        header = f'{"#1/" + str(len(name) + 1):<16}{0:<12}{0:<6}{0:<6}{100644:<8}{len(payload):<10}`\n'.encode()
        bsd = b'!<arch>\n' + header + payload + (b'\n' if len(payload) % 2 else b'')
        self.assertEqual(verify.ar_objects(bsd), {name.decode(): b'object'})
        table = name + b'/\n'
        def entry(label, value):
            h = f'{label:<16}{0:<12}{0:<6}{0:<6}{100644:<8}{len(value):<10}`\n'.encode()
            return h + value + (b'\n' if len(value) % 2 else b'')
        self.assertEqual(verify.ar_objects(b'!<arch>\n' + entry('//', table) + entry('/0', b'object')),
                         {name.decode(): b'object'})

    def test_runner_preserves_existing_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            sentinel = Path(directory) / 'sentinel'; sentinel.write_text('keep')
            result = subprocess.run([sys.executable, HERE / 'run.py', '--out', directory], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('FileExistsError', result.stderr)
            self.assertEqual(sentinel.read_text(), 'keep')


class RecordTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        paths = sorted((HERE / 'results').glob('*/evidence.zip'))
        if os.environ.get('VASTITAS_LEAN_DIAGNOSTIC_RECORD'):
            paths.append(Path(os.environ['VASTITAS_LEAN_DIAGNOSTIC_RECORD']))
        if not paths:
            raise unittest.SkipTest('no retained or explicitly supplied record yet')
        cls.records = []
        for path in paths:
            if path.is_dir():
                files = {p.relative_to(path).as_posix(): p.read_bytes() for p in path.rglob('*') if p.is_file()}
            else:
                with zipfile.ZipFile(path) as archive:
                    files = {n: archive.read(n) for n in archive.namelist()}
            cls.records.append(files)

    def test_all_records(self):
        for files in self.records:
            with self.subTest(record=verify.decode(files['record.json'])['repository']['head']):
                self.assertEqual(verify.verify_files(files.__getitem__, list(files))['snapshots'], 162)

    def fixture(self):
        files = dict(self.records[0])
        return files, verify.decode(files['record.json'])

    def check(self, files, record):
        files['record.json'] = json.dumps(record).encode()
        return verify.verify_files(files.__getitem__, list(files))

    def rehash(self, files, record, name, data):
        files[name] = data
        record['files'][name] = dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))

    def rows(self):
        files, record = self.fixture()
        run = next(r for r in record['runs'] if r['variant'] == 'diagnostic2')
        return verify.decode(files[run['parsed']])

    def test_counts_and_live_bytes_cannot_be_silently_omitted(self):
        for key, nested in (('malloc_normal_count', None), ('malloc_huge_count', None),
                            ('malloc_normal', 'current'), ('malloc_huge', 'total'),
                            ('malloc_requested', 'current')):
            rows = self.rows()
            index = 9 if 'huge' in key else 3
            if nested: rows[index]['stats'][key][nested] += 1
            else: rows[index]['stats'][key] += 1
            with self.subTest(key=key):
                with self.assertRaises(ValueError): verify.observation(rows, 'diagnostic2')

    def test_requested_bytes_are_not_live_and_exclude_huge(self):
        rows = self.rows()
        rows[4]['stats']['malloc_requested']['current'] = rows[2]['stats']['malloc_requested']['current']
        with self.assertRaises(ValueError): verify.observation(rows, 'diagnostic2')
        rows = self.rows()
        rows[9]['stats']['malloc_requested']['total'] += 8 * 2097176
        with self.assertRaises(ValueError): verify.observation(rows, 'diagnostic2')

    def test_visitor_release_and_repeated_observation(self):
        for index, key in ((4, 'known'), (7, 'blocks'), (12, 'block_bytes'), (15, 'area_bytes')):
            rows = self.rows(); rows[index][key] += 1
            with self.assertRaises(ValueError): verify.observation(rows, 'diagnostic2')
        rows = self.rows(); rows[2]['stats']['malloc_normal_count'] += 1
        with self.assertRaises(ValueError): verify.observation(rows, 'diagnostic2')

    def test_phase_order_coverage_domains_and_checksum(self):
        for mutate in (lambda r: r.pop(), lambda r: r.append(r[-1]), lambda r: r.reverse(),
                       lambda r: r[3].__setitem__('phase', 'released'),
                       lambda r: r[0].__setitem__('checksum', 1),
                       lambda r: r[3].__setitem__('known', True)):
            rows = self.rows(); mutate(rows)
            with self.assertRaises((ValueError, KeyError)): verify.observation(rows, 'diagnostic2')

    def test_unsupported_claims(self):
        for key in verify.CLAIMS:
            files, record = self.fixture(); record['claims'][key] = True
            with self.subTest(key=key):
                with self.assertRaises(ValueError): self.check(files, record)

    def test_missing_variant_or_run(self):
        files, record = self.fixture(); record['runs'].pop()
        with self.assertRaises(ValueError): self.check(files, record)

    def test_foreign_runtime_link_map(self):
        files, record = self.fixture(); name = 'build/diagnostic2/link.map'
        data = files[name].replace(b'/diagnostic2/libleanrt.a', b'/foreign/libleanrt.a')
        self.rehash(files, record, name, data)
        with self.assertRaises(ValueError): self.check(files, record)

    def test_extra_member_even_with_rehashed_archive(self):
        files, record = self.fixture(); name = 'build/diagnostic2/libleanrt.a'
        data = files[name] + ar([('unexpected.o', b'bad')])[8:]
        self.rehash(files, record, name, data)
        with self.assertRaises(ValueError): self.check(files, record)

    def test_changed_raw_or_parsed_observations(self):
        files, record = self.fixture(); run = record['runs'][-1]
        data = verify.decode(files[run['parsed']]); data[0]['checksum'] += 1
        self.rehash(files, record, run['parsed'], json.dumps(data).encode())
        with self.assertRaises(ValueError): self.check(files, record)

    def test_rebuild_flags_and_runtime_environment(self):
        for mode in ('flag', 'environment'):
            files, record = self.fixture(); commands = verify.decode(files['commands.json'])
            if mode == 'flag':
                next(c for c in commands if c['label'] == 'diagnostic2-compile')['argv'].append('-DMI_DEBUG=3')
            else:
                next(c for c in commands if c['label'] == 'diagnostic2-run-1')['environment']['LEAN_NUM_THREADS'] = '4'
            self.rehash(files, record, 'commands.json', json.dumps(commands).encode())
            with self.assertRaises(ValueError): self.check(files, record)


if __name__ == '__main__':
    unittest.main()
