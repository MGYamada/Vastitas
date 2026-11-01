"""Reject omissions and unjustified coverage claims in allocation observations."""
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


def sample():
    """Small independent fixture with explicit known retention/release counts."""
    config = dict(kind='configuration', mimalloc_header_version=30405, stats_header_version=5,
                  small_held_count=1024, large_held_count=8, small_transient_count=10000,
                  large_transient_count=128, small_scalar_bytes=32, small_object_bytes=40,
                  large_payload_bytes=2097152, large_object_bytes=2097176,
                  small_held_usable_bytes=40960, large_held_usable_bytes=18874368,
                  observer_snapshot_bytes=1220328, known_object_table_bytes=16512, checksum=78664)
    rows = [config]
    for index, phase in enumerate(('baseline', 'small_held', 'small_released', 'large_held',
                                   'large_released', 'small_transient', 'large_transient', 'forced_collection')):
        count = (20,1044,20,28,20,20,20,20)[index]
        size = (800,41760,800,18875168,800,800,800,800)[index]
        stats = {name: dict(current=0, peak=0, total=0) for name in
                 ('pages','reserved','committed','malloc_normal','malloc_huge','malloc_requested')}
        huge = (0,0,0,18874368,18874368,18874368,320864256,320864256)[index]
        stats.update(stat_version=5, mimalloc_version=30405, malloc_normal_count=0,
                     chunk_bins=[dict(bin=label,current=0,peak=0,total=0) for label in 'SXMLH '],
                     malloc_huge_count=(0,0,0,8,8,8,136,136)[index],
                     malloc_huge=dict(current=huge, peak=huge, total=huge))
        rows.append(dict(kind='snapshot', phase=phase, visit_ok=True, stats_ok=True, json_ok=True,
                         areas=4, area_used=count, area_live_bin_bytes=size,
                         area_reserved_bytes=40000000, area_committed_bytes=20000000,
                         blocks=count, block_bytes=size, known_small=1024 if index==1 else 0,
                         known_large=8 if index==3 else 0,
                         process=dict(rss=50000000,peak_rss=50000000,commit=50000000,peak_commit=50000000,faults=10),
                         stats=stats))
    return rows


class ObservationTests(unittest.TestCase):
    def test_disabled_churn_is_not_zero_allocation(self):
        result = verify.observations(sample())
        self.assertEqual(result['small_churn'], 'unsupported_no_signal')
        self.assertEqual(result['large_churn'], 'calibrated_tested_count')
        self.assertEqual(result['huge_current'], 'not_live_bytes')

    def test_other_counter_capabilities_are_reported_honestly(self):
        for normal, huge, expected_normal, expected_huge in (
            (10000,0,'calibrated_tested_count','unsupported_no_signal'),
            (17,3,'unsupported_inconsistent_signal','unsupported_inconsistent_signal')):
            rows=sample()
            rows[6]['stats']['malloc_normal_count']=normal
            rows[7]['stats']['malloc_huge_count']=8+huge
            result=verify.observations(rows)
            self.assertEqual(result['small_churn'],expected_normal)
            self.assertEqual(result['large_churn'],expected_huge)

    def test_huge_release_has_only_tested_scope(self):
        rows=sample()
        rows[5]['stats']['malloc_huge']['current']=0
        self.assertEqual(verify.observations(rows)['huge_current'],'matches_tested_release_only')
        rows[5]['stats']['malloc_huge']['current']=1
        self.assertEqual(verify.observations(rows)['huge_current'],'unsupported_inconsistent_signal')

    def test_missing_duplicate_reordered_and_extra_phases(self):
        for change in (lambda r:r.pop(2), lambda r:r.append(r[-1]),
                       lambda r:r.__setitem__(2,copy.deepcopy(r[1])),
                       lambda r:r.reverse()):
            with self.subTest(change=change):
                rows=sample(); change(rows)
                with self.assertRaises((ValueError,KeyError)): verify.observations(rows)

    def test_pointer_and_release_coverage(self):
        for row,key in ((2,'known_small'),(4,'known_large'),(3,'blocks'),(5,'block_bytes'),
                        (6,'area_used'),(7,'area_live_bin_bytes'),(8,'block_bytes')):
            with self.subTest(row=row,key=key):
                rows=sample(); rows[row][key]+=1
                with self.assertRaises(ValueError): verify.observations(rows)

    def test_integer_domains_and_failed_observer(self):
        for value in (True,0.0,-1):
            for location,key in ((0,'checksum'),(1,'blocks'),(1,'stats')):
                rows=sample()
                if key=='stats': rows[location][key]['malloc_normal_count']=value
                else: rows[location][key]=value
                with self.subTest(value=value,location=location,key=key):
                    with self.assertRaises(ValueError): verify.observations(rows)
        for value in (False,1,'true'):
            rows=sample(); rows[1]['visit_ok']=value
            with self.assertRaises(ValueError): verify.observations(rows)

    def test_checksum_header_and_observer_costs(self):
        for key in ('mimalloc_header_version','stats_header_version','checksum',
                    'small_object_bytes','large_payload_bytes','known_object_table_bytes'):
            rows=sample(); rows[0][key]+=1
            with self.subTest(key=key):
                with self.assertRaises(ValueError): verify.observations(rows)
        rows=sample(); rows[0]['observer_snapshot_bytes']=1
        with self.assertRaises(ValueError): verify.observations(rows)

    def test_allocator_label_domains(self):
        rows=sample(); rows[1]['stats']['chunk_bins'][0]['bin']='unknown'
        with self.assertRaises(ValueError): verify.observations(rows)
        rows=sample(); rows[1]['stats']['malloc_normal_count']='0'
        with self.assertRaises(ValueError): verify.observations(rows)

    def test_duplicate_nonfinite_or_trailing_json(self):
        for raw in ('{"x":0,"x":1}', '{"x":NaN}', '{"x":Infinity}', '{}garbage'):
            with self.assertRaises(ValueError): verify.stream(raw)
        self.assertFalse(verify.same_json({'x':True},{'x':1}))

    def test_runner_never_reuses_existing_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            sentinel=Path(directory)/'sentinel'; sentinel.write_text('preserve')
            result=subprocess.run([sys.executable,str(HERE/'run.py'),'--out',directory],capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('FileExistsError',result.stderr)
            self.assertEqual(sentinel.read_text(),'preserve')


class RetainedRecordTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        records=sorted((HERE/'results').glob('*/evidence.zip'))
        supplied=os.environ.get('VASTITAS_CAPABILITY_TEST_RECORD')
        if supplied:
            records.append(Path(supplied))
        if not records:
            raise unittest.SkipTest('retained capability record not yet published')
        cls.records=[]
        for path in records:
            if path.is_dir():
                cls.records.append({p.relative_to(path).as_posix():p.read_bytes()
                                    for p in path.rglob('*') if p.is_file()})
                continue
            with zipfile.ZipFile(path) as archive:
                cls.records.append({name:archive.read(name) for name in archive.namelist()})

    def fixture(self):
        files=dict(self.records[0])
        return files,verify.decode(files['record.json'])

    def check(self,files,record):
        files['record.json']=json.dumps(record).encode()
        return verify.verify_files(files.__getitem__,list(files))

    def rehash(self,files,record,name,data):
        files[name]=data
        record['files'][name]=dict(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))

    def test_all_retained_records(self):
        for files in self.records:
            result=verify.verify_files(files.__getitem__,list(files))
            self.assertEqual(result['runs'],3)
            self.assertEqual(result['snapshots'],24)
            self.assertFalse(result['whole_process_accounting'])

    def test_unsupported_claims(self):
        for claim in ('whole_process_accounting','between_snapshot_peak','timing','backend_hooks','production_rebuild'):
            files,record=self.fixture(); record['claims'][claim]=True
            with self.subTest(claim=claim):
                with self.assertRaises(ValueError): self.check(files,record)
        files,record=self.fixture(); record['claims']['timing']=0
        with self.assertRaises(ValueError): self.check(files,record)

    def test_run_omission_or_repetition(self):
        for mutate in (lambda r:r['runs'].pop(),lambda r:r['runs'][1].update(index=1),
                       lambda r:r['runs'][0].update(index=True)):
            files,record=self.fixture(); mutate(record)
            with self.assertRaises(ValueError): self.check(files,record)

    def test_rehashed_false_classification_and_observation(self):
        files,record=self.fixture()
        record['runs'][0]['classification']['small_churn']='calibrated_tested_count'
        with self.assertRaises(ValueError): self.check(files,record)
        # Rehash both duplicated observation forms so this reaches arithmetic,
        # not merely the transport hash/raw-vs-parsed comparison.
        files,record=self.fixture(); run=record['runs'][0]
        rows=verify.decode(files[run['parsed']]); rows[3]['block_bytes']+=8
        self.rehash(files,record,run['parsed'],json.dumps(rows).encode())
        self.rehash(files,record,run['stdout'],'\n'.join(json.dumps(r) for r in rows).encode())
        with self.assertRaisesRegex(ValueError,'live block bytes'): self.check(files,record)

    def test_raw_parsed_mismatch(self):
        files,record=self.fixture(); name=record['runs'][0]['parsed']
        rows=verify.decode(files[name]); rows[1]['process']['rss']+=1
        self.rehash(files,record,name,json.dumps(rows).encode())
        with self.assertRaisesRegex(ValueError,'raw/parsed'): self.check(files,record)

    def test_input_omission_or_changed_fingerprint(self):
        files,record=self.fixture(); record['repository']['inputs'].pop('lean-toolchain')
        with self.assertRaises(ValueError): self.check(files,record)
        files,record=self.fixture(); record['toolchain']['inputs']['bin/lean']['sha256_after']='0'*64
        with self.assertRaises(ValueError): self.check(files,record)

    def test_hash_omission_and_duplicate_archive(self):
        files,record=self.fixture(); files['unexpected']=b'x'
        with self.assertRaises(ValueError): self.check(files,record)
        files,record=self.fixture(); files['build/Main.c']+=b' changed'
        with self.assertRaises(ValueError): self.check(files,record)
        files,record=self.fixture()
        with self.assertRaises(ValueError): verify.verify_files(files.__getitem__,list(files)+['record.json'])
        with self.assertRaises(ValueError): verify.verify_files(files.__getitem__,list(files)+['../foreign'])

    def test_rehashed_command_failure(self):
        files,record=self.fixture(); commands=verify.decode(files['commands.json'])
        commands[-1]['returncode']=1
        self.rehash(files,record,'commands.json',json.dumps(commands).encode())
        with self.assertRaisesRegex(ValueError,'command failed'): self.check(files,record)


if __name__=='__main__':
    unittest.main()
