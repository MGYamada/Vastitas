import copy
import hashlib
import json
import os
from pathlib import Path
import unittest

from allocator import PHASES, replay
from verify import backend, verify_reader
from test_source_workspace import Overlay


def fixture():
    reader = backend.Reader(Path(__file__).resolve().parent/'results/2026-11-01-macos/evidence.zip')
    selected = next(r['allocation'] for r in reader.json('observations.json')['rows']
                    if r['implementation']=='generated' and r['scope']==0 and r['repetitions']==1)
    zero = dict(total=0,current=0,peak=0)
    current = dict(boundary=0,repeat=0,normal_count=0,huge_count=0,
                   normal=dict(zero),huge=dict(zero),requested=dict(zero))
    rows = [copy.deepcopy(current),dict(copy.deepcopy(current),repeat=1)]
    for i,phase in enumerate(PHASES,1):
        kinds = selected['phases'][phase]['kinds'].values()
        current['boundary'] = i
        current['normal_count'] += sum(k['allocations'] for k in kinds)
        size = sum(k['bytes'] for k in kinds)
        current['normal']['total'] += size
        current['normal']['current'] += size-sum(k['released_bytes'] for k in kinds)
        current['normal']['peak'] = max(current['normal']['peak'],current['normal']['current'])
        current['requested']['total'] += size
        current['requested']['current'] += size  # Deliberately cumulative, not live.
        current['requested']['peak'] += size
        rows.extend([copy.deepcopy(current),dict(copy.deepcopy(current),repeat=1)])
    return dict(kind='source_lean_allocator',schema=1,mimalloc_version=30405,stats_version=5,
                observer_static_bytes=43732,snapshots=rows,error_objects=[]),selected


class AllocatorPhaseReplay(unittest.TestCase):
    def test_cumulative_requested_is_not_treated_as_live(self):
        trace,selected=fixture()
        result=replay(trace,selected,'diagnostic2')['phases']['run']
        self.assertEqual(result['normal_count'],6)
        self.assertEqual(result['normal_binned_bytes'],120)
        self.assertEqual(result['normal_live_delta'],0)
        self.assertEqual(result['requested_counter_delta'],120)

    def test_unsupported_stock_counter_is_not_reported_as_zero(self):
        trace,selected=fixture()
        for s in trace['snapshots']:
            s['normal_count']=0
            s['normal']={k:0 for k in s['normal']}
        result=replay(trace,selected,'stock')
        self.assertEqual(result['phases'],dict.fromkeys(PHASES))

    def test_missing_boundary_fails(self):
        trace,selected=fixture();trace['snapshots'].pop()
        with self.assertRaisesRegex(ValueError,'boundary coverage'): replay(trace,selected,'diagnostic2')

    def test_empty_observation_cannot_allocate(self):
        trace,selected=fixture();trace['snapshots'][1]['normal_count']+=1
        with self.assertRaisesRegex(ValueError,'empty observer'): replay(trace,selected,'diagnostic2')

    def test_count_cannot_omit_selected_source_allocations(self):
        trace,selected=fixture()
        for s in trace['snapshots'][6:]:s['normal_count']-=1
        with self.assertRaisesRegex(ValueError,'misses selected'): replay(trace,selected,'diagnostic2')

    def test_boolean_is_not_a_count(self):
        trace,selected=fixture();trace['snapshots'][0]['normal_count']=False
        with self.assertRaisesRegex(ValueError,'count domain'): replay(trace,selected,'diagnostic2')

    def test_unattributed_churn_remains_visible(self):
        trace,selected=fixture()
        for s in trace['snapshots'][6:]:
            s['normal_count']+=1;s['normal']['total']+=64
        result=replay(trace,selected,'diagnostic2')['phases']['run']
        self.assertEqual(result['unattributed_normal_count'],1)
        self.assertEqual(result['unattributed_normal_binned_bytes'],64)

    def test_error_payload_cannot_be_invented_for_success(self):
        trace,selected=fixture();trace['error_objects']=[{}]
        with self.assertRaisesRegex(ValueError,'actual error objects'): replay(trace,selected,'diagnostic2')

    def test_observer_bytes_cannot_omit_static_buffers(self):
        trace,selected=fixture();trace['observer_static_bytes']=8
        with self.assertRaisesRegex(ValueError,'observer storage'): replay(trace,selected,'diagnostic2')


class SourceAllocatorRecord(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path=os.environ.get('VASTITAS_SOURCE_ALLOCATOR_RECORD')
        if not path:
            candidate=Path(__file__).resolve().parent/'results/2026-11-01-macos-allocator/evidence.zip'
            if candidate.exists():path=candidate
        if not path: raise unittest.SkipTest('source allocator record is supplied after measurement')
        cls.reader=backend.Reader(path)

    def check(self,reader):
        return verify_reader(reader,allow_build_tree=reader.reader.zip is None if isinstance(reader,Overlay) else reader.zip is None)

    def test_full_raw_receipt_replay(self):
        summary=self.check(self.reader)
        backends=8 if self.reader.json('record.json')['schema']==4 else 6
        per_case=backends*(8 if summary['selection'] in ('streaming','debug-streaming-one') else 12)
        self.assertEqual(summary['records'],per_case*summary['cases'])
        self.assertEqual(summary['failure_cleanups'],backends*summary['cases'])
        self.assertEqual(summary['lean_allocator']['snapshots'],10*(per_case+backends)*summary['cases'])

    def test_configuration_cannot_omit_zero_stat_control(self):
        reader=Overlay(self.reader);record=reader.json('record.json')
        record['configurations'].pop('stock-rebuilt0');reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'configuration coverage'):self.check(reader)

    def test_foreign_runtime_fails_calibration_binding(self):
        reader=Overlay(self.reader);record=reader.json('record.json')
        record['lean_allocator']['archives']['diagnostic2']='0'*64;reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'uncalibrated source runtime'):self.check(reader)

    def test_startup_or_stock_count_claim_cannot_be_added(self):
        for claim in ('startup_accounted','diagnostic_counts_are_stock_counts','general_peak'):
            with self.subTest(claim=claim):
                reader=Overlay(self.reader);record=reader.json('record.json')
                record['lean_allocator']['claims'][claim]=True;reader.replace('record.json',record)
                with self.assertRaisesRegex(ValueError,'unsupported allocator claim'):self.check(reader)

    def test_changed_calibrated_toolchain_fails(self):
        reader=Overlay(self.reader);record=reader.json('record.json')
        path=next(p for p in record['external_inputs'] if p.endswith('/libInit.a'))
        record['external_inputs'][path]='0'*64;reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'toolchain differs'):self.check(reader)

    def test_entry_thread_override_is_required(self):
        reader=Overlay(self.reader);commands=reader.json('commands.json')
        next(c for c in commands if c['phase']=='source_workspace')['compiler_environment']['LEAN_MAIN_USE_THREAD']='0'
        reader.replace('commands.json',commands)
        with self.assertRaisesRegex(ValueError,'entry thread profile'):self.check(reader)

    def test_actual_error_string_usable_size_is_required(self):
        row=next(r for r in self.reader.json('observations.json')['failures']
                 if r['backend']=='stock-diagnostic2')
        row['lean_allocator']['error_objects'][0]['string_usable']=76
        with self.assertRaisesRegex(ValueError,'actual error objects'):
            replay(row['lean_allocator'],row['allocation'],'diagnostic2')

    def test_foreign_link_map_cannot_use_a_valid_calibration(self):
        reader=Overlay(self.reader);record=reader.json('record.json')
        name=next(n for n in reader.names if '/stock-diagnostic2/link.map' in n)
        data=reader.read(name).replace(record['lean_allocator']['prefixes']['diagnostic2'].encode(),b'/foreign/runtime')
        reader.changed[name]=data
        record['files'][name]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'link map selects'):self.check(reader)

    def test_reporting_cannot_precede_the_final_allocator_snapshot(self):
        reader=Overlay(self.reader);record=reader.json('record.json')
        name=next(n for n in reader.names if '/stock-diagnostic2/native/ffi.c' in n)
        data=reader.read(name).replace(b'source_allocator_finish(); bench_report();',
                                     b'bench_report(); source_allocator_finish();')
        reader.changed[name]=data
        record['files'][name]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'helper/report connection|reporting is inside'):self.check(reader)

    def test_fingerprinted_support_archive_must_be_the_linked_one(self):
        reader=Overlay(self.reader);record=reader.json('record.json')
        name=next(n for n in reader.names if '/stock-diagnostic2/link.map' in n)
        installed=reader.json('lean-calibration/record.json')['toolchain']['inputs']['lib/lean/libInit.a']['path']
        data=reader.read(name).replace(installed.encode(),b'/foreign/toolchain/libInit.a')
        reader.changed[name]=data
        record['files'][name]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
        reader.replace('record.json',record)
        with self.assertRaisesRegex(ValueError,'uncalibrated support archive'):self.check(reader)


class RetainedAllocatorExports(unittest.TestCase):
    def test_both_full_exports_match_their_manifests_and_source_inputs(self):
        root=Path(__file__).resolve().parent/'results'
        inputs=[]
        for platform in ('macos','linux'):
            with self.subTest(platform=platform):
                directory=root/('2026-11-01-'+platform+'-allocator')
                manifest=json.loads((directory/'artifact-manifest.json').read_text())
                archive=directory/'evidence.zip'
                with archive.open('rb') as stream:
                    self.assertEqual(hashlib.file_digest(stream,'sha256').hexdigest(),manifest['sha256'])
                self.assertEqual(archive.stat().st_size,manifest['bytes'])
                reader=backend.Reader(archive)
                self.assertEqual(len(reader.names),manifest['members'])
                summary=verify_reader(reader)
                self.assertEqual(summary,manifest['summary'])
                self.assertEqual((summary['cases'],summary['records'],summary['failure_cleanups']), (12,864,72))
                self.assertEqual(summary['canonical_executions'],72)
                self.assertEqual(summary['lean_allocator']['snapshots'],9360)
                record=reader.json('record.json')
                self.assertEqual(record['head'],manifest['measured_head'])
                self.assertEqual(record['status'],manifest['measured_status'])
                self.assertEqual(record['status'],'')
                inputs.append(record['inputs'])
        self.assertEqual(len(inputs),2)
        self.assertEqual(inputs[0],inputs[1])


if __name__=='__main__':unittest.main()
