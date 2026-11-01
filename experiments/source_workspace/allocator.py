"""Bind the source observer to calibrated archives; replay phase deltas only."""
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('source_allocator_calibration',
    HERE.parent / 'lean_allocation_diagnostic/verify.py')
calibration = importlib.util.module_from_spec(spec)
spec.loader.exec_module(calibration)
require, same = calibration.require, calibration.same
VARIANTS = calibration.VARIANTS
PHASES = ('cold', 'setup', 'run', 'cleanup')
CLAIMS = dict(calling_thread_phase_deltas=True, startup_accounted=False,
              whole_process_accounting=False, general_peak=False,
              diagnostic_counts_are_stock_counts=False, timings=False)


def configurations(enabled):
    return ({f'{b}-{v}': dict(backend=b, runtime=v)
             for b in ('stock', 'diagnostic') for v in VARIANTS} if enabled else
            {b: dict(backend=b, runtime=None) for b in ('stock', 'diagnostic')})


def replay(trace, selected, variant):
    require(set(trace) == {'kind', 'schema', 'mimalloc_version', 'stats_version',
                          'observer_static_bytes', 'snapshots', 'error_objects'}, 'allocator envelope')
    require(trace['kind'] == 'source_lean_allocator' and type(trace['schema']) is int and
            trace['schema'] == 1 and trace['mimalloc_version'] == 30405 and
            trace['stats_version'] == 5, 'allocator ABI/schema')
    require(type(trace['observer_static_bytes']) is int and trace['observer_static_bytes'] == 43732,
            'allocator observer storage')
    error_count = selected['phases']['run']['kinds']['ffi_error']['allocations']
    require(error_count in (0,1) and same(trace['error_objects'],
            [dict(phase=3,object_requested=16,object_usable=16,string_requested=76,string_usable=80,string_bytes=44)]*error_count),
            'missing or changed actual error objects')
    rows = trace['snapshots']
    require([(s['boundary'], s['repeat']) for s in rows] ==
            [(i, j) for i in range(5) for j in range(2)], 'allocator boundary coverage')
    for s in rows:
        require(set(s) == {'boundary', 'repeat', 'normal_count', 'huge_count',
                           'normal', 'huge', 'requested'}, 'allocator snapshot fields')
        require(all(type(s[k]) is int and s[k] >= 0 for k in
                    ('boundary', 'repeat', 'normal_count', 'huge_count')), 'allocator count domain')
        for name in ('normal', 'huge', 'requested'):
            value = s[name]
            require(set(value) == {'total', 'current', 'peak'} and
                    all(type(x) is int for x in value.values()) and value['total'] >= 0 and
                    value['peak'] >= 0 and value['current'] <= value['peak'], 'allocator byte domain')
    for i in range(5):
        require(same({k: v for k, v in rows[2*i].items() if k != 'repeat'},
                     {k: v for k, v in rows[2*i+1].items() if k != 'repeat'}),
                'empty observer changed allocator counters')
    phases = {}
    for index, phase in enumerate(PHASES):
        before, after = rows[2*index], rows[2*index+2]
        counts = {name: after[name] - before[name] for name in ('normal_count', 'huge_count')}
        changes = {name: {key: after[name][key] - before[name][key] for key in ('total', 'current')}
                   for name in ('normal', 'huge', 'requested')}
        require(all(v >= 0 for v in counts.values()) and all(v['total'] >= 0 for v in changes.values()),
                'allocator cumulative counter decreased')
        kinds = selected['phases'][phase]['kinds']
        known_count = sum(x['allocations'] for x in kinds.values())
        known_bytes = sum(x['bytes'] for x in kinds.values())
        # These selected objects have exact 8-byte-aligned 16/24/32-byte sizes.
        # The total observer is a superset, not an additional allocation cost.
        if variant == 'diagnostic2':
            require(counts['normal_count'] >= known_count and changes['normal']['total'] >= known_bytes,
                    'allocator misses selected source allocations')
            require(all(changes[n]['total'] >= changes[n]['current'] for n in ('normal', 'huge')),
                    'allocator live growth exceeds allocation')
            phases[phase] = dict(normal_count=counts['normal_count'], huge_count=counts['huge_count'],
                normal_binned_bytes=changes['normal']['total'], huge_binned_bytes=changes['huge']['total'],
                normal_live_delta=changes['normal']['current'], huge_live_delta=changes['huge']['current'],
                requested_counter_delta=changes['requested']['total'],
                selected_count=known_count, selected_bytes=known_bytes,
                additional_normal_count=counts['normal_count']-known_count,
                additional_normal_binned_bytes=changes['normal']['total']-known_bytes,
                error_payload_count=2*error_count if phase=='run' else 0,
                error_payload_binned_bytes=96*error_count if phase=='run' else 0,
                error_payload_requested_bytes=92*error_count if phase=='run' else 0)
            p = phases[phase]
            p['unattributed_normal_count'] = p['additional_normal_count']-p['error_payload_count']
            p['unattributed_normal_binned_bytes'] = p['additional_normal_binned_bytes']-p['error_payload_binned_bytes']
            require(p['unattributed_normal_count'] >= 0 and p['unattributed_normal_binned_bytes'] >= 0,
                    'allocator misses actual error objects')
        else:
            phases[phase] = None  # Unsupported stock channel is not zero allocation.
    return dict(capability='calibrated_phase_deltas' if variant == 'diagnostic2' else 'unsupported_normal_counts',
                phases=phases)


def check_calibration(reader, record, prefixed):
    binding = record['lean_allocator']
    require(set(binding) == {'record', 'prefixes', 'archives', 'claims'}, 'allocator binding fields')
    require(same(binding['claims'], CLAIMS), 'unsupported allocator claim')
    require(binding['record'] == 'lean-calibration', 'allocator calibration location')
    nested = prefixed(reader, binding['record'])
    calibration.verify_files(nested.read, nested.names)
    calibrated = nested.json('record.json')
    required = {'experiments/source_workspace/'+name for name in
                ('allocator.c','allocator.h','allocator.py','run.py','verify.py')}
    require(required <= set(record['inputs']), 'missing source allocator inputs')
    require(set(binding['prefixes']) == set(binding['archives']) == set(VARIANTS), 'allocator variant coverage')
    for variant in VARIANTS:
        digest = calibration.digest(nested.read(calibrated['archives'][variant]['path']))
        require(binding['archives'][variant] == digest ==
                record['external_inputs'][binding['prefixes'][variant] + '/libleanrt.a'],
                'uncalibrated source runtime archive')
    for item in calibrated['toolchain']['inputs'].values():
        require(record['external_inputs'].get(item['path']) == item['sha256'],
                'source toolchain differs from calibrated toolchain')
    relative = 'experiments/stock_allocation_capabilities/vendor/mimalloc-stats.h'
    require(record['inputs'][relative] == calibrated['repository']['inputs'][relative]['sha256'],
            'allocator ABI header differs from calibration')
    for name in ('lean.h', 'config.h'):
        require(reader.read('pinned-' + name) == nested.read('inputs/toolchain/include/lean/' + name),
                'source headers differ from calibrated toolchain')


def check_program(reader, record, prefix, config):
    binding = record['lean_allocator']
    directory = binding['prefixes'][config['runtime']]
    mapping = reader.read(prefix + 'link.map').decode()
    paths = set(re.findall(r'(/[^\s()]+/libleanrt\.a)\(', mapping))
    require(paths == {directory + '/libleanrt.a'} and 'mimalloc.cpp.o' in mapping and
            'lean_alloc_small_object_core' in mapping and 'mi_stats_get' in mapping and
            'source_allocator_mark' in mapping and 'allocator.o' in mapping,
            'source link map selects an uncalibrated runtime')
    root = reader.read(prefix + 'lakefile.lean').decode()
    require(root.count(json.dumps('-L' + directory)) == 1 and root.count('link.map') == 1,
            'missing source runtime link arguments')
    for name in ('allocator.c', 'allocator.h'):
        require(reader.read(prefix + 'native/' + name) ==
                reader.read('source/experiments/source_workspace/' + name), 'allocator observer source differs')
    require(reader.read(prefix + 'native/mimalloc-stats.h') == reader.read(
        'source/experiments/stock_allocation_capabilities/vendor/mimalloc-stats.h'), 'source statistics header differs')
    require(reader.read(prefix + 'native/mimalloc.h') == reader.read(
        'lean-calibration/inputs/toolchain/include/lean/mimalloc.h'), 'source allocator API differs')
    ffi = reader.read(prefix + 'native/ffi.c')
    require(ffi.count(b'source_allocator_finish(); bench_report();') == 1 and
            ffi.count(b'source_workspace_report(); source_allocator_report();') == 1,
            'allocator reporting is inside the measured phases')
    audit = reader.read(prefix + 'native/audit.c')
    require(audit.count(b'source_allocator_mark(next); source_workspace_mark(next);') == 1,
            'allocator phase hook differs')
    require(audit.count(b'source_allocator_error(value); return record(lean_io_result_mk_error(value), IO_ERROR);') == 1,
            'actual error payload hook differs')
    lake = reader.read(prefix + 'native/lakefile.lean')
    require('← allocatorObject.fetch'.encode() in lake and b'allocator.c' in lake and
            b'mimalloc-stats.h' in lake, 'allocator observer is not built')
