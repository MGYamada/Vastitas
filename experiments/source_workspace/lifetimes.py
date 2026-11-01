"""Bind actual source phases to the calibrated private block-lifetime runtime."""
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    loaded = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(loaded)
    return loaded


calibration = module('source_heap_calibration', HERE.parent / 'lean_allocation_lifetimes/verify.py')
allocator = module('source_heap_thread_counters', HERE / 'allocator.py')
observation = calibration.observation
require, same, digest = calibration.require, calibration.same, calibration.digest
CLAIMS = dict(pre_cold_mimalloc_traffic=True, phase_usable_peaks=True,
              whole_process_accounting=False, full_process_exit=False,
              physical_backing_peak=False, stock_counts=False, timings=False)


def replay(trace, selected, counters):
    fixed = dict(kind='source_lean_heap_lifetimes', schema=1, mimalloc_version=30405,
                 capacity=observation.CAPACITY, observer_static_bytes=observation.OBSERVER_BYTES,
                 phase_storage_bytes=1208)
    require(type(trace) is dict and set(trace) == set(fixed) | {'snapshots'}, 'heap lifetime envelope')
    require(same({k: trace[k] for k in fixed}, fixed), 'heap lifetime profile/storage')
    rows = trace['snapshots']
    require(type(rows) is list and len(rows) == 5, 'heap boundary coverage')
    states, previous = [], None
    for index, row in enumerate(rows):
        require(type(row) is dict and set(row) ==
                {'boundary', 'visited_blocks', 'visited_usable', 'before', 'after'}, 'heap boundary fields')
        require(type(row['boundary']) is int and row['boundary'] == index, 'heap boundary order')
        require(same(row['before'], row['after']), 'source observer changes heap lifetimes')
        current = row['after']
        observation.state(current, previous)
        for key in ('visited_blocks', 'visited_usable'):
            observation.integer(row[key], key)
        require(row['visited_blocks'] == current['live_blocks'] and
                row['visited_usable'] == current['live_usable'], 'independent source heap visitor differs')
        if previous is not None:
            observation.difference(current, previous, {k: 0 for k in
                ('bulk_frees', 'resizes', 'aligns', 'rehomes', 'resize_requests')}, 'unsupported source heap operation')
        states.append(current)
        previous = current
    require(states[0]['live_blocks'] > 0 and states[0]['peak_usable'] == states[0]['interval_peak_usable'],
            'pre-cold live set or lifetime peak was reset')
    thread = allocator.replay(counters, selected, 'lifetimes')['phases']
    phases = {}
    for index, name in enumerate(allocator.PHASES):
        before, after = states[index:index+2]
        delta = {key: after[key] - before[key] for key in
                 ('allocations', 'frees', 'allocated_requests', 'allocated_usable', 'freed_usable')}
        mi = thread[name]
        require(delta['allocations'] == mi['normal_count'] + mi['huge_count'] and
                delta['allocated_usable'] == mi['normal_binned_bytes'] + mi['huge_binned_bytes'] and
                after['live_usable'] - before['live_usable'] == mi['normal_live_delta'] + mi['huge_live_delta'],
                'global source lifetime traffic differs from independent calling-thread counters')
        require(delta['allocated_requests'] >= mi['requested_counter_delta'] and
                (mi['huge_count'] != 0 or delta['allocated_requests'] == mi['requested_counter_delta']),
                'source allocation requests disagree with the calibrated normal request channel')
        kinds = selected['phases'][name]['kinds'].values()
        known = {key: sum(kind[key] for kind in kinds) for key in
                 ('allocations', 'bytes', 'final_releases', 'released_bytes')}
        errors = mi['error_payload_count']
        error_bytes, error_requests = mi['error_payload_binned_bytes'], mi['error_payload_requested_bytes']
        other = dict(allocations=delta['allocations']-known['allocations']-errors,
                     allocation_requests=delta['allocated_requests']-known['bytes']-error_requests,
                     acquired_usable=delta['allocated_usable']-known['bytes']-error_bytes,
                     frees=delta['frees']-known['final_releases']-errors,
                     released_usable=delta['freed_usable']-known['released_bytes']-error_bytes)
        require(all(value >= 0 for value in other.values()), 'heap lifetimes omit selected objects or actual error payloads')
        phases[name] = dict(**delta, live_blocks_before=before['live_blocks'], live_blocks_after=after['live_blocks'],
            live_usable_before=before['live_usable'], live_usable_after=after['live_usable'],
            peak_usable=after['interval_peak_usable'], peak_above_entry=after['interval_peak_usable']-before['live_usable'],
            selected=known, error_objects=errors, other=other)
    return dict(pre_cold=states[0], end=states[-1], phases=phases)


def check_calibration(reader, record, prefixed):
    binding = record['lean_lifetimes']
    require(set(binding) == {'record', 'runtime_dir', 'archive_sha256', 'observer_object', 'observer_sha256', 'claims'},
            'source heap binding fields')
    require(binding['record'] == 'heap-calibration' and same(binding['claims'], CLAIMS), 'unsupported source heap claim')
    nested = prefixed(reader, binding['record'])
    calibration.verify_files(nested.read, list(nested.names))
    calibrated = nested.json('record.json')
    require(digest(nested.read(calibrated['runtime']['path'])) == binding['archive_sha256'] ==
            record['external_inputs'][binding['runtime_dir'] + '/libleanrt.a'], 'uncalibrated source heap runtime')
    require(digest(nested.read('build/lifetime.o')) == binding['observer_sha256'] ==
            record['external_inputs'][binding['observer_object']], 'uncalibrated source heap observer object')
    for item in calibrated['toolchain']['inputs'].values():
        require(record['external_inputs'].get(item['path']) == item['sha256'], 'source heap toolchain differs')
    for name in ('lean.h', 'config.h'):
        require(reader.read('pinned-' + name) == nested.read('inputs/toolchain/include/lean/' + name),
                'source heap headers differ')
    required = {'experiments/source_workspace/' + name for name in
                ('heap.c', 'heap.h', 'lifetimes.py', 'allocator.c', 'allocator.h', 'run.py', 'verify.py')}
    required.add('experiments/lean_allocation_lifetimes/lifetime.h')
    require(required <= set(record['inputs']), 'missing source heap inputs')
    header = 'experiments/lean_allocation_lifetimes/lifetime.h'
    require(record['inputs'][header] == calibrated['repository']['inputs'][header]['sha256'], 'source heap ABI differs')
    # Source observations are audited against the reviewed finite observer, not
    # an arbitrary C program that happens to print the same JSON envelope.
    for name in ('heap.c', 'heap.h'):
        require(reader.read('source/experiments/source_workspace/' + name) == (HERE / name).read_bytes(),
                'unreviewed source heap observer')


def phase_signature(summary):
    """Compare traffic/relative peaks without identifying fresh startup states."""
    result = {}
    for name, values in summary['phases'].items():
        result[name] = {key: value for key, value in values.items() if key not in
            ('live_blocks_before', 'live_blocks_after', 'live_usable_before', 'live_usable_after', 'peak_usable')}
        result[name]['live_blocks_delta'] = values['live_blocks_after']-values['live_blocks_before']
        result[name]['live_usable_delta'] = values['live_usable_after']-values['live_usable_before']
    return result


def check_program(reader, record, prefix, config):
    binding = record['lean_lifetimes']
    allocator.check_program(reader, record, prefix, config, lifetime_binding=binding)
    mapping = reader.read(prefix + 'link.map').decode()
    objects = set(re.findall(r'(/[^\s()]+/lifetime\.o)', mapping))
    require(objects == {binding['observer_object']} and all(name in mapping for name in
            ('vastitas_heap_snapshot', 'vastitas_heap_checkpoint', 'source_heap_before', 'source_heap_after', 'heap.o')),
            'source heap link map lacks the calibrated observer')
    root = reader.read(prefix + 'lakefile.lean').decode()
    require(root.count(json.dumps(binding['observer_object'])) == 1, 'source heap observer link argument')
    for name in ('heap.c', 'heap.h'):
        require(reader.read(prefix + 'native/' + name) == reader.read('source/experiments/source_workspace/' + name),
                'source heap observer changed')
    require(reader.read(prefix + 'native/lifetime.h') == reader.read(
            'heap-calibration/inputs/repository/experiments/lean_allocation_lifetimes/lifetime.h'), 'source heap ABI header')
    native = reader.read(prefix + 'native/allocator.c')
    require(native.count(b'source_heap_before(index);') == 1 and native.count(b'source_heap_after(index);') == 1 and
            native.count(b'source_heap_report();') == 1, 'source heap phase hook coverage')
    before, get, after = (native.index(token) for token in
                         (b'source_heap_before(index);', b'assert(mi_stats_get(s));', b'source_heap_after(index);'))
    require(before < get < after, 'source heap hooks do not bracket the existing observer')
    lake = reader.read(prefix + 'native/lakefile.lean')
    require(lake.count(b'-DSOURCE_HEAP_LIFETIMES=1') == 1 and '← heapObject.fetch'.encode() in lake and
            b'heap.c' in lake and b'lifetime.h' in lake, 'source heap observer is not built')
