"""Replay lifetime calibration observations without executing retained code.

This is the semantic part of record validation. Source, runtime, command and
linker provenance must also be checked before accepting a complete record.
"""
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    loaded = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(loaded)
    return loaded


calibration = module('lifetime_existing_calibration', HERE.parent / 'lean_allocation_diagnostic/verify.py')
render = module('lifetime_probe_render', HERE / 'render.py')
require, same = calibration.require, calibration.same
METRICS = set(render.METRICS)
CURRENT = {'live_blocks', 'live_usable', 'interval_peak_usable'}
CAPACITY = 131072
OBSERVER_BYTES = CAPACITY * 32 + 14 * 8 + 1
NATIVE_PHASES = ('baseline', 'held', 'released', 'reallocation-alignment',
                 'cross-thread-free', 'heap-destroy', 'heap-delete', 'workers-ready',
                 'concurrent-churn', 'worker-exit', 'done')


def integer(value, label, minimum=0):
    require(type(value) is int and minimum <= value < 2**64, 'lifetime integer: ' + label)


def state(value, previous=None):
    require(type(value) is dict and set(value) == METRICS, 'lifetime metric fields')
    for key, number in value.items():
        integer(number, key)
    require(value['live_blocks'] == value['allocations'] - value['frees'], 'live block balance')
    require(value['live_usable'] == value['allocated_usable'] - value['freed_usable'], 'live byte balance')
    require(value['bulk_frees'] <= value['frees'], 'bulk frees exceed frees')
    require(value['allocated_requests'] <= value['allocated_usable'], 'requests exceed acquired blocks')
    require(value['peak_usable'] >= value['interval_peak_usable'] >= value['live_usable'], 'peak/live bounds')
    if previous is not None:
        require(all(value[k] >= previous[k] for k in METRICS - CURRENT), 'cumulative lifetime counter decreased')
        require(value['interval_peak_usable'] >= previous['live_usable'], 'interval omits its starting live bytes')
        require(value['peak_usable'] == max(previous['peak_usable'], value['interval_peak_usable']),
                'global and interval peaks disagree')
        require(value['interval_peak_usable'] <= previous['live_usable'] +
                value['allocated_usable'] - previous['allocated_usable'], 'peak exceeds actual acquisitions')


def difference(after, before, expected, label):
    for key, number in expected.items():
        require(after[key] - before[key] == number, label + ': ' + key)


def lean(rows):
    require(type(rows) is list and len(rows) == 38, 'Lean lifetime row count')
    require(all(type(row) is dict for row in rows), 'Lean lifetime row objects')
    kinds = ['configuration'] + [kind for _ in calibration.PHASES for kind in ('heap_lifetime', 'snapshot')]
    kinds += ['heap_lifetime_configuration']
    require([r.get('kind') for r in rows] == kinds, 'Lean lifetime row order')
    original = [rows[0]] + rows[2:-1:2]
    calibration.observation(original, 'diagnostic2')
    configuration = dict(kind='heap_lifetime_configuration', schema=1,
                         observer_static_bytes=OBSERVER_BYTES, capacity=CAPACITY)
    require(same(rows[-1], configuration), 'lifetime observer configuration')
    traces = rows[1:-1:2]
    previous = None
    states = []
    for row, snapshot, phase in zip(traces, original[1:], calibration.PHASES):
        require(set(row) == {'kind', 'workload', 'phase', 'before', 'after'}, 'Lean lifetime envelope')
        require((row['workload'], row['phase']) == phase, 'Lean lifetime phase mapping')
        require(same(row['before'], row['after']), 'observer changes lifetime counters')
        current = row['after']
        state(current, previous)
        require(current['live_blocks'] == snapshot['blocks'] and
                current['live_usable'] == snapshot['block_bytes'], 'independent heap visitor differs')
        if previous is not None:
            difference(current, previous, {k: 0 for k in
                ('bulk_frees', 'resizes', 'aligns', 'rehomes', 'resize_requests')}, 'unexpected Lean fixture path')
        states.append(current)
        previous = current
    # Empty observations and the explicitly separate collection do not create
    # tracked objects. Backing/RSS effects of collection are outside this channel.
    difference(states[1], states[0], {k: 0 for k in METRICS - CURRENT}, 'empty observation')
    difference(states[-1], states[-2], {k: 0 for k in METRICS - CURRENT}, 'collection')
    baseline = states[1]
    for index, case in enumerate(original[0]['workloads']):
        before, held, released, churn = states[1 + 3*index:5 + 3*index]
        count, usable, requested, repeats = (case[k] for k in ('held', 'usable_bytes', 'object_bytes', 'churn'))
        difference(held, before, dict(allocations=count, frees=0, allocated_usable=count*usable,
                   allocated_requests=count*requested, freed_usable=0), 'held ' + case['name'])
        require(held['live_blocks'] == baseline['live_blocks'] + count and
                held['interval_peak_usable'] == baseline['live_usable'] + count*usable, 'held live/peak')
        difference(released, held, dict(allocations=0, frees=count, allocated_usable=0,
                   allocated_requests=0, freed_usable=count*usable), 'release ' + case['name'])
        require(released['interval_peak_usable'] == held['live_usable'], 'release interval peak')
        difference(churn, released, dict(allocations=repeats, frees=repeats,
                   allocated_usable=repeats*usable, freed_usable=repeats*usable,
                   allocated_requests=repeats*requested), 'churn ' + case['name'])
        require(churn['interval_peak_usable'] == baseline['live_usable'] + usable, 'transient interval peak')
        for current in (released, churn):
            require(current['live_usable'] == baseline['live_usable'] and
                    current['live_blocks'] == baseline['live_blocks'], 'fixture did not release all objects')
    return dict(snapshots=len(traces), baseline_blocks=baseline['live_blocks'],
                baseline_usable=baseline['live_usable'], global_peak_usable=states[-1]['peak_usable'],
                startup_allocations=states[0]['allocations'], startup_acquired_requests=states[0]['allocated_requests'])


def native(rows):
    require(type(rows) is list and len(rows) == len(NATIVE_PHASES) + 1, 'native lifetime row count')
    require(all(type(row) is dict for row in rows), 'native lifetime row objects')
    config = rows[-1]
    fixed = dict(kind='native_heap_lifetime_configuration', schema=1, threads=8, iterations=10000,
                 allocations_per_iteration=2, capacity=CAPACITY, observer_static_bytes=OBSERVER_BYTES)
    require(set(config) == set(fixed) | {'held_usable', 'churn_usable', 'single_bound', 'combined_bound'},
            'native lifetime configuration fields')
    require(same({k: config[k] for k in fixed}, fixed), 'native lifetime fixed profile')
    require(type(config['held_usable']) is list and len(config['held_usable']) == 3, 'native held sizes')
    requests = (16, 4*1024*1024, 32*1024*1024)
    for actual, requested in zip(config['held_usable'], requests):
        integer(actual, 'held usable', requested)
    for key in ('churn_usable', 'single_bound', 'combined_bound'):
        integer(config[key], key, 1)
    require(config['single_bound'] <= config['combined_bound'] <= 8*config['single_bound'], 'worker maximum bounds')
    require(config['churn_usable'] <= 80000*config['single_bound'], 'worker acquired byte bound')
    states, previous = {}, None
    for row, phase in zip(rows[:-1], NATIVE_PHASES):
        require(type(row) is dict and set(row) == METRICS | {'kind', 'phase'}, 'native metric fields')
        require(row['kind'] == 'native_heap_lifetime' and row['phase'] == phase, 'native phase order')
        current = {k: row[k] for k in METRICS}
        state(current, previous)
        states[phase] = current
        previous = current
    baseline, held, released = (states[p] for p in NATIVE_PHASES[:3])
    usable = sum(config['held_usable'])
    difference(held, baseline, dict(allocations=3, frees=0, allocated_requests=sum(requests),
               allocated_usable=usable, freed_usable=0), 'native held')
    require(held['interval_peak_usable'] == baseline['live_usable'] + usable, 'native mixed-size peak')
    difference(released, held, dict(allocations=0, frees=3, allocated_requests=0,
               allocated_usable=0, freed_usable=usable), 'native release')
    require(released['live_usable'] == baseline['live_usable'] and
            released['interval_peak_usable'] == held['live_usable'], 'native release live/peak')
    resized = states['reallocation-alignment']
    difference(resized, released, dict(allocations=3, frees=3, resizes=2, aligns=1), 'native resize/alignment')
    require(resized['live_usable'] == baseline['live_usable'], 'native resize leaked')
    difference(states['cross-thread-free'], resized, dict(allocations=1, frees=1), 'cross-thread free')
    difference(states['heap-destroy'], states['cross-thread-free'], dict(bulk_frees=1), 'bulk destroy')
    difference(states['heap-delete'], states['heap-destroy'], dict(rehomes=1), 'heap delete rehome')
    before, after = states['workers-ready'], states['concurrent-churn']
    requested = 8*sum(17 + i%128 + 4097 + i%8 for i in range(10000))
    difference(after, before, dict(allocations=160000, frees=160000, allocated_requests=requested,
               allocated_usable=config['churn_usable'], freed_usable=config['churn_usable']), 'parked worker boundaries')
    require(after['live_blocks'] == before['live_blocks'] and after['live_usable'] == before['live_usable'],
            'workers did not restore their initial live set')
    require(before['live_usable'] + config['single_bound'] <= after['interval_peak_usable'] <=
            before['live_usable'] + config['combined_bound'], 'concurrent peak outside owned-pair bounds')
    difference(states['done'], states['worker-exit'], {k: 0 for k in METRICS - CURRENT}, 'native empty snapshot')
    return dict(snapshots=len(NATIVE_PHASES), workload_allocations=160000,
                mixed_peak_usable=held['interval_peak_usable'], concurrent_peak_usable=after['interval_peak_usable'],
                retained_blocks=states['done']['live_blocks'], retained_usable=states['done']['live_usable'])
