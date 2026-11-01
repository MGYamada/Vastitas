#!/usr/bin/env python3
"""Independently audit stock-allocator observations, never infer total coverage."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import zipfile

PIN = 'leanprover/lean4:v4.35.0'
HEADER_BLOB = 'b4e19c09aaa2b18bae1b1d5f0e4591967a99452f'
PHASES = ('baseline', 'small_held', 'small_released', 'large_held',
          'large_released', 'small_transient', 'large_transient', 'forced_collection')
EXPERIMENT = 'experiments/stock_allocation_capabilities/'
REQUIRED_INPUTS = {EXPERIMENT + name for name in (
    'Main.lean', 'probe.c', 'run.py', 'verify.py', 'test_capabilities.py',
    'README.md', 'upstream-sources.json', 'vendor/mimalloc-stats.h',
    'vendor/LICENSE.mimalloc')} | {'lean-toolchain', 'lean-kernel/lean-toolchain'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, name, minimum=0):
    require(type(value) is int and value >= minimum, f'invalid integer: {name}')
    return value


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'duplicate JSON key: {key}')
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError(f'non-finite JSON number: {value}')


DECODER = json.JSONDecoder(object_pairs_hook=unique_object, parse_constant=reject_constant)


def decode(data):
    return DECODER.decode(data.decode() if isinstance(data, bytes) else data)


def stream(data):
    text = data.decode() if isinstance(data, bytes) else data
    rows = []
    while text.strip():
        value, end = DECODER.raw_decode(text.lstrip())
        rows.append(value)
        text = text.lstrip()[end:]
    return rows


def same_json(left, right):
    # Python equality otherwise equates True, 1 and 1.0, including nested fields.
    return json.dumps(left, sort_keys=True) == json.dumps(right, sort_keys=True)


def number_tree(value, name):
    if isinstance(value, dict):
        for key, item in value.items():
            number_tree(item, f'{name}.{key}')
    elif isinstance(value, list):
        for index, item in enumerate(value):
            number_tree(item, f'{name}[{index}]')
    else:
        integer(value, name)


def observations(rows):
    require(type(rows) is list and len(rows) == 9, 'configuration plus eight snapshots required')
    config = rows[0]
    fixed = dict(kind='configuration', mimalloc_header_version=30405,
                 stats_header_version=5, small_held_count=1024, large_held_count=8,
                 small_transient_count=10000, large_transient_count=128,
                 small_scalar_bytes=32, small_object_bytes=40,
                 large_payload_bytes=2097152, large_object_bytes=2097176,
                 known_object_table_bytes=16512, checksum=(1024+10000)*7+(8+128)*11)
    measured = {'small_held_usable_bytes', 'large_held_usable_bytes', 'observer_snapshot_bytes'}
    require(set(config) == set(fixed) | measured, 'configuration fields differ')
    for key, expected in fixed.items():
        require(same_json(config[key], expected), f'configuration differs: {key}')
    for key in measured:
        integer(config[key], key, 1)
    require(config['small_held_usable_bytes'] >= 1024*40, 'small block bytes below objects')
    require(config['large_held_usable_bytes'] >= 8*2097176, 'large block bytes below objects')
    require(config['small_held_usable_bytes'] % 1024 == 0, 'small usable bytes not uniform')
    require(config['large_held_usable_bytes'] % 8 == 0, 'large usable bytes not uniform')
    require(config['observer_snapshot_bytes'] >= 9*128*1024, 'observer bytes omit static buffers')
    counters = {'areas', 'area_used', 'area_live_bin_bytes', 'area_reserved_bytes',
                'area_committed_bytes', 'blocks', 'block_bytes', 'known_small', 'known_large'}
    snapshot_keys = counters | {'kind', 'phase', 'visit_ok', 'stats_ok', 'json_ok', 'process', 'stats'}
    baseline = rows[1]
    for phase, row in zip(PHASES, rows[1:]):
        require(set(row) == snapshot_keys and row['kind'] == 'snapshot' and row['phase'] == phase,
                'missing, repeated, reordered or unsupported snapshot')
        require(all(row[key] is True for key in ('visit_ok', 'stats_ok', 'json_ok')), 'observer failed')
        for key in counters:
            integer(row[key], key)
        require(set(row['process']) == {'rss', 'peak_rss', 'commit', 'peak_commit', 'faults'},
                'missing process diagnostics')
        number_tree(row['process'], 'process')
        stats = row['stats']
        require(type(stats) is dict, 'statistics object required')
        # This pinned JSON ABI uses six literal chunk-bin labels, unlike its
        # numerical size-bin tables. Do not accept arbitrary string counters.
        bins = stats['chunk_bins']
        require(type(bins) is list and [b.get('bin') for b in bins] == list('SXMLH '), 'chunk-bin coverage differs')
        for entry in bins:
            require(set(entry) == {'bin', 'current', 'peak', 'total'}, 'chunk-bin fields differ')
            number_tree({k:v for k,v in entry.items() if k != 'bin'}, 'chunk_bins')
        number_tree({k:v for k,v in stats.items() if k != 'chunk_bins'}, 'stats')
        require(stats['stat_version'] == 5 and stats['mimalloc_version'] == 30405, 'statistics ABI mismatch')
        for key in ('pages', 'reserved', 'committed', 'malloc_normal', 'malloc_huge', 'malloc_requested'):
            require(set(stats[key]) == {'total', 'peak', 'current'}, f'incomplete statistics: {key}')
        for key in ('malloc_normal_count', 'malloc_huge_count'):
            integer(stats[key], key)
        small, large = int(phase == 'small_held') * 1024, int(phase == 'large_held') * 8
        require(row['known_small'] == small and row['known_large'] == large, 'retained pointer coverage differs')
        expected_bytes = baseline['block_bytes']
        if small:
            expected_bytes += config['small_held_usable_bytes']
        if large:
            expected_bytes += config['large_held_usable_bytes']
        require(row['blocks'] == baseline['blocks'] + small + large, 'live block count or release differs')
        require(row['block_bytes'] == expected_bytes, 'live block bytes or release differs')
        require(row['area_used'] == row['blocks'] and row['area_live_bin_bytes'] == row['block_bytes'],
                'area/block observations disagree')

    # Derive claims from raw observations; do not import run.py's classifier.
    released, small, large = (rows[index]['stats'] for index in (5, 6, 7))
    delta_small = small['malloc_normal_count'] - released['malloc_normal_count']
    delta_large = large['malloc_huge_count'] - small['malloc_huge_count']

    def count_signal(delta, expected):
        if delta == 0:
            return 'unsupported_no_signal'
        if delta == expected:
            return 'calibrated_tested_count'
        return 'unsupported_inconsistent_signal'

    base_bytes = baseline['stats']['malloc_huge']['current']
    held_bytes = rows[4]['stats']['malloc_huge']['current']
    released_bytes = released['malloc_huge']['current']
    huge = 'unsupported_inconsistent_signal'
    if held_bytes > base_bytes:
        if released_bytes == held_bytes:
            huge = 'not_live_bytes'
        elif released_bytes == base_bytes:
            huge = 'matches_tested_release_only'
    return dict(small_transient_count_delta=delta_small,
                small_churn=count_signal(delta_small, 10000),
                large_transient_count_delta=delta_large,
                large_churn=count_signal(delta_large, 128), huge_current=huge,
                live_snapshots='calibrated_known_main_heap_objects_only',
                backing='separate_nonadditive_diagnostic')


def path_name(name):
    require(type(name) is str and name and '\\' not in name, 'invalid record path')
    path = PurePosixPath(name)
    require(not path.is_absolute() and '..' not in path.parts and str(path) == name, 'unsafe record path')
    return name


def digest_info(data, item, name):
    require(type(item['sha256']) is str and re.fullmatch('[0-9a-f]{64}', item['sha256']), f'invalid digest: {name}')
    integer(item['bytes'], name)
    require(len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], f'hash mismatch: {name}')


def verify_files(read, names):
    require(len(names) == len(set(names)), 'duplicate archive members')
    for name in names:
        path_name(name)
    record = decode(read('record.json'))
    require(type(record['schema']) is int and record['schema'] == 1 and
            record['kind'] == 'stock-lean-allocation-capabilities', 'unsupported record')
    require(set(names) == set(record['files']) | {'record.json'}, 'inventory has omitted or extra files')
    for name, item in record['files'].items():
        digest_info(read(name), item, name)
    require(record['commands'] == 'commands.json', 'unexpected command log')
    claims = dict(whole_process_accounting=False, between_snapshot_peak=False,
                  timing=False, backend_hooks=False, production_rebuild=False)
    require(same_json(record['claims'], claims), 'unsupported measurement claim')
    toolchain = record['toolchain']
    require(toolchain['pin'] == PIN and 'version 4.35.0' in toolchain['version'], 'wrong Lean pin')
    require(toolchain['mimalloc_stats_header_blob'] == HEADER_BLOB, 'wrong allocator header pin')
    require(record['host']['system'] in ('Darwin', 'Linux'), 'unsupported host')
    require(record['environment'] == {'LEAN_CC': record['host']['cc'], 'LEAN_NUM_THREADS': '0'}, 'wrong execution environment')
    repo = record['repository']
    require(type(repo['head']) is str and re.fullmatch('[0-9a-f]{40}', repo['head']), 'invalid source revision')
    require(type(repo['status']) is str, 'missing source status')
    require(set(repo['inputs']) == REQUIRED_INPUTS, 'repository source coverage differs')
    for relative, item in repo['inputs'].items():
        expected = 'inputs/repository/' + relative
        require(item['snapshot'] == expected, 'wrong source snapshot path')
        data = read(expected)
        require(hashlib.sha256(data).hexdigest() == item['sha256'] == item['sha256_after'], 'source changed')
        if relative.endswith('lean-toolchain'):
            require(data.decode().strip() == PIN, 'snapshot pin mismatch')
    header = read('inputs/repository/' + EXPERIMENT + 'vendor/mimalloc-stats.h')
    blob = hashlib.sha1(b'blob ' + str(len(header)).encode() + b'\0' + header).hexdigest()
    require(blob == HEADER_BLOB, 'pinned header contents differ')
    require({'bin/lean', 'bin/leanc', 'lib/lean/libleanrt.a', 'include/lean/lean.h',
             'include/lean/mimalloc.h', 'include/lean/config.h'} <= set(toolchain['inputs']), 'missing toolchain fingerprints')
    for relative, item in toolchain['inputs'].items():
        path_name(relative)
        require(re.fullmatch('[0-9a-f]{64}', item['sha256']) and item['sha256'] == item['sha256_after'], 'toolchain changed')
        # The stock installation includes an intentionally empty lean_libuv.h.
        integer(item['bytes'], relative, 0 if relative.endswith('.h') else 1)
        if relative.endswith('.h'):
            require(item['snapshot'] == 'inputs/toolchain/' + relative, 'wrong header path')
            digest_info(read(item['snapshot']), item, relative)
    labels = ('lean-prefix', 'lean-version', 'cc-version', 'git-head', 'git-status', 'git-tracked-diff',
              'lean-emit', 'main-compile', 'probe-compile', 'link', 'binary-symbols', 'binary-linkage',
              'probe-1', 'probe-2', 'probe-3')
    commands = decode(read('commands.json'))
    require([c['label'] for c in commands] == list(labels), 'command coverage differs')
    for index, command in enumerate(commands):
        require(type(command['returncode']) is int and command['returncode'] == 0, 'command failed')
        require(type(command['argv']) is list and command['argv'] and
                all(type(x) is str and x for x in command['argv']), 'invalid command arguments')
        require(command['stdout'] == f'logs/{index:02d}-{labels[index]}.stdout' and
                command['stderr'] == f'logs/{index:02d}-{labels[index]}.stderr', 'incorrect log association')
        require(command['stdout'] in names and command['stderr'] in names, 'missing command output')
    for index, expected in ((0, toolchain['prefix']), (1, toolchain['version']),
                            (2, record['host']['cc_version']), (3, repo['head'])):
        require(read(commands[index]['stdout']).decode().strip() == expected, 'provenance/log mismatch')
    require(read(commands[4]['stdout']).decode() == repo['status'], 'status/log mismatch')
    require({'build/Main.c', 'build/Main.o', 'build/probe.o', 'build/capability-probe'} <= set(names), 'missing emitted/native files')
    require(read('build/Main.lean') == read('inputs/repository/' + EXPERIMENT + 'Main.lean'), 'built Lean input differs')
    runs = record['runs']
    require(type(runs) is list and len(runs) == 3, 'three fresh-process records required')
    classifications = []
    for index, run in enumerate(runs, 1):
        require(type(run['index']) is int and run['index'] == index, 'duplicate/missing run')
        command = commands[11 + index]
        require(run['stdout'] == command['stdout'] and run['stderr'] == command['stderr'] and
                run['parsed'] == f'runs/{index}.json', 'wrong run/log association')
        require(len(command['argv']) == 1 and command['argv'][0].endswith('/build/capability-probe'), 'wrong probe command')
        require(not read(run['stderr']).strip(), 'unexpected probe diagnostic')
        raw = stream(read(run['stdout']))
        require(same_json(raw, decode(read(run['parsed']))), 'raw/parsed observations differ')
        derived = observations(raw)
        require(same_json(derived, run['classification']), 'incorrect capability classification')
        classifications.append(derived)
    return dict(runs=3, snapshots=24, files=len(names), measured_head=repo['head'],
                classifications=classifications, timing='not measured', whole_process_accounting=False)


def verify(path):
    path = Path(path)
    if path.is_dir():
        entries = list(path.rglob('*'))
        require(not any(p.is_symlink() for p in entries), 'symlink in record')
        names = [p.relative_to(path).as_posix() for p in entries if p.is_file()]
        return verify_files(lambda name: (path / path_name(name)).read_bytes(), names)
    with zipfile.ZipFile(path) as archive:
        return verify_files(archive.read, archive.namelist())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('record', type=Path)
    print(json.dumps(verify(parser.parse_args().record), indent=2))


if __name__ == '__main__':
    main()
