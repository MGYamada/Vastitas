#!/usr/bin/env python3
"""Audit paired allocator calibration without executing retained programs."""
import argparse
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import re
import tarfile
import zipfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('stock_capability_verify', HERE.parent / 'stock_allocation_capabilities/verify.py')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
require, same, decode = base.require, base.same_json, base.decode
PIN = 'leanprover/lean4:v4.35.0'
ARCHIVE_SHA = '19a43af0645c57d348e729d5b31e23e912582911bb1047f795790834d3416221'
LEAN_BLOBS = {
    'runtime/mimalloc.cpp': '9a4d944d71115ef0c58e3227081338261369e286',
    'runtime/alloc.h': '489bae7d60484cf09de1f07cb3b716e568bd49e9',
    'runtime/alloc_tls.h': '9b956b24292819b1fa7975bf527d447053b5a13e',
    'runtime/debug.h': '1ddc06445c3a12b728e5ec3675fca9cd9d468bc4',
    'runtime/exception.h': '0004494591da4a03e63b41ec5eb65e5ffadd7e2a',
}
VARIANTS = ('stock', 'rebuilt0', 'diagnostic2')
CASES = (
    ('constructor', 1024, 10000, 40, 7),
    ('byte_array', 13, 257, 1025, 11),
    ('large_byte_array', 8, 128, 2097176, 11),
    ('closure', 19, 199, 32, 13),
    ('array', 17, 263, 824, 99),
)
PHASES = [('observer', 'baseline'), ('observer', 'repeat')]
PHASES += [(name, phase) for name, *_ in CASES for phase in ('held', 'released', 'churn')]
PHASES += [('observer', 'collection')]
COUNTS = ('malloc_normal_count', 'malloc_huge_count')
BYTES = ('malloc_normal', 'malloc_huge', 'malloc_requested')
CLAIMS = dict(timing=False, whole_process_accounting=False, production_runtime_modified=False,
              source_program_accounting=False, general_peak=False,
              diagnostic_counts_are_stock_counts=False)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def ar_objects(data):
    """Read ordinary BSD/GNU ar bytes; ignore only archive metadata tables."""
    require(data.startswith(b'!<arch>\n'), 'not an ordinary ar archive')
    cursor, strings, entries = 8, b'', []
    while cursor < len(data):
        header = data[cursor:cursor + 60]
        require(len(header) == 60 and header[58:] == b'`\n', 'malformed ar header')
        size = int(header[48:58].decode().strip())
        require(size >= 0 and cursor + 60 + size <= len(data), 'truncated ar member')
        payload = data[cursor + 60:cursor + 60 + size]
        name = header[:16].decode().strip()
        cursor += 60 + size + size % 2
        require(cursor <= len(data), 'missing ar padding')
        if name.startswith('#1/'):
            length = int(name[3:])
            require(0 < length <= len(payload), 'invalid BSD ar name')
            name, payload = payload[:length].rstrip(b'\0').decode(), payload[length:]
        elif name == '//':
            require(not strings, 'duplicate ar name table')
            strings = payload
            continue
        elif name.startswith('/') and name[1:].isdigit():
            offset = int(name[1:])
            require(offset < len(strings), 'invalid GNU ar name')
            end = strings.find(b'/\n', offset)
            require(end >= offset, 'unterminated GNU ar name')
            name = strings[offset:end].decode()
        elif name not in ('/', '/SYM64/'):
            name = name.removesuffix('/')
        if name in ('/', '/SYM64/', '__.SYMDEF', '__.SYMDEF SORTED', '__.SYMDEF_64', '__.SYMDEF_64 SORTED'):
            continue
        require(name.endswith('.o') and '/' not in name and name not in {n for n, _ in entries},
                'unsupported or duplicate runtime object')
        entries.append((name, payload))
    require(cursor == len(data) and entries, 'empty or trailing ar contents')
    return dict(entries)


def audit_replacement(stock, replacement, object_bytes):
    left, right = ar_objects(stock), ar_objects(replacement)
    require(list(left) == list(right), 'runtime object membership/order changed')
    changed = [name for name in left if left[name] != right[name]]
    require(changed == ['mimalloc.cpp.o'], 'runtime changes extend beyond mimalloc.cpp.o')
    require(right['mimalloc.cpp.o'] == object_bytes, 'replacement object does not match archive')
    return {name: digest(value) for name, value in right.items()}


def observation(rows, variant):
    require(variant in VARIANTS and len(rows) == len(PHASES) + 1, 'wrong variant/snapshot count')
    config = rows[0]
    fixed = dict(kind='configuration', mimalloc_version=30405, stats_version=5,
                 pointer_table_bytes=16384, workload_table_bytes=240, checksum_bytes=8,
                 checksum=sum((held + churn) * value for _, held, churn, _, value in CASES))
    require(set(config) == set(fixed) | {'workloads', 'snapshot_bytes'}, 'configuration fields differ')
    for key, value in fixed.items():
        require(same(config[key], value), f'configuration differs: {key}')
    base.integer(config['snapshot_bytes'], 'snapshot_bytes', 19 * 128 * 1024)
    require(len(config['workloads']) == len(CASES), 'workload coverage differs')
    for measured, (name, held, churn, size, _) in zip(config['workloads'], CASES):
        require(set(measured) == {'name', 'held', 'churn', 'object_bytes', 'usable_bytes'}, 'workload fields differ')
        require(same({k: v for k, v in measured.items() if k != 'usable_bytes'},
                     dict(name=name, held=held, churn=churn, object_bytes=size)), 'workload differs')
        base.integer(measured['usable_bytes'], 'usable_bytes', size)
    baseline = rows[1]
    for (name, phase), row in zip(PHASES, rows[1:]):
        require(set(row) == {'kind', 'workload', 'phase', 'visit_ok', 'stats_ok', 'json_ok',
                            'blocks', 'block_bytes', 'known', 'areas', 'area_blocks', 'area_bytes', 'stats'},
                'snapshot fields differ')
        require((row['kind'], row['workload'], row['phase']) == ('snapshot', name, phase), 'snapshot order/identity differs')
        require(all(row[k] is True for k in ('visit_ok', 'stats_ok', 'json_ok')), 'observer failed')
        for key in ('blocks', 'block_bytes', 'known', 'areas', 'area_blocks', 'area_bytes'):
            base.integer(row[key], key)
        workload = next((v for v in config['workloads'] if v['name'] == name), None)
        held = workload['held'] if phase == 'held' else 0
        amount = held * workload['usable_bytes'] if held else 0
        require(row['known'] == held and row['blocks'] == baseline['blocks'] + held and
                row['block_bytes'] == baseline['block_bytes'] + amount, 'known object/byte retention or release differs')
        require(row['area_blocks'] == row['blocks'] and row['area_bytes'] == row['block_bytes'], 'visitor totals disagree')
        stats = row['stats']
        bins = stats['chunk_bins']
        require([b['bin'] for b in bins] == list('SXMLH '), 'chunk bins differ')
        for entry in bins:
            require(set(entry) == {'bin', 'current', 'peak', 'total'}, 'chunk-bin fields differ')
            base.number_tree({k: v for k, v in entry.items() if k != 'bin'}, 'bins')
        base.number_tree({k: v for k, v in stats.items() if k != 'chunk_bins'}, 'stats')
        require(stats['stat_version'] == 5 and stats['mimalloc_version'] == 30405, 'wrong statistics ABI')
        for key in BYTES:
            require(set(stats[key]) == {'current', 'peak', 'total'}, 'incomplete allocator byte channel')
        for key in COUNTS:
            base.integer(stats[key], key)
    # Repeated observations, release samples and explicit collection cannot be
    # silently charged as workload churn. Preserve totals rather than resetting.
    def selected(row):
        return {key: row['stats'][key] for key in COUNTS + BYTES}
    require(same(selected(rows[1]), selected(rows[2])), 'observer creates allocation signal')
    require(same(selected(rows[-2]), selected(rows[-1])), 'collection changes allocation signal')
    signals = []
    for index, workload in enumerate(config['workloads']):
        before, held, released, churn = rows[2 + 3 * index:6 + 3 * index]
        huge = workload['name'] == 'large_byte_array'
        kind = 'malloc_huge' if huge else 'malloc_normal'
        other = 'malloc_normal' if huge else 'malloc_huge'
        delta = churn['stats'][kind + '_count'] - released['stats'][kind + '_count']
        signals.append(delta)
        for a, b in ((before, held), (held, released), (released, churn)):
            require(b['stats'][other + '_count'] == a['stats'][other + '_count'], 'allocation on unexpected size channel')
            require(same(b['stats'][other], a['stats'][other]), 'bytes change on unexpected size channel')
        if variant == 'stock':
            # Record what the installation exposes; do not assume its build flags.
            continue
        normal_enabled = variant == 'diagnostic2'
        tracked = huge or normal_enabled
        initial = before['stats']
        for row, total_n, live_n in ((held, workload['held'], workload['held']),
                                    (released, workload['held'], 0),
                                    (churn, workload['held'] + workload['churn'], 0)):
            stats = row['stats']
            require(stats[kind + '_count'] == initial[kind + '_count'] + (total_n if tracked else 0),
                    'known allocation count differs')
            require(stats[kind]['total'] == initial[kind]['total'] + (total_n * workload['usable_bytes'] if tracked else 0),
                    'known binned allocation total differs')
            live = live_n if normal_enabled else total_n if huge else 0
            require(stats[kind]['current'] == initial[kind]['current'] + live * workload['usable_bytes'],
                    'binned live/cumulative byte distinction differs')
            request = total_n * workload['object_bytes'] if normal_enabled and not huge else 0
            for key in ('total', 'current'):
                require(stats['malloc_requested'][key] == initial['malloc_requested'][key] + request,
                        'requested counter is neither complete nor live bytes')
        require(same(selected(held)['malloc_requested'], selected(released)['malloc_requested']),
                'requested accounting unexpectedly decrements on free')
    return dict(workloads=len(CASES), snapshots=len(PHASES), transient_count_deltas=signals,
                known_live_objects='visitor_calibrated',
                binned_current='known_release_calibrated' if variant == 'diagnostic2' else 'not_assumed_live',
                requested_current='not_a_general_live_or_total_byte_channel',
                startup_and_general_peaks='not_calibrated')


def verify_files(read, names):
    require(len(names) == len(set(names)), 'duplicate archive members')
    for name in names:
        base.path_name(name)
    record = decode(read('record.json'))
    require(type(record['schema']) is int and record['schema'] == 1 and
            record['kind'] == 'lean-allocation-diagnostic', 'unsupported record')
    require(set(names) == set(record['files']) | {'record.json'}, 'omitted/extra inventory files')
    for name, item in record['files'].items():
        base.digest_info(read(name), item, name)
    require(same(record['claims'], CLAIMS), 'unsupported allocation claim')
    require(record['environment'] == {'LEAN_NUM_THREADS': '0', 'LEAN_MAIN_USE_THREAD': '1',
                                      'LEAN_CC': record['host']['cc']}, 'wrong execution environment')
    require(record['host']['system'] in ('Darwin', 'Linux'), 'unsupported platform')
    require(record['toolchain']['pin'] == PIN and 'version 4.35.0' in record['toolchain']['version'], 'wrong Lean toolchain')
    require(digest(read('inputs/mimalloc-v3.4.5.tar.gz')) == ARCHIVE_SHA, 'wrong mimalloc source archive')
    for path, blob in LEAN_BLOBS.items():
        data = read('inputs/repository/experiments/lean_allocation_diagnostic/vendor/lean/' + path)
        require(hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob,
                'changed upstream Lean allocator source')
    repo = record['repository']
    require(re.fullmatch('[0-9a-f]{40}', repo['head']) and type(repo['status']) is str, 'missing source provenance')
    required = {'lean-toolchain', 'lean-kernel/lean-toolchain'}
    required |= {'experiments/lean_allocation_diagnostic/' + p for p in (
        'Main.lean', 'probe.c', 'run.py', 'verify.py', 'test_diagnostic.py', 'README.md',
        'upstream-sources.json', 'vendor/LICENSE.lean')}
    required |= {'experiments/lean_allocation_diagnostic/vendor/lean/' + p for p in LEAN_BLOBS}
    required |= {'experiments/stock_allocation_capabilities/' + p for p in (
        'verify.py', 'vendor/mimalloc-stats.h', 'vendor/LICENSE.mimalloc')}
    require(set(repo['inputs']) == required, 'source input coverage differs')
    for name, item in repo['inputs'].items():
        require(item['snapshot'] == 'inputs/repository/' + name, 'wrong repository snapshot')
        require(digest(read(item['snapshot'])) == item['sha256'] == item['sha256_after'], 'repository input changed')
        if name.endswith('lean-toolchain'):
            require(read(item['snapshot']).decode().strip() == PIN, 'source toolchain pin differs')
    header = read('inputs/repository/experiments/stock_allocation_capabilities/vendor/mimalloc-stats.h')
    require(hashlib.sha1(b'blob ' + str(len(header)).encode() + b'\0' + header).hexdigest() == base.HEADER_BLOB,
            'changed statistics ABI header')
    with tarfile.open(fileobj=io.BytesIO(read('inputs/mimalloc-v3.4.5.tar.gz'))) as archive:
        header = archive.extractfile('mimalloc-3.4.5/include/mimalloc.h').read()
        require(header == read('inputs/toolchain/include/lean/mimalloc.h'), 'installed allocator API differs')
    external = record['toolchain']['inputs']
    require({'bin/lean', 'bin/leanc', 'lib/lean/libleanrt.a', 'include/lean/lean.h',
             'include/lean/config.h', 'include/lean/mimalloc.h'} <= set(external), 'missing toolchain fingerprints')
    require({'lib/lean/lib' + n + '.a' for n in ('leancpp', 'Init', 'Std', 'Lean', 'Lake', 'LeanExport')} <= set(external),
            'missing linked Lean library fingerprints')
    for name, item in external.items():
        base.path_name(name)
        require(re.fullmatch('[0-9a-f]{64}', item['sha256']) and item['sha256'] == item['sha256_after'], 'installed toolchain changed')
        if name.endswith('.h') or name == 'lib/lean/libleanrt.a':
            require(item['snapshot'] == 'inputs/toolchain/' + name, 'wrong installed input snapshot')
            base.digest_info(read(item['snapshot']), item, name)
    stock = read('inputs/toolchain/lib/lean/libleanrt.a')
    stock_objects = ar_objects(stock)
    require({'alloc.cpp.o', 'object.cpp.o', 'mimalloc.cpp.o'} <= set(stock_objects), 'unexpected installed runtime object domain')
    require(set(record['archives']) == set(VARIANTS), 'runtime archive variants differ')
    for variant in VARIANTS:
        item = record['archives'][variant]
        path = f'build/{variant}/libleanrt.a'
        require(item['path'] == path, 'wrong selected runtime archive')
        data = read(path)
        if variant == 'stock':
            require(data == stock, 'stock runtime was rebuilt')
            members = {n: digest(b) for n, b in stock_objects.items()}
        else:
            members = audit_replacement(stock, data, read(f'build/{variant}/mimalloc.cpp.o'))
        require(item['members'] == members, 'incorrect runtime member fingerprints')
        mapping = read(f'build/{variant}/link.map').decode()
        paths = set(re.findall(r'(/[^\s()]+/libleanrt\.a)\(', mapping))
        require(paths == {record['output_path'] + '/' + path}, 'link map selects a foreign runtime archive')
        require('mimalloc.cpp.o' in mapping and 'lean_alloc_small_object_core' in mapping and
                'mi_free' in mapping, 'allocator link origins missing')
    require({'build/Main.c', 'build/main.o', 'build/probe.o'} | {f'build/{v}/probe' for v in VARIANTS} <= set(names),
            'missing emitted C, compiled objects or executables')
    commands = decode(read('commands.json'))
    require(len(commands) == len({c['label'] for c in commands}), 'duplicate commands')
    for i, command in enumerate(commands):
        require(type(command['returncode']) is int and command['returncode'] == 0, 'command failed')
        require(type(command['argv']) is list and command['argv'] and
                all(type(x) is str and x for x in command['argv']), 'invalid command argv')
        require(command['stdout'] == f'logs/{i:02d}-{command["label"]}.stdout' and
                command['stderr'] == f'logs/{i:02d}-{command["label"]}.stderr', 'wrong command/log mapping')
        require(command['stdout'] in names and command['stderr'] in names, 'missing command output')
    by_label = {c['label']: c for c in commands}
    labels = ['lean-prefix', 'lean-version', 'cc-version', 'cxx-version', 'git-head', 'git-status', 'git-diff']
    if 'download-mimalloc' in by_label:
        labels.append('download-mimalloc')
    labels += ['lean-emit', 'main-compile', 'probe-compile']
    for variant in VARIANTS:
        if variant != 'stock':
            labels += [variant + '-compile', variant + '-archive']
        labels += [variant + '-link', variant + '-symbols', variant + '-linkage']
        labels += [f'{variant}-run-{i}' for i in range(1, 4)]
    require([c['label'] for c in commands] == labels, 'build/run command coverage differs')
    require(read(by_label['git-head']['stdout']).decode().strip() == repo['head'] and
            read(by_label['git-status']['stdout']).decode() == repo['status'], 'source revision/log mismatch')
    for label, expected in (('lean-prefix', record['toolchain']['prefix']),
                            ('lean-version', record['toolchain']['version']),
                            ('cc-version', record['host']['cc_version']), ('cxx-version', record['host']['cxx_version'])):
        require(read(by_label[label]['stdout']).decode().strip() == expected, 'toolchain/log mismatch')
    output, prefix = record['output_path'], record['toolchain']['prefix']
    source = output + '/inputs/repository/experiments/lean_allocation_diagnostic'
    require(read('build/Main.lean') == read('inputs/repository/experiments/lean_allocation_diagnostic/Main.lean'),
            'built Lean source differs from snapshot')
    require(by_label['lean-emit']['argv'] == [prefix + '/bin/lean', '-c', 'Main.c', 'Main.lean'] and
            by_label['lean-emit']['cwd'] == output + '/build', 'wrong Lean-to-C compilation')
    cflags = ['-O3', '-Wall', '-Wextra', '-Werror', '-I' + prefix + '/include/lean']
    for name, input_path in (('main', output + '/build/Main.c'), ('probe', source + '/probe.c')):
        require(by_label[name + '-compile']['argv'] == [prefix + '/bin/leanc', *cflags, '-c', input_path,
                                                       '-o', output + '/build/' + name + '.o'], 'wrong probe C input/output')
    for variant in VARIANTS:
        directory = output + '/build/' + variant
        map_flag = '-Wl,-map,' if record['host']['system'] == 'Darwin' else '-Wl,-Map,'
        expected = [prefix + '/bin/leanc', '-v', '-L' + directory, '-L' + prefix + '/lib',
                    output + '/build/main.o', output + '/build/probe.o', map_flag + directory + '/link.map',
                    '-o', directory + '/probe']
        require(by_label[variant + '-link']['argv'] == expected, 'wrong probe/runtime linkage')
        if variant != 'stock':
            require(by_label[variant + '-archive']['argv'] == [record['host']['ar'], 'r', directory + '/libleanrt.a',
                                                               directory + '/mimalloc.cpp.o'], 'wrong archive replacement')
    # Both rebuilds differ by MI_STAT alone, including compiler and include paths.
    zero, two = (by_label[v + '-compile']['argv'] for v in VARIANTS[1:])
    normalized = lambda args: [a.replace('rebuilt0', 'VARIANT').replace('diagnostic2', 'VARIANT')
                               .replace('-DMI_STAT=0', '-DMI_STAT=N').replace('-DMI_STAT=2', '-DMI_STAT=N') for a in args]
    require(normalized(zero) == normalized(two), 'rebuild flags differ beyond MI_STAT/output')
    for args, level in ((zero, 0), (two, 2)):
        require(args[0] == record['host']['cxx'] and f'-DMI_STAT={level}' in args and
                '-DNDEBUG' in args and '-DMI_SECURE=0' in args and '-DMI_MAX_ALIGN_SIZE=8' in args,
                'wrong diagnostic allocator profile')
        include = [a[2:] for a in args if a.startswith('-I') and a.endswith('/mimalloc-3.4.5/include')]
        require(len(include) == 1, 'missing pinned allocator include path')
        allocator = include[0].removesuffix('/include')
        expected = [record['host']['cxx'], '-std=c++20', '-O3', '-DNDEBUG', '-DMI_SHARED_LIB', '-DMI_SHARED_LIB_EXPORT',
                    '-DMI_WIN_NOREDIRECT', '-DMI_MAX_ALIGN_SIZE=8', '-DMI_SECURE=0', '-DLEAN_EXPORTING', '-fPIC',
                    '-fvisibility=hidden', '-fvisibility-inlines-hidden', '-ftls-model=local-exec',
                    '-Wno-unused-function', '-Wno-deprecated']
        if record['host']['system'] == 'Linux':
            expected += ['-stdlib=libc++']
        expected += ['-I' + p for p in (prefix + '/include', source + '/vendor/lean', allocator + '/include', allocator + '/src')]
        variant = 'rebuilt0' if level == 0 else 'diagnostic2'
        expected += [f'-DMI_STAT={level}', '-c', source + '/vendor/lean/runtime/mimalloc.cpp',
                     '-o', output + f'/build/{variant}/mimalloc.cpp.o']
        require(args == expected, 'allocator compiler inputs/flags differ')
    for command in commands:
        if command['label'].endswith(('-compile', '-link')) or command['label'] == 'lean-emit':
            require(command['environment'] == record['environment'], 'wrong build environment')
    runs = record['runs']
    require([(r['variant'], r['index']) for r in runs] == [(v, i) for v in VARIANTS for i in range(1, 4)],
            'exact three-variant/three-process coverage required')
    configurations = []
    for run in runs:
        variant, index = run['variant'], run['index']
        command = by_label[f'{variant}-run-{index}']
        require(command['argv'] == [record['output_path'] + f'/build/{variant}/probe'] and
                command['environment'] == record['environment'], 'wrong probe executable/environment')
        require(run['stdout'] == command['stdout'] and run['stderr'] == command['stderr'] and
                run['parsed'] == f'runs/{variant}-{index}.json', 'incorrect run/log association')
        require(not read(run['stderr']).strip(), 'unexpected runtime diagnostic')
        raw = base.stream(read(run['stdout']))
        require(same(raw, decode(read(run['parsed']))), 'raw/parsed observations differ')
        require(same(observation(raw, variant), run['calibration']), 'calibration claim differs')
        configurations.append(raw[0])
    require(all(same(configurations[0], c) for c in configurations[1:]), 'variant object layouts/checksums differ')
    return dict(runs=9, snapshots=162, workloads=5, unchanged_runtime_objects=len(stock_objects) - 1,
                measured_head=repo['head'], files=len(names), claims=CLAIMS)


def verify(path):
    path = Path(path)
    if path.is_dir():
        entries = list(path.rglob('*'))
        require(not any(p.is_symlink() for p in entries), 'symlink in record')
        names = [p.relative_to(path).as_posix() for p in entries if p.is_file()]
        return verify_files(lambda n: (path / base.path_name(n)).read_bytes(), names)
    with zipfile.ZipFile(path) as archive:
        return verify_files(archive.read, archive.namelist())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('record', type=Path)
    print(json.dumps(verify(parser.parse_args().record), indent=2))
