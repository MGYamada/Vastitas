#!/usr/bin/env python3
"""Replay a complete lifetime calibration without executing retained code."""
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
spec = importlib.util.spec_from_file_location('lifetime_observation_replay', HERE / 'observation.py')
observation = importlib.util.module_from_spec(spec)
spec.loader.exec_module(observation)
profile = observation.module('lifetime_build_profile', HERE / 'profile.py')
instrument = observation.module('lifetime_source_instrumentation', HERE / 'instrument.py')
render = observation.render
calibration = observation.calibration
base = calibration.base
require, same, decode, digest = calibration.require, calibration.same, calibration.decode, calibration.digest
SANITIZER_ENV = dict(ASAN_OPTIONS='detect_leaks=0:halt_on_error=1',
                     UBSAN_OPTIONS='halt_on_error=1:print_stacktrace=1')
FORBIDDEN_ENV = ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'DYLD_INSERT_LIBRARIES', 'DYLD_LIBRARY_PATH',
                 'DYLD_FALLBACK_LIBRARY_PATH', 'CPATH', 'C_INCLUDE_PATH', 'CPLUS_INCLUDE_PATH',
                 'LIBRARY_PATH', 'COMPILER_PATH', 'GCC_EXEC_PREFIX', 'LEAN_CFLAGS', 'LEAN_LDFLAGS')


def verify_files(read, names):
    require(len(names) == len(set(names)), 'duplicate record members')
    for name in names:
        base.path_name(name)
    record = decode(read('record.json'))
    require(set(record) == {'schema', 'kind', 'created_utc', 'output_path', 'repository', 'toolchain',
                           'host', 'environment', 'removed_environment', 'claims', 'runtime', 'runs', 'files'},
            'lifetime record fields')
    require(type(record['schema']) is int and record['schema'] == 1 and
            record['kind'] == 'lean-allocation-lifetimes', 'lifetime record schema')
    require(set(names) == set(record['files']) | {'record.json'}, 'omitted/extra inventory files')
    for name, item in record['files'].items():
        base.digest_info(read(name), item, name)
    required_build = {'Main.lean', 'Main.c', 'main.o', 'probe.c', 'probe.o', 'lifetime.o',
                      'runtime/mimalloc.cpp.o', 'runtime/libleanrt.a', 'native-mimalloc.o',
                      'lean-probe', 'lean-link.map', 'native-probe', 'native-link.map', 'sanitized-probe'}
    require({'build/' + name for name in required_build} <= set(names), 'missing compiled calibration artifacts')
    require(same(record['claims'], profile.CLAIMS), 'unsupported lifetime claim')
    repo, host, toolchain = (record[k] for k in ('repository', 'host', 'toolchain'))
    output, prefix = record['output_path'], toolchain['prefix']
    require(all(type(p) is str and Path(p).is_absolute() for p in (output, prefix)), 'absolute record paths')
    require(host['system'] in ('Darwin', 'Linux'), 'unsupported host')
    require(toolchain['pin'] == calibration.PIN and 'version 4.35.0' in toolchain['version'], 'Lean pin')
    require(same(record['environment'], dict(LEAN_CC=host['cc'], LEAN_NUM_THREADS='0', LEAN_MAIN_USE_THREAD='1')),
            'lifetime execution environment')
    removed = record['removed_environment']
    require(type(removed) is list and all(type(k) is str and
            (k.startswith('MIMALLOC_') or k in ('ASAN_OPTIONS', 'UBSAN_OPTIONS', 'LSAN_OPTIONS')) for k in removed) and
            removed == sorted(set(removed)), 'removed environment names')
    require(re.fullmatch('[0-9a-f]{40}', repo['head']) and type(repo['status']) is str, 'source provenance')
    require(set(repo['inputs']) == set(profile.REPOSITORY), 'source input coverage')
    for name, item in repo['inputs'].items():
        require(item['snapshot'] == 'inputs/repository/' + name, 'source snapshot path')
        require(digest(read(item['snapshot'])) == item['sha256'] == item['sha256_after'], 'source input changed')
        if name.endswith('lean-toolchain'):
            require(read(item['snapshot']).decode().strip() == calibration.PIN, 'source toolchain pin')
    # Native fixture/observer semantics are this trusted profile, not executable
    # scripts supplied by the record. A new native profile needs an explicit audit.
    for name in ('lifetime.h', 'lifetime.cpp', 'native_probe.cpp'):
        require(read('inputs/repository/experiments/lean_allocation_lifetimes/' + name) ==
                (HERE / name).read_bytes(), 'unreviewed lifetime native source: ' + name)
    original = 'inputs/repository/experiments/lean_allocation_diagnostic/'
    for name in ('Main.lean', 'probe.c'):
        require(read(original + name) == (HERE.parent / 'lean_allocation_diagnostic' / name).read_bytes(),
                'unreviewed original Lean fixture')
    for name, blob in calibration.LEAN_BLOBS.items():
        data = read(original + 'vendor/lean/' + name)
        require(hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob,
                'changed upstream Lean allocator source')
    stats = read('inputs/repository/experiments/stock_allocation_capabilities/vendor/mimalloc-stats.h')
    require(hashlib.sha1(b'blob ' + str(len(stats)).encode() + b'\0' + stats).hexdigest() == base.HEADER_BLOB,
            'changed allocator statistics ABI')
    raw_archive = read('inputs/mimalloc-v3.4.5.tar.gz')
    require(digest(raw_archive) == calibration.ARCHIVE_SHA, 'pinned allocator archive')
    with tarfile.open(fileobj=io.BytesIO(raw_archive)) as archive:
        originals = {item.name.removeprefix('mimalloc-3.4.5/'): archive.extractfile(item).read()
                     for item in archive.getmembers() if item.isfile()}
    changes = instrument.transformed({name: originals[name].decode() for name, _, _ in instrument.PATCHES})
    receipts = {name: dict(before_sha256=digest(originals[name]), after_sha256=digest(text.encode()))
                for name, text in changes.items()}
    require(same(decode(read('patches.json')), receipts), 'patch receipt differs from pinned-source reconstruction')
    tree = 'build/mimalloc-3.4.5/'
    require({p for p in names if p.startswith(tree)} == {tree + p for p in originals}, 'allocator source tree coverage')
    for name, original_bytes in originals.items():
        expected = changes[name].encode() if name in changes else original_bytes
        require(read(tree + name) == expected, 'allocator source differs beyond diagnostic hooks: ' + name)
    require(originals['include/mimalloc.h'] == read('inputs/toolchain/include/lean/mimalloc.h'), 'installed allocator API')
    external = toolchain['inputs']
    required = {'bin/lean', 'bin/leanc', 'lib/lean/libleanrt.a', 'include/lean/lean.h',
                'include/lean/config.h', 'include/lean/mimalloc.h'}
    required |= {'lib/lean/lib' + n + '.a' for n in ('leancpp', 'Init', 'Std', 'Lean', 'Lake', 'LeanExport')}
    require(required <= set(external), 'toolchain fingerprint coverage')
    for name, item in external.items():
        base.path_name(name)
        require(item['path'] == prefix + '/' + name and re.fullmatch('[0-9a-f]{64}', item['sha256']) and
                item['sha256'] == item['sha256_after'], 'toolchain input changed')
        if name.endswith('.h') or name == 'lib/lean/libleanrt.a':
            require(item['snapshot'] == 'inputs/toolchain/' + name, 'toolchain snapshot path')
            base.digest_info(read(item['snapshot']), item, name)
    stock = read('inputs/toolchain/lib/lean/libleanrt.a')
    runtime = 'build/runtime/libleanrt.a'
    members = calibration.audit_replacement(stock, read(runtime), read('build/runtime/mimalloc.cpp.o'))
    require(same(record['runtime'], dict(path=runtime, members=members)), 'runtime member receipt')
    mapping = read('build/lean-link.map').decode()
    paths = set(re.findall(r'(/[^\s()]+/libleanrt\.a)\(', mapping))
    require(paths == {output + '/' + runtime}, 'foreign Lean runtime in link map')
    require(all(p in mapping for p in ('mimalloc.cpp.o', 'lean_alloc_small_object_core',
                'mi_free', 'vastitas_heap_snapshot', output + '/build/lifetime.o')), 'missing allocator/observer linkage')
    linked = set(re.findall(r'(/[^\s()]+\.a)\(', mapping))
    for name, item in external.items():
        if name.endswith('.a') and name != 'lib/lean/libleanrt.a':
            matches = {p for p in linked if Path(p).name == Path(name).name}
            require(not matches or matches == {item['path']}, 'foreign support archive in link map')
    native_map = read('build/native-link.map').decode()
    require(all(p in native_map for p in (output + '/build/native-mimalloc.o', output + '/build/lifetime.o',
                                         'mi_free', 'vastitas_heap_snapshot')), 'native calibration linkage')
    require('libleanrt.a' not in native_map, 'native calibration unexpectedly uses Lean runtime')
    require(read('build/Main.lean') == read(original + 'Main.lean'), 'emitted Lean input')
    require(read('build/probe.c') == render.lean_probe(read(original + 'probe.c').decode()).encode(),
            'emitted Lean probe differs from trusted observation transform')
    commands = decode(read('commands.json'))
    require(type(commands) is list and len(commands) == len({c['label'] for c in commands}), 'command labels')
    build_commands = profile.commands(output, prefix, host)
    labels = ['lean-prefix', 'lean-version', 'cc-version', 'cxx-version', 'git-head', 'git-status', 'git-diff']
    by_label = {c['label']: c for c in commands}
    if 'download-mimalloc' in by_label:
        labels.append('download-mimalloc')
    labels += list(build_commands) + ['lean-symbols', 'lean-linkage']
    coverage = [(v, i) for v in ('lean', 'native') for i in range(1, 4)] + [('sanitized', 1)]
    labels += [f'{v}-run-{i}' for v, i in coverage] + ['native-capacity', 'sanitized-capacity']
    require([c['label'] for c in commands] == labels, 'build/run command coverage')
    for index, command in enumerate(commands):
        label = command['label']
        require(type(command['returncode']) is int and command['returncode'] ==
                (90 if label.endswith('-capacity') else 0), 'unexpected command failure')
        require(type(command['argv']) is list and command['argv'] and
                all(type(x) is str and x for x in command['argv']), 'command argv')
        require(command['stdout'] == f'logs/{index:02d}-{label}.stdout' and
                command['stderr'] == f'logs/{index:02d}-{label}.stderr', 'command/log association')
        require(command['stdout'] in names and command['stderr'] in names, 'missing command logs')
        env = dict(record['environment'])
        if label.startswith('sanitized-') and label != 'sanitized-link':
            env.update(SANITIZER_ENV)
        require(same(command['environment'], env), 'build/run environment differs')
    for label, expected in (('lean-prefix', prefix), ('lean-version', toolchain['version']),
            ('cc-version', host['cc_version']), ('cxx-version', host['cxx_version']), ('git-head', repo['head'])):
        require(read(by_label[label]['stdout']).decode().strip() == expected, 'provenance/log mismatch')
    require(read(by_label['git-status']['stdout']).decode() == repo['status'], 'source status/log mismatch')
    fixed_commands = {'lean-prefix': ['lean', '--print-prefix'],
        'lean-version': [prefix + '/bin/lean', '--version'], 'cc-version': [host['cc'], '--version'],
        'cxx-version': [host['cxx'], '--version'], 'git-head': ['git', 'rev-parse', 'HEAD'],
        'git-status': ['git', 'status', '--porcelain'], 'git-diff': ['git', 'diff', '--binary', 'HEAD'],
        'lean-symbols': ['nm', '-g', output + '/build/lean-probe'],
        'lean-linkage': (['otool', '-L'] if host['system'] == 'Darwin' else ['ldd']) + [output + '/build/lean-probe']}
    if 'download-mimalloc' in by_label:
        fixed_commands['download-mimalloc'] = ['curl', '--fail', '--location', '--silent', '--show-error',
            'https://github.com/microsoft/mimalloc/archive/v3.4.5.tar.gz', '-o', output + '/inputs/mimalloc-v3.4.5.tar.gz']
    for label, argv in fixed_commands.items():
        require(by_label[label]['argv'] == argv, 'provenance command differs: ' + label)
    for label, argv in build_commands.items():
        require(by_label[label]['argv'] == argv and by_label[label]['cwd'] == output + '/build',
                'compiler inputs/outputs/flags differ: ' + label)
    runs = record['runs']
    require([(r['variant'], r['index']) for r in runs] == coverage, 'fresh process coverage')
    summaries = []
    for run in runs:
        variant, index = run['variant'], run['index']
        command = by_label[f'{variant}-run-{index}']
        require(command['argv'] == [output + '/build/' + variant + '-probe'] and command['cwd'] == output,
                'wrong calibration executable')
        require(run['stdout'] == command['stdout'] and run['stderr'] == command['stderr'] and
                run['parsed'] == f'runs/{variant}-{index}.json', 'run/log association')
        require(not read(run['stderr']).strip(), 'unexpected calibration runtime diagnostic')
        rows = base.stream(read(run['stdout']))
        require(same(rows, decode(read(run['parsed']))), 'raw/parsed observation mismatch')
        summary = observation.lean(rows) if variant == 'lean' else observation.native(rows)
        require(same(summary, run['calibration']), 'computed calibration claim mismatch')
        summaries.append(summary)
    for variant in ('native', 'sanitized'):
        command = by_label[variant + '-capacity']
        require(command['argv'] == [output + '/build/' + variant + '-probe', 'capacity'] and
                command['cwd'] == output, 'wrong capacity failure executable')
        require(read(command['stdout']) == b'' and read(command['stderr']) == profile.AUDIT_FAILURE,
                'capacity limit silently truncated or failed for another reason')
    return dict(runs=len(runs), lean_snapshots=54, native_snapshots=44,
                unchanged_runtime_objects=len(members)-1, measured_head=repo['head'],
                observer_static_bytes=observation.OBSERVER_BYTES, files=len(names), claims=profile.CLAIMS,
                lean=summaries[:3], native=summaries[3:])


def verify(path):
    path = Path(path)
    if path.is_dir():
        entries = list(path.rglob('*'))
        require(not any(p.is_symlink() for p in entries), 'symlink in lifetime record')
        names = [p.relative_to(path).as_posix() for p in entries if p.is_file()]
        return verify_files(lambda name: (path / base.path_name(name)).read_bytes(), names)
    with zipfile.ZipFile(path) as archive:
        return verify_files(archive.read, archive.namelist())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('record', type=Path)
    print(json.dumps(verify(parser.parse_args().record), indent=2))
