#!/usr/bin/env python3
"""Calibrate an unchanged installed Lean runtime; never a timing benchmark."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PIN = 'leanprover/lean4:v4.35.0'
HEADER_BLOB = 'b4e19c09aaa2b18bae1b1d5f0e4591967a99452f'
RUNS = 3


def sha256(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def stream_json(text):
    decoder, rows = json.JSONDecoder(), []
    while text.strip():
        text = text.lstrip()
        value, end = decoder.raw_decode(text)
        rows.append(value)
        text = text[end:]
    return rows


def classify(rows):
    """Claims repeated independently by verify.py, not a complete allocator model."""
    snapshots = {row['phase']: row for row in rows[1:]}
    before = snapshots['large_released']['stats']
    small = snapshots['small_transient']['stats']
    large = snapshots['large_transient']['stats']
    normal_delta = small['malloc_normal_count'] - before['malloc_normal_count']
    huge_delta = large['malloc_huge_count'] - small['malloc_huge_count']
    held = snapshots['large_held']['stats']['malloc_huge']['current']
    released = before['malloc_huge']['current']
    baseline = snapshots['baseline']['stats']['malloc_huge']['current']
    return {
        'small_transient_count_delta': normal_delta,
        'small_churn': ('unsupported_no_signal' if normal_delta == 0 else
                        'calibrated_tested_count' if normal_delta == 10000 else
                        'unsupported_inconsistent_signal'),
        'large_transient_count_delta': huge_delta,
        'large_churn': ('calibrated_tested_count' if huge_delta == 128 else
                        'unsupported_no_signal' if huge_delta == 0 else
                        'unsupported_inconsistent_signal'),
        'huge_current': ('not_live_bytes' if held > baseline and released == held else
                         'matches_tested_release_only' if held > baseline and released == baseline else
                         'unsupported_inconsistent_signal'),
        'live_snapshots': 'calibrated_known_main_heap_objects_only',
        'backing': 'separate_nonadditive_diagnostic',
    }


class Runner:
    def __init__(self, out):
        self.out, self.commands = out, []
        (out / 'logs').mkdir()

    def run(self, args, *, cwd=ROOT, env=None, label):
        args = [str(x) for x in args]
        result = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True)
        index = len(self.commands)
        stdout = f'logs/{index:02d}-{label}.stdout'
        stderr = f'logs/{index:02d}-{label}.stderr'
        (self.out / stdout).write_text(result.stdout)
        (self.out / stderr).write_text(result.stderr)
        self.commands.append(dict(argv=args, cwd=str(cwd), label=label,
                                  returncode=result.returncode, stdout=stdout, stderr=stderr))
        dump(self.out / 'commands.json', self.commands)
        if result.returncode:
            raise RuntimeError(f'{label} failed ({result.returncode}); see {self.out / stderr}')
        return result.stdout, stdout, stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True, help='new output directory (must not exist)')
    parser.add_argument('--cc', default=os.environ.get('CC', 'cc'), help='host compiler executable; no shell arguments')
    args = parser.parse_args()
    out = args.out.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError('Record output must be outside the source checkout')
    # Exclusive creation, including failure on a preexisting empty directory.
    out.mkdir(parents=True, exist_ok=False)
    if platform.system() not in ('Darwin', 'Linux'):
        raise RuntimeError('This calibration currently supports macOS and Linux only')
    cc = shutil.which(args.cc)
    if not cc:
        raise RuntimeError(f'host compiler executable not found: {args.cc}')
    cc = str(Path(cc).resolve())
    runner = Runner(out)
    pins = [(ROOT / p).read_text().strip() for p in ('lean-toolchain', 'lean-kernel/lean-toolchain')]
    if pins != [PIN, PIN]:
        raise RuntimeError('Revalidate the mimalloc header/API and probe when the repository toolchain changes')
    prefix = Path(runner.run(['lean', '--print-prefix'], cwd=ROOT/'lean-kernel', label='lean-prefix')[0].strip()).resolve()
    lean, leanc = prefix/'bin/lean', prefix/'bin/leanc'
    version = runner.run([lean, '--version'], label='lean-version')[0].strip()
    if 'version 4.35.0' not in version:
        raise RuntimeError(f'Unexpected installed Lean: {version}')
    cc_version = runner.run([cc, '--version'], label='cc-version')[0].strip()
    header = (HERE/'vendor/mimalloc-stats.h').read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(header)).encode() + b'\0' + header).hexdigest()
    if blob != HEADER_BLOB:
        raise RuntimeError('mimalloc-stats.h differs from the exact pinned upstream Git blob')

    repo_files = sorted(p for p in HERE.rglob('*') if p.is_file()
                        and not {'results', '__pycache__'}.intersection(p.relative_to(HERE).parts)
                        and p.suffix != '.pyc')
    repo_files += [ROOT/'lean-toolchain', ROOT/'lean-kernel/lean-toolchain']
    source_inputs = {}
    for path in repo_files:
        relative = path.relative_to(ROOT).as_posix()
        snapshot = out/'inputs/repository'/relative
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, snapshot)
        source_inputs[relative] = {'snapshot': snapshot.relative_to(out).as_posix(), 'sha256': sha256(path)}

    # Archive/binary fingerprints identify the actual unchanged installation.
    # Headers are also retained; external system SDK/libc sources are not vendored.
    toolchain_files = [prefix/'bin/lean', prefix/'bin/leanc', prefix/'lib/lean/libleanrt.a']
    toolchain_files += sorted((prefix/'include/lean').glob('*.h'))
    external_inputs = {}
    for path in toolchain_files:
        relative = path.relative_to(prefix).as_posix()
        entry = {'path': str(path), 'sha256': sha256(path), 'bytes': path.stat().st_size}
        if path.suffix == '.h':
            target = out/'inputs/toolchain'/relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
            entry['snapshot'] = target.relative_to(out).as_posix()
        external_inputs[relative] = entry

    head = runner.run(['git', 'rev-parse', 'HEAD'], label='git-head')[0].strip()
    status = runner.run(['git', 'status', '--porcelain'], label='git-status')[0]
    runner.run(['git', 'diff', '--binary', 'HEAD'], label='git-tracked-diff')
    build = out/'build'
    build.mkdir()
    source = out/'inputs/repository/experiments/stock_allocation_capabilities'
    shutil.copyfile(source/'Main.lean', build/'Main.lean')
    env = dict(os.environ, LEAN_CC=cc, LEAN_NUM_THREADS='0')
    runner.run([lean, '-c', 'Main.c', 'Main.lean'], cwd=build, env=env, label='lean-emit')
    # LEAN_CC selects the host compiler. -L prefix/lib follows existing native
    # harnesses (in particular installed GMP/uv/SSL archives on Linux/macOS).
    flags = ['-O3', '-Wall', '-Wextra', '-Werror', '-I'+str(prefix/'include/lean')]
    runner.run([leanc, *flags, '-c', 'Main.c', '-o', 'Main.o'], cwd=build, env=env, label='main-compile')
    runner.run([leanc, *flags, '-c', source/'probe.c', '-o', 'probe.o'], cwd=build, env=env, label='probe-compile')
    binary = build/'capability-probe'
    runner.run([leanc, '-L'+str(prefix/'lib'), 'Main.o', 'probe.o', '-o', binary],
               cwd=build, env=env, label='link')
    runner.run(['nm', '-g', binary], label='binary-symbols')
    runner.run(['otool', '-L', binary] if platform.system() == 'Darwin' else ['ldd', binary], label='binary-linkage')
    (out/'runs').mkdir()
    runs = []
    for index in range(1, RUNS + 1):
        raw, stdout, stderr = runner.run([binary], cwd=out, env=env, label=f'probe-{index}')
        rows = stream_json(raw)
        parsed = f'runs/{index}.json'
        dump(out/parsed, rows)
        runs.append({'index': index, 'stdout': stdout, 'stderr': stderr, 'parsed': parsed,
                     'classification': classify(rows)})
    for relative, entry in source_inputs.items():
        entry['sha256_after'] = sha256(ROOT/relative)
        if entry['sha256_after'] != entry['sha256']:
            raise RuntimeError(f'source changed during calibration: {relative}')
    for entry in external_inputs.values():
        entry['sha256_after'] = sha256(Path(entry['path']))
        if entry['sha256_after'] != entry['sha256']:
            raise RuntimeError(f'installed toolchain changed during calibration: {entry["path"]}')
    files = {p.relative_to(out).as_posix(): {'sha256': sha256(p), 'bytes': p.stat().st_size}
             for p in sorted(out.rglob('*')) if p.is_file()}
    record = {
        'schema': 1, 'kind': 'stock-lean-allocation-capabilities',
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'repository': {'head': head, 'status': status, 'inputs': source_inputs},
        'toolchain': {'pin': PIN, 'prefix': str(prefix), 'version': version,
                      'inputs': external_inputs, 'mimalloc_stats_header_blob': blob},
        'host': {'system': platform.system(), 'platform': platform.platform(),
                 'machine': platform.machine(), 'cc': cc, 'cc_version': cc_version},
        'environment': {'LEAN_CC': cc, 'LEAN_NUM_THREADS': '0'},
        'claims': {'whole_process_accounting': False, 'between_snapshot_peak': False,
                   'timing': False, 'backend_hooks': False, 'production_rebuild': False},
        'commands': 'commands.json', 'runs': runs, 'files': files,
    }
    dump(out/'record.json', record)
    # This validator independently reconstructs classifications and coverage.
    from verify import verify
    verify(out)
    print(json.dumps({'record': str(out/'record.json'), 'runs': RUNS,
                      'classifications': [r['classification'] for r in runs]}, indent=2))


if __name__ == '__main__':
    main()
