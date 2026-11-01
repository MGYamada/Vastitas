#!/usr/bin/env python3
"""Calibrate the pinned private lifetime observer; never time operations."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import shutil
import subprocess
import tarfile

import instrument
import observation
import profile
import render
import verify

HERE, ROOT = profile.HERE, profile.ROOT
calibration = observation.calibration
URL = 'https://github.com/microsoft/mimalloc/archive/v3.4.5.tar.gz'


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


class Runner:
    def __init__(self, out, env, overrides):
        self.out, self.env, self.overrides = out, env, overrides
        self.commands = []
        (out / 'logs').mkdir()

    def run(self, argv, label, *, cwd=ROOT, expected=0, sanitized=False):
        overrides = dict(self.overrides)
        if sanitized:
            overrides.update(verify.SANITIZER_ENV)
        env = dict(self.env, **overrides)
        result = subprocess.run(list(map(str, argv)), cwd=cwd, env=env, capture_output=True)
        index = len(self.commands)
        stdout, stderr = (f'logs/{index:02d}-{label}.{suffix}' for suffix in ('stdout', 'stderr'))
        (self.out / stdout).write_bytes(result.stdout)
        (self.out / stderr).write_bytes(result.stderr)
        self.commands.append(dict(argv=list(map(str, argv)), label=label, cwd=str(cwd),
            returncode=result.returncode, stdout=stdout, stderr=stderr, environment=overrides))
        dump(self.out / 'commands.json', self.commands)
        print(label, result.returncode, flush=True)
        if result.returncode != expected:
            raise RuntimeError(f'{label} returned {result.returncode}, expected {expected}; see {self.out / stderr}')
        return result.stdout, stdout, stderr


def extract(archive, destination):
    if sha(archive) != calibration.ARCHIVE_SHA:
        raise ValueError('mimalloc archive checksum differs from the pinned v3.4.5 release')
    with tarfile.open(archive) as tar:
        names = set()
        for item in tar.getmembers():
            path = PurePosixPath(item.name)
            if (not path.parts or path.parts[0] != 'mimalloc-3.4.5' or path.is_absolute() or
                    '..' in path.parts or not (item.isfile() or item.isdir()) or item.name in names):
                raise ValueError('unexpected mimalloc archive member')
            names.add(item.name)
            target = destination / item.name
            if item.isdir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile(item) as source, target.open('xb') as output:
                    shutil.copyfileobj(source, output)
    return destination / 'mimalloc-3.4.5'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--mimalloc-archive', type=Path)
    parser.add_argument('--cc', default='cc', help='C compiler executable, not shell text')
    parser.add_argument('--cxx', default='clang++', help='C++20 compiler; Linux uses libc++')
    args = parser.parse_args()
    out = args.out.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError('output must be outside the source checkout')
    out.mkdir(parents=True, exist_ok=False)
    system = platform.system()
    if system not in ('Darwin', 'Linux') or platform.architecture()[0] != '64bit':
        raise ValueError('lifetime calibration supports only 64-bit macOS/Linux')
    executables = [shutil.which(x) for x in (args.cc, args.cxx, 'ar')]
    if not all(executables):
        raise ValueError('C, C++ and ar executables are required')
    # Preserve the invoked basename: clang++ may be a symlink to clang, whose
    # C driver does not add the C++ ABI libraries when linking this fixture.
    cc, cxx, ar = [str(Path(x).absolute()) for x in executables]
    overrides = dict(LEAN_CC=cc, LEAN_NUM_THREADS='0', LEAN_MAIN_USE_THREAD='1')
    # No inherited allocator, sanitizer, loader or compiler-injection options.
    if any(os.environ.get(k) for k in verify.FORBIDDEN_ENV):
        raise ValueError('remove loader/compiler injection environment options before calibration')
    removed = sorted(k for k in os.environ if k.startswith('MIMALLOC_') or
                     k in ('ASAN_OPTIONS', 'UBSAN_OPTIONS', 'LSAN_OPTIONS'))
    env = {k: v for k, v in os.environ.items() if k not in removed}
    runner = Runner(out, env, overrides)
    if [(ROOT / p).read_text().strip() for p in ('lean-toolchain', 'lean-kernel/lean-toolchain')] != [calibration.PIN] * 2:
        raise ValueError('revalidate allocator hooks for a changed Lean pin')
    prefix = Path(runner.run(['lean', '--print-prefix'], 'lean-prefix', cwd=ROOT / 'lean-kernel')[0].decode().strip()).resolve()
    version = runner.run([prefix / 'bin/lean', '--version'], 'lean-version')[0].decode().strip()
    if 'version 4.35.0' not in version:
        raise ValueError('installed Lean does not match the pinned release')
    cc_version = runner.run([cc, '--version'], 'cc-version')[0].decode().strip()
    cxx_version = runner.run([cxx, '--version'], 'cxx-version')[0].decode().strip()
    head = runner.run(['git', 'rev-parse', 'HEAD'], 'git-head')[0].decode().strip()
    status = runner.run(['git', 'status', '--porcelain'], 'git-status')[0].decode()
    runner.run(['git', 'diff', '--binary', 'HEAD'], 'git-diff')
    inputs, external = {}, {}
    for name in profile.REPOSITORY:
        path, dest = ROOT / name, out / 'inputs/repository' / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, dest)
        inputs[name] = dict(snapshot=dest.relative_to(out).as_posix(), sha256=sha(path))
    toolchain_files = [prefix / 'bin/lean', prefix / 'bin/leanc']
    toolchain_files += sorted((prefix / 'include/lean').glob('*.h'))
    toolchain_files += sorted((prefix / 'lib/lean').glob('*.a')) + sorted((prefix / 'lib').glob('*.a'))
    for path in toolchain_files:
        name = path.relative_to(prefix).as_posix()
        item = dict(path=str(path), sha256=sha(path), bytes=path.stat().st_size)
        if path.suffix == '.h' or name == 'lib/lean/libleanrt.a':
            dest = out / 'inputs/toolchain' / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, dest)
            item['snapshot'] = dest.relative_to(out).as_posix()
        external[name] = item
    archive = out / 'inputs/mimalloc-v3.4.5.tar.gz'
    if args.mimalloc_archive:
        shutil.copyfile(args.mimalloc_archive.resolve(), archive)
    else:
        runner.run(['curl', '--fail', '--location', '--silent', '--show-error', URL, '-o', archive], 'download-mimalloc')
    build = out / 'build'
    build.mkdir()
    allocator = extract(archive, build)
    if (allocator / 'include/mimalloc.h').read_bytes() != (prefix / 'include/lean/mimalloc.h').read_bytes():
        raise ValueError('installed mimalloc header differs from the pinned source')
    dump(out / 'patches.json', instrument.apply(allocator))
    original = out / 'inputs/repository/experiments/lean_allocation_diagnostic'
    shutil.copyfile(original / 'Main.lean', build / 'Main.lean')
    (build / 'probe.c').write_text(render.lean_probe((original / 'probe.c').read_text()))
    (build / 'runtime').mkdir()
    stock = out / 'inputs/toolchain/lib/lean/libleanrt.a'
    runtime = build / 'runtime/libleanrt.a'
    shutil.copyfile(stock, runtime)
    host = dict(system=system, platform=platform.platform(), machine=platform.machine(),
                cc=cc, cxx=cxx, ar=ar, cc_version=cc_version, cxx_version=cxx_version)
    for label, argv in profile.commands(str(out), str(prefix), host).items():
        runner.run(argv, label, cwd=build)
    members = calibration.audit_replacement(stock.read_bytes(), runtime.read_bytes(),
                                            (build / 'runtime/mimalloc.cpp.o').read_bytes())
    runner.run(['nm', '-g', build / 'lean-probe'], 'lean-symbols', cwd=build)
    runner.run(['otool', '-L', build / 'lean-probe'] if system == 'Darwin' else
               ['ldd', build / 'lean-probe'], 'lean-linkage', cwd=build)
    runs = []
    (out / 'runs').mkdir()
    for variant, indices in (('lean', range(1, 4)), ('native', range(1, 4)), ('sanitized', (1,))):
        for index in indices:
            raw, stdout, stderr = runner.run([build / (variant + '-probe')], f'{variant}-run-{index}',
                cwd=out, sanitized=variant == 'sanitized')
            rows = calibration.base.stream(raw)
            parsed = f'runs/{variant}-{index}.json'
            dump(out / parsed, rows)
            summary = observation.lean(rows) if variant == 'lean' else observation.native(rows)
            runs.append(dict(variant=variant, index=index, stdout=stdout, stderr=stderr,
                             parsed=parsed, calibration=summary))
    for variant in ('native', 'sanitized'):
        runner.run([build / (variant + '-probe'), 'capacity'], variant + '-capacity',
                   cwd=out, expected=90, sanitized=variant == 'sanitized')
    for name, item in inputs.items():
        item['sha256_after'] = sha(ROOT / name)
        if item['sha256_after'] != item['sha256']:
            raise ValueError('repository input changed during calibration: ' + name)
    for item in external.values():
        item['sha256_after'] = sha(Path(item['path']))
        if item['sha256_after'] != item['sha256']:
            raise ValueError('toolchain changed during calibration')
    files = {p.relative_to(out).as_posix(): dict(sha256=sha(p), bytes=p.stat().st_size)
             for p in sorted(out.rglob('*')) if p.is_file()}
    record = dict(schema=1, kind='lean-allocation-lifetimes', created_utc=datetime.now(timezone.utc).isoformat(),
        output_path=str(out), repository=dict(head=head, status=status, inputs=inputs),
        toolchain=dict(pin=calibration.PIN, prefix=str(prefix), version=version, inputs=external),
        host=host, environment=overrides, removed_environment=removed, claims=profile.CLAIMS,
        runtime=dict(path='build/runtime/libleanrt.a', members=members), runs=runs, files=files)
    dump(out / 'record.json', record)
    print(json.dumps(verify.verify(out), indent=2))


if __name__ == '__main__':
    main()
