#!/usr/bin/env python3
"""Calibrate a private one-object Lean runtime rebuild; never time operations."""
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
import tempfile

import verify

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
URL = 'https://github.com/microsoft/mimalloc/archive/v3.4.5.tar.gz'


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


class Runner:
    def __init__(self, out):
        self.out, self.commands = out, []
        (out / 'logs').mkdir()

    def run(self, argv, label, *, cwd=ROOT, env=None, overrides=None):
        argv = list(map(str, argv))
        result = subprocess.run(argv, cwd=cwd, env=env, text=True, capture_output=True)
        index = len(self.commands)
        stdout, stderr = (f'logs/{index:02d}-{label}.{suffix}' for suffix in ('stdout', 'stderr'))
        (self.out / stdout).write_text(result.stdout)
        (self.out / stderr).write_text(result.stderr)
        self.commands.append(dict(argv=argv, label=label, cwd=str(cwd), returncode=result.returncode,
                                  stdout=stdout, stderr=stderr, environment=overrides or {}))
        dump(self.out / 'commands.json', self.commands)
        if result.returncode:
            raise RuntimeError(f'{label} failed ({result.returncode}); see {self.out / stderr}')
        return result.stdout, stdout, stderr


def extract(archive, destination):
    if sha(archive) != verify.ARCHIVE_SHA:
        raise ValueError('mimalloc archive checksum differs from the pinned v3.4.5 release')
    with tarfile.open(archive) as tar:
        members = tar.getmembers()
        names = set()
        for item in members:
            p = PurePosixPath(item.name)
            if (not p.parts or p.parts[0] != 'mimalloc-3.4.5' or p.is_absolute() or
                    '..' in p.parts or not (item.isfile() or item.isdir()) or item.name in names):
                raise ValueError('unexpected mimalloc archive member')
            names.add(item.name)
        # Members are checksum pinned, confined regular files/directories; no
        # symlink, hardlink, device, permission or owner restoration is needed.
        for item in members:
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
    parser.add_argument('--cc', default='cc', help='compiler executable, not shell text')
    parser.add_argument('--cxx', default='clang++', help='C++20 compiler executable; Linux uses libc++')
    args = parser.parse_args()
    out = args.out.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError('output must be outside the source checkout')
    out.mkdir(parents=True, exist_ok=False)
    system = platform.system()
    if system not in ('Darwin', 'Linux'):
        raise ValueError('this calibration supports only 64-bit macOS/Linux')
    cc, cxx, ar = (shutil.which(x) for x in (args.cc, args.cxx, 'ar'))
    if not all((cc, cxx, ar)):
        raise ValueError('C, C++ and ar executables are required')
    cc, cxx, ar = (str(Path(x).resolve()) for x in (cc, cxx, ar))
    runner = Runner(out)
    if [(ROOT / p).read_text().strip() for p in ('lean-toolchain', 'lean-kernel/lean-toolchain')] != [verify.PIN] * 2:
        raise ValueError('revalidate the allocator source/API for a changed Lean pin')
    prefix = Path(runner.run(['lean', '--print-prefix'], 'lean-prefix', cwd=ROOT / 'lean-kernel')[0].strip()).resolve()
    lean, leanc = prefix / 'bin/lean', prefix / 'bin/leanc'
    version = runner.run([lean, '--version'], 'lean-version')[0].strip()
    if 'version 4.35.0' not in version:
        raise ValueError('installed Lean does not match the pinned release')
    cc_version = runner.run([cc, '--version'], 'cc-version')[0].strip()
    cxx_version = runner.run([cxx, '--version'], 'cxx-version')[0].strip()
    head = runner.run(['git', 'rev-parse', 'HEAD'], 'git-head')[0].strip()
    status = runner.run(['git', 'status', '--porcelain'], 'git-status')[0]
    runner.run(['git', 'diff', '--binary', 'HEAD'], 'git-diff')

    sources = sorted(p for p in HERE.rglob('*') if p.is_file() and
                     not {'results', '__pycache__'}.intersection(p.relative_to(HERE).parts) and p.suffix != '.pyc')
    sources += [ROOT / p for p in ('lean-toolchain', 'lean-kernel/lean-toolchain')]
    sources += [HERE.parent / 'stock_allocation_capabilities' / p for p in
                ('verify.py', 'vendor/mimalloc-stats.h', 'vendor/LICENSE.mimalloc')]
    inputs = {}
    for path in sources:
        name = path.relative_to(ROOT).as_posix()
        dest = out / 'inputs/repository' / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, dest)
        inputs[name] = dict(snapshot=dest.relative_to(out).as_posix(), sha256=sha(path))
    for name, blob in verify.LEAN_BLOBS.items():
        data = (HERE / 'vendor/lean' / name).read_bytes()
        if hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() != blob:
            raise ValueError('vendored Lean allocator source differs from its upstream blob')
    external = {}
    toolchain_files = [lean, leanc] + sorted((prefix / 'include/lean').glob('*.h'))
    # Fingerprint the actual static libraries selected by leanc as well as the
    # runtime archive. Other toolchain libraries are external, not vendored.
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

    overrides = dict(LEAN_CC=cc, LEAN_NUM_THREADS='0')
    env = {k: v for k, v in os.environ.items() if not k.startswith('MIMALLOC_')}
    if any(env.get(k) for k in ('LD_PRELOAD', 'DYLD_INSERT_LIBRARIES')):
        raise ValueError('allocator calibration requires no preload interposition')
    env.update(overrides)
    build = out / 'build'
    build.mkdir()
    source = out / 'inputs/repository/experiments/lean_allocation_diagnostic'
    shutil.copyfile(source / 'Main.lean', build / 'Main.lean')
    runner.run([lean, '-c', 'Main.c', 'Main.lean'], 'lean-emit', cwd=build, env=env, overrides=overrides)
    cflags = ['-O3', '-Wall', '-Wextra', '-Werror', '-I' + str(prefix / 'include/lean')]
    for name, input_path in (('main', build / 'Main.c'), ('probe', source / 'probe.c')):
        runner.run([leanc, *cflags, '-c', input_path, '-o', build / (name + '.o')], name + '-compile',
                   env=env, overrides=overrides)
    archives, runs = {}, []
    (out / 'runs').mkdir()
    stock = out / 'inputs/toolchain/lib/lean/libleanrt.a'
    with tempfile.TemporaryDirectory(prefix='vastitas-mimalloc-source-') as temporary:
        mimalloc = extract(archive, Path(temporary))
        if (mimalloc / 'include/mimalloc.h').read_bytes() != (prefix / 'include/lean/mimalloc.h').read_bytes():
            raise ValueError('installed mimalloc public header differs from the pinned source')
        flags = ['-std=c++20', '-O3', '-DNDEBUG', '-DMI_SHARED_LIB', '-DMI_SHARED_LIB_EXPORT',
                 '-DMI_WIN_NOREDIRECT', '-DMI_MAX_ALIGN_SIZE=8', '-DMI_SECURE=0', '-DLEAN_EXPORTING',
                 '-fPIC', '-fvisibility=hidden', '-fvisibility-inlines-hidden', '-ftls-model=local-exec',
                 '-Wno-unused-function', '-Wno-deprecated']
        if system == 'Linux':
            flags += ['-stdlib=libc++']
        flags += ['-I' + str(p) for p in (prefix / 'include', source / 'vendor/lean',
                                         mimalloc / 'include', mimalloc / 'src')]
        for variant in verify.VARIANTS:
            directory = build / variant
            directory.mkdir()
            runtime = directory / 'libleanrt.a'
            shutil.copyfile(stock, runtime)
            if variant != 'stock':
                level = 0 if variant == 'rebuilt0' else 2
                obj = directory / 'mimalloc.cpp.o'
                runner.run([cxx, *flags, f'-DMI_STAT={level}', '-c', source / 'vendor/lean/runtime/mimalloc.cpp', '-o', obj],
                           variant + '-compile', env=env, overrides=overrides)
                runner.run([ar, 'r', runtime, obj], variant + '-archive')
                members = verify.audit_replacement(stock.read_bytes(), runtime.read_bytes(), obj.read_bytes())
            else:
                members = {n: verify.digest(b) for n, b in verify.ar_objects(runtime.read_bytes()).items()}
            archives[variant] = dict(path=runtime.relative_to(out).as_posix(), members=members)
            map_flag = '-Wl,-map,' if system == 'Darwin' else '-Wl,-Map,'
            runner.run([leanc, '-v', '-L' + str(directory), '-L' + str(prefix / 'lib'),
                        build / 'main.o', build / 'probe.o', map_flag + str(directory / 'link.map'),
                        '-o', directory / 'probe'], variant + '-link', env=env, overrides=overrides)
            runner.run(['nm', '-g', directory / 'probe'], variant + '-symbols')
            runner.run(['otool', '-L', directory / 'probe'] if system == 'Darwin' else ['ldd', directory / 'probe'],
                       variant + '-linkage')
            for index in range(1, 4):
                raw, stdout, stderr = runner.run([directory / 'probe'], f'{variant}-run-{index}',
                                                cwd=out, env=env, overrides=overrides)
                rows = verify.base.stream(raw)
                parsed = f'runs/{variant}-{index}.json'
                dump(out / parsed, rows)
                runs.append(dict(variant=variant, index=index, stdout=stdout, stderr=stderr, parsed=parsed,
                                 calibration=verify.observation(rows, variant)))
    for name, item in inputs.items():
        item['sha256_after'] = sha(ROOT / name)
        if item['sha256'] != item['sha256_after']:
            raise ValueError('repository changed during calibration: ' + name)
    for item in external.values():
        item['sha256_after'] = sha(Path(item['path']))
        if item['sha256'] != item['sha256_after']:
            raise ValueError('installed toolchain changed during calibration')
    files = {p.relative_to(out).as_posix(): dict(sha256=sha(p), bytes=p.stat().st_size)
             for p in sorted(out.rglob('*')) if p.is_file()}
    record = dict(schema=1, kind='lean-allocation-diagnostic', created_utc=datetime.now(timezone.utc).isoformat(),
                  output_path=str(out), repository=dict(head=head, status=status, inputs=inputs),
                  toolchain=dict(pin=verify.PIN, prefix=str(prefix), version=version, inputs=external),
                  host=dict(system=system, platform=platform.platform(), machine=platform.machine(),
                            cc=cc, cxx=cxx, cc_version=cc_version, cxx_version=cxx_version, ar=ar),
                  environment=overrides, claims=verify.CLAIMS, archives=archives, runs=runs, files=files)
    dump(out / 'record.json', record)
    print(json.dumps(verify.verify(out), indent=2))


if __name__ == '__main__':
    main()
