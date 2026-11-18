#!/usr/bin/env python3
"""Check numerical experiment wrappers against today's public compiler output.

This is a correctness regression for #880, not a timing or release gate. The
fixtures currently use F64<RR> and F64<CC>; binary32 admission is separate.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import tempfile

from check_resource_cleanup import Runner, capture_wire
from kernel_protocol import CURRENT_PROTOCOL

ROOT = Path(__file__).resolve().parents[1]
FAMILIES = ('public_gemm', 'tensor_packing', 'contraction_trees', 'runtime_shapes')


def fixtures(name):
    spec = importlib.util.spec_from_file_location(
        'entry_' + name, ROOT / 'experiments' / name / 'cases.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_case(runner, frontend, kernel, module, package, prefix, cc):
    manifest = package / 'Vastitas.toml'
    wire = capture_wire(runner, frontend, package)
    runner.run([frontend, 'check', '--manifest-path', manifest])
    result = runner.run([kernel, 'emit'], input=wire)
    response = json.loads(result['stdout'])
    if (response.get('version') != CURRENT_PROTOCOL or response.get('ok') is not True or
            response.get('storage_runtime') is not True or response.get('numerical_runtime') is not True):
        raise ValueError('expected checked numerical emission')
    generated = response['lean_source']
    if 'def main : IO UInt32 := do\n' not in generated:
        raise ValueError('expected the current public exit-status contract')
    module.split_generated(generated)
    wrapped = module.driver(generated)
    if 'pure status' in wrapped or wrapped.count('throw cleanupError') != 2:
        raise ValueError('wrapper lost the two generated cleanup scopes')
    if prefix is not None:
        executable = package / 'program'
        command = [frontend, 'build', '--manifest-path', manifest,
                   '--openblas-prefix', prefix, '-o', executable]
        if cc is not None:
            command += ['--native-cc', cc]
        runner.run(command)
        module.cleanup_envelope.require_success(runner.run([executable]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--frontend', type=Path, default=ROOT / 'target/debug/vastitas')
    parser.add_argument('--prefix', type=Path,
                        help='also build/run every fixture with pinned OpenBLAS 0.3.34')
    parser.add_argument('--cc', help='optional numerical native compiler executable')
    args = parser.parse_args()
    if args.cc is not None and args.prefix is None:
        parser.error('--cc requires --prefix')
    frontend = args.frontend.resolve()
    kernel = ROOT / 'lean-kernel/.lake/build/bin/vastitas-kernel'
    prefix = args.prefix.resolve() if args.prefix is not None else None
    if not frontend.is_file() or not kernel.is_file():
        parser.error('build the standalone kernel and Rust compiler first')
    runner = Runner(dict(os.environ, VASTITAS_KERNEL=str(kernel),
                         VASTITAS_KERNEL_ROOT=str(ROOT / 'lean-kernel'),
                         OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1', GOTO_NUM_THREADS='1'))
    total = 0
    with tempfile.TemporaryDirectory(prefix='vastitas-harness-entry-') as directory:
        for family in FAMILIES:
            module = fixtures(family)
            cases = ([(scalar, transpose) for scalar in (0, 1) for transpose in (0, 1)]
                     if family == 'runtime_shapes' else module.cases(smoke=True))
            for index, case in enumerate(cases):
                package = Path(directory) / family / str(index)
                if family == 'runtime_shapes':
                    module.write_package(package, *case)
                else:
                    module.write_package(case, package)
                check_case(runner, frontend, kernel, module, package, prefix, args.cc)
                total += 1
            print(f'{family}: {len(cases)} current emitted entries and wrappers passed', flush=True)
    print(f'{total} checked harness fixtures; native execution: '
          + ('passed' if prefix is not None else 'not run') + '; performance: not measured')


if __name__ == '__main__':
    main()
