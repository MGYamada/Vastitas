#!/usr/bin/env python3
"""Allocation-only experiment using the actual emitted two-edge tree program.

Never use elapsed fields from this instrumented run as performance evidence.
Hooks count FFI result/external allocations and direct emitted-C constructors,
not all allocations inside the Lean runtime or OpenBLAS.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import platform
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
TREE = ROOT / 'experiments/contraction_trees'
sys.path.insert(0, str(TREE))
import cases as fixtures
_spec = importlib.util.spec_from_file_location('tree_allocation_fixture', TREE / 'run.py')
tree = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(tree)

SHARED_HELPER = '''static lean_once_cell_t success_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object *unit_success;
static lean_object *initialize_success(void) {
    lean_object *result = lean_io_result_mk_ok(lean_box(0));
    lean_mark_persistent(result);
    return result;
}

/* Lean's once cell publishes the fully initialized immutable object. The pinned
 * Lean API prevents callers from resetting a persistent constructor in place;
 * generated finally blocks take their ordinary nonexclusive fallback instead.
 * One result remains live for the process lifetime, with no arena/error payload. */
LEAN_EXPORT lean_obj_res vastitas_io_unit_success(void) {
    lean_object *result = lean_obj_once(&unit_success, &success_once, initialize_success);
    lean_inc(result);
    return result;
}'''


def replace_once(text, before, after):
    if text.count(before) != 1:
        raise ValueError(f'unfamiliar instrumented input: {before}')
    return text.replace(before, after)


def unit_helper(text, variant, threaded=False):
    """Fail closed on the complete actual once/initializer/return envelope."""
    if variant not in ('production_shared', 'private_fresh'):
        raise ValueError('unsupported audit variant')
    if threaded and variant != 'production_shared':
        raise ValueError('thread audit must exercise the production helper')
    if variant == 'private_fresh':
        replacement = '''/* EXPERIMENT ONLY: fresh-result comparator. */
LEAN_EXPORT lean_obj_res vastitas_io_unit_success(void) {
    return lean_io_result_mk_ok(lean_box(0));
}'''
    elif threaded:
        replacement = replace_once(SHARED_HELPER,
            '    lean_mark_persistent(result);',
            '    lean_mark_persistent(result);\n    allocation_thread_initialize(result);')
    else:
        replacement = replace_once(SHARED_HELPER,
            '    lean_object *result = lean_io_result_mk_ok(lean_box(0));',
            '    lean_object *result = audit_shared_create();')
        replacement = replace_once(replacement,
            '    lean_inc(result);\n    return result;',
            '    lean_inc(result);\n    return audit_shared_return(result);')
    return replace_once(text, SHARED_HELPER, replacement)


def failure_wire(wire):
    raw = json.loads(wire)
    found = []
    def visit(value):
        if isinstance(value, dict):
            if value.get('op') == 'expect': found.append(value)
            for child in value.values(): visit(child)
        elif isinstance(value, list):
            for child in value: visit(child)
    visit(raw)
    if len(found) != 3: raise ValueError('expected three actual resource assertions')
    value = found[0]['value']
    key = 'real' if value['kind'] == 'complex_f64' else 'bits'
    value[key] ^= 1
    return raw


def wrapper(generated, failure):
    text = fixtures.driver(generated)
    _, arena, setup, operation, cleanup = fixtures.split_generated(failure)
    function = '@[noinline] def generatedFailure : IO Unit := do\n' + arena + '\n  try\n'
    function += '\n'.join(setup + operation + cleanup) + '\n    pure ()\n  finally\n    close arena\n\n'
    function = fixtures.cleanup_envelope.preserve(failure, function, expected=1)
    text = replace_once(text, 'def main (args : List String)',
        function + '@[extern "audit_mark_lean"] opaque auditMark (phase : UInt32) : IO Unit\n\ndef main (args : List String)')
    text = replace_once(text, '  generatedOnce\n', '  auditMark 1\n  generatedOnce\n  auditMark 2\n')
    return replace_once(text, '  if impl == "c" then', '''  if impl == "failure" then
    benchBegin 0 1 true
    let caught ← try
      generatedFailure
      pure false
    catch error =>
      if error.toString != "E_NATIVE_EXPECT: stored bit pattern differs" then throw error
      pure true
    if !caught then throw (IO.userError "expected injected native failure")
    benchStop
  else if impl == "c" then''')


def private_runtime(work, case, variant):
    tree.private_runtime(work, case)
    for name in ('audit.h', 'audit.c'):
        shutil.copyfile(HERE / name, work / 'native' / name)
    probe = (TREE / 'probe.c').read_text()
    probe = probe.replace('"../../lean-kernel/native/storage.c"', json.dumps(str(ROOT / 'lean-kernel/native/storage.c')))
    probe = probe.replace('"../../lean-kernel/numerical/gemm.h"', json.dumps(str(ROOT / 'lean-kernel/numerical/gemm.h')))
    probe = 'void audit_phase(unsigned);\n' + probe
    probe = replace_once(probe, 'static VStorageArena *active;',
        'void audit_arena_cycle(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);\nstatic VStorageArena *active;')
    probe = replace_once(probe, '    total.data_allocations += s.data_allocations;',
        '    audit_arena_cycle(s.data_allocations,s.data_frees,s.peak_bytes,s.written_bytes,s.copied_bytes,s.metadata_allocations,s.metadata_bytes);\n    total.data_allocations += s.data_allocations;')
    probe = replace_once(probe, '    scope = which; repetitions = reps;',
        '    audit_phase(3);\n    scope = which; repetitions = reps;')
    probe = replace_once(probe, 'void bench_stop(void) {', 'void bench_stop(void) {\n    audit_phase(4);')
    (work / 'native/storage.c').write_text(probe)
    native = (ROOT / 'lean-kernel/native/ffi.c').read_text()
    native = unit_helper(native, variant)
    native = replace_once(native, 'static void finalize(void *data) { vstorage_delete(data); }',
        'static void finalize(void *data) { audit_finalize(data); vstorage_delete(data); }')
    helpers = (TREE / 'ffi.c').read_text()
    helpers = replace_once(helpers, 'bench_report(); return lean_io_result_mk_ok(lean_box(0));',
        'bench_report(); audit_report(); return untracked_report_result();')
    native = '#include "audit.h"\n' + native + '\n#undef lean_io_result_mk_ok\n#define lean_io_result_mk_ok audit_control_ok\n' + helpers
    # Reporting's result is created after the observation window and deliberately untracked.
    native = '#include <lean/lean.h>\nstatic lean_obj_res untracked_report_result(void) { return lean_io_result_mk_ok(lean_box(0)); }\n' + native
    (work / 'native/ffi.c').write_text(native)
    numerical = (ROOT / 'lean-kernel/numerical/ffi.c').read_text()
    (work / 'numerical/ffi.c').write_text('#include "audit.h"\n' + numerical)
    lake = work / 'native/lakefile.lean'
    text = lake.read_text()
    target = '''input_file auditSource where path := "audit.c"
input_file auditHeader where path := "audit.h"
target auditObject pkg : FilePath := do
  let source ← auditSource.fetch
  let header ← auditHeader.fetch
  let source ← source.bindM fun path => header.mapM fun _ => pure path
  buildLeanO (pkg.buildDir / "audit.o") source #[] #["-std=c11", "-O3", "-fno-lto", "-Wall", "-Wextra", "-Werror", "-DAUDIT_PRODUCTION_SHARED=SHARED"]

'''.replace('SHARED"]', str(int(variant == 'production_shared')) + '"]')
    text = replace_once(text, 'extern_lib storageNative pkg := do', target + 'extern_lib storageNative pkg := do')
    text = replace_once(text, '← diagonalObject.fetch, ← ffiObject.fetch]', '← diagonalObject.fetch, ← ffiObject.fetch, ← auditObject.fetch]')
    lake.write_text(text)


def build(runner, case, work, prefix, frontend, kernel, cc, variant, *, link_prefix=None, runtime_hook=None,
          extra_link_args=()):
    # Public check/build/run always uses prefix. A separate diagnostic may
    # decorate only the private runtime and select its own linked backend.
    link_prefix = prefix if link_prefix is None else link_prefix
    work.mkdir(parents=True)
    package = work / 'package'
    fixtures.write_package(case, package)
    wire = tree.capture_wire(runner, frontend, package)
    env = dict(runner.env, VASTITAS_KERNEL=str(kernel), VASTITAS_KERNEL_ROOT=str(ROOT / 'lean-kernel'))
    runner.run([frontend, 'check', '--manifest-path', package / 'Vastitas.toml'], env=env, phase='public_check')
    canonical = work / 'canonical'
    runner.run([frontend, 'build', '--manifest-path', package / 'Vastitas.toml', '--openblas-prefix', prefix,
                '--native-cc', cc, '-o', canonical], env=env, phase='public_build')
    execution = runner.run([canonical], phase='public_execute')
    assert execution['stdout'].strip() == '0'
    response = json.loads(runner.run([kernel, 'emit'], input=wire, phase='kernel_emit')['stdout'])
    assert response['ok'] and response['version'] == 8 and response['numerical_runtime']
    tree.dump(work / 'response.json', response)
    invalid = failure_wire(wire)
    tree.dump(work / 'failure-wire.json', invalid)
    failure = json.loads(runner.run([kernel, 'emit'], input=json.dumps(invalid), phase='kernel_failure_emit')['stdout'])
    assert failure['ok'] and failure['version'] == 8
    tree.dump(work / 'failure-response.json', failure)
    (work / 'Generated.lean').write_text(response['lean_source'])
    (work / 'GeneratedFailure.lean').write_text(failure['lean_source'])
    (work / 'Main.lean').write_text(wrapper(response['lean_source'], failure['lean_source']))
    private_runtime(work, case, variant)
    if runtime_hook is not None:
        runtime_hook(work)
    (work / 'openblas_include').symlink_to(link_prefix / 'include', target_is_directory=True)
    shutil.copyfile(ROOT / 'lean-kernel/lean-toolchain', work / 'lean-toolchain')
    lean_root = runner.run(['lean', '--print-prefix'])['stdout'].strip()
    (work / 'lakefile.lean').write_text(f'''import Lake
open Lake DSL
package allocation_audit where
  moreLinkArgs := #[{', '.join(json.dumps(x) for x in ['-fno-lto', *extra_link_args, '-L', str(Path(lean_root) / 'lib')])}]
require vastitas_kernel from {json.dumps(str(ROOT / 'lean-kernel'))}
require vastitas_gemm_native from "./numerical" with
  NameMap.empty.insert `openblas {json.dumps(str(link_prefix))}
lean_exe audit where
  root := `Main
  moreLeancArgs := #["-O3", "-fno-lto", "-DAUDIT_GENERATED_MAIN=1", "-include", {json.dumps(str(work / 'native/audit.h'))}]
''')
    runner.run(['lake', 'build', 'audit'], cwd=work, env=dict(runner.env, LEAN_CC=cc), phase='audit_build')
    shutil.copyfile(work / '.lake/build/ir/Main.c', work / 'Emitted.c')
    return work / '.lake/build/bin/audit'


def validate(row, scope, reps, variant, impl, cleanup='finally'):
    assert cleanup in ('finally', 'unit-catch')
    persistent = variant == 'production_shared'
    assert row['schema'] == 2 and row['variant'] == variant and row['shared_result'] == persistent
    counts = row['phases']['run']['kinds']
    assert row['tracked_live_bytes'] == (16 if persistent else 0)
    if impl == 'generated':
        expected = (reps if persistent else 36*reps) if scope == 0 else (0 if persistent else 4*reps)
        assert counts['ffi_ok']['allocations'] == expected, (scope, reps, persistent, counts)
        assert counts['ffi_ok']['bytes'] == 16*expected
        assert counts['arena_external']['allocations'] == (reps if scope == 0 else 0)
        assert counts['arena_external']['bytes'] == (24*reps if scope == 0 else 0)
        # The range object and terminal loop result are per batch. Only the
        # legacy finally envelope rebuilds a shared cleanup's Unit result.
        assert counts['generated_ctor']['allocations'] == 2 + (reps if scope == 0 and persistent and cleanup == 'finally' else 0)
    else:
        assert all(counts[k]['allocations'] == 0 for k in ('ffi_ok','arena_external','generated_ctor'))
    assert row['phases']['cold']['kinds']['ffi_ok']['allocations'] == (1 if persistent else 36)
    assert row['phases']['cold']['kinds']['persistent_unit']['allocations'] == int(persistent)
    assert row['phases']['cold']['kinds']['persistent_unit']['retained_returns'] == (35 if persistent else 0)
    if impl == 'generated':
        assert counts['persistent_unit']['retained_returns'] == ((35*reps if scope == 0 else 4*reps) if persistent else 0)
    assert row['phases']['cold']['kinds']['arena_external']['allocations'] == 1
    assert row['phases']['cold']['closed_arena_cycles'] == 1
    assert row['phases']['cold']['arena_allocations'] == row['phases']['cold']['arena_frees'] == 6
    assert row['phases']['cold']['arena_metadata_allocations'] == 2
    end = row['phases']['run' if scope == 0 else 'cleanup']
    assert end['closed_arena_cycles'] == (reps if scope == 0 else 1)
    assert end['arena_allocations'] == end['arena_frees'] == 6*end['closed_arena_cycles']


def thread_test(runner, out, cc):
    work = out / 'production-thread-test'
    work.mkdir()
    shutil.copytree(ROOT / 'lean-kernel/native', work / 'native', ignore=shutil.ignore_patterns('.lake'))
    source = (work / 'native/ffi.c').read_text()
    source = '#include <lean/lean.h>\nvoid allocation_thread_initialize(lean_object *);\n' + unit_helper(source, 'production_shared', threaded=True)
    (work / 'native/ffi.c').write_text(source)
    shutil.copyfile(HERE / 'production_thread.c', work / 'production_thread.c')
    shutil.copyfile(ROOT / 'lean-kernel/lean-toolchain', work / 'lean-toolchain')
    lean_root = Path(runner.run(['lean', '--print-prefix'])['stdout'].strip())
    (work / 'Main.lean').write_text('''import VastitasStorageNative
@[extern "allocation_test_unit"] opaque sharedUnit : IO Unit
@[extern "allocation_test_gate"] opaque gate : IO Unit
@[extern "allocation_test_error"] opaque expectedError : IO Unit
@[extern "allocation_test_validate"] opaque validate (expected : UInt32) : IO Unit
def main : IO Unit := do
  let tasks ← (List.range 8).mapM fun _ => IO.asTask (do
    gate
    for _ in [:1000] do sharedUnit) Task.Priority.dedicated
  for task in tasks do
    match task.get with
    | .ok _ => pure ()
    | .error error => throw error
  let caught ← try
    try expectedError finally sharedUnit
    pure false
  catch error =>
    if error.toString != "E_NATIVE_HANDLE: allocation is absent, closed or already issued" then throw error
    pure true
  if !caught then throw (IO.userError "expected error was lost")
  validate 8001
''')
    (work / 'lakefile.lean').write_text(f'''import Lake
open Lake DSL System
package production_thread_test where
  moreLinkArgs := #["-fno-lto", "-L", {json.dumps(str(lean_root / 'lib'))}]
require vastitas_storage_native from "./native"
input_file threadSource where path := "production_thread.c"
target threadObject pkg : FilePath := do
  let source ← threadSource.fetch
  buildLeanO (pkg.buildDir / "thread.o") source #[] #["-std=c11", "-O3", "-fno-lto", "-Wall", "-Wextra", "-Werror", {json.dumps('-I' + str(work / 'native'))}]
extern_lib threadNative pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "thread_native") #[← threadObject.fetch]
lean_exe test where
  root := `Main
''')
    runner.run(['lake', 'build', 'test'], cwd=work, env=dict(runner.env, LEAN_CC=cc), phase='production_thread_build')
    shutil.copyfile(work / '.lake/build/ir/Main.c', work / 'Emitted.c')
    for _ in range(4):
        result = runner.run([work / '.lake/build/bin/test'], phase='production_thread_test')
        assert json.loads(result['stdout']) == {'production_thread_test':'passed','workers':8,'initializations':1,'calls':8001,
                                               'fresh_arena_results':2,'fresh_stats_results':2,'fresh_errors':2}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--prefix', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--frontend', type=Path, default=ROOT / 'target/debug/vastitas')
    p.add_argument('--kernel', type=Path, default=ROOT / 'lean-kernel/.lake/build/bin/vastitas-kernel')
    p.add_argument('--cc', default='cc')
    p.add_argument('--full', action='store_true')
    p.add_argument('--one-case', action='store_true')
    args = p.parse_args()
    out, prefix = args.output.resolve(), args.prefix.resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1')
    runner = tree.Runner(out, env)
    selected = fixtures.cases(not args.full)
    if args.one_case: selected = selected[:1]
    rows = []
    tree.dump(out / 'cases.json', selected)
    head = runner.run(['git', 'rev-parse', 'HEAD'])['stdout'].strip()
    inputs = {}
    for directory in (HERE, TREE, ROOT / 'lean-kernel/native', ROOT / 'lean-kernel/numerical'):
        for path in directory.rglob('*'):
            if path.is_file() and not any(part in ('.lake', '__pycache__', 'results') for part in path.relative_to(directory).parts):
                relative = path.relative_to(ROOT)
                target = out / 'source' / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, target)
                inputs[str(path)] = tree.sha(path)
    for relative in ('experiments/native_cleanup.py', 'lean-kernel/VastitasKernel/StorageCodegen.lean',
                     'lean-kernel/VastitasKernel/ResourceCodegen.lean'):
        path = ROOT / relative
        target = out / 'source' / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        inputs[str(path)] = tree.sha(path)
    lean_root = Path(runner.run(['lean', '--print-prefix'])['stdout'].strip())
    for name in ('lean.h', 'config.h'):
        path = lean_root / 'include/lean' / name
        shutil.copyfile(path, out / ('pinned-' + name))
        inputs[str(path)] = tree.sha(path)
    for path in (args.frontend.resolve(), args.kernel.resolve(), prefix / 'lib/libopenblas.a'):
        inputs[str(path)] = tree.sha(path)
    shutil.copyfile(prefix / 'vastitas-openblas.json', out / 'openblas-build.json')
    environment = {'schema': 2, 'variants': ['production_shared','private_fresh'], 'checkout_root': str(ROOT),
        'selection': 'debug-one' if args.one_case else 'full' if args.full else 'smoke',
        'head': head, 'git_status': runner.run(['git', 'status', '--short'])['stdout'],
        'argv': sys.argv, 'platform': platform.platform(), 'timing': 'not performance evidence',
        'coverage': 'instrumented FFI IO/external and direct emitted-C constructors; process startup, general Lean/internal allocator and BLAS workspace excluded',
        'inputs': inputs}
    tree.dump(out / 'environment.json', environment)
    thread_test(runner, out, args.cc)
    for case in selected:
        for variant in ('production_shared', 'private_fresh'):
            persistent = variant == 'production_shared'
            work = out / case['case'] / variant
            exe = build(runner, case, work, prefix, args.frontend.resolve(), args.kernel.resolve(), args.cc, variant)
            cleanup, _ = fixtures.cleanup_envelope.split((work / 'Generated.lean').read_text().splitlines(), 'arena')
            failed = runner.run([exe, 'failure', 0, 1, 1], phase='failure_cleanup')
            failure_cost, failure_audit = map(json.loads, failed['stdout'].splitlines())
            assert failure_cost['data_allocations'] == failure_cost['data_frees'] == 6
            assert failure_cost['live_bytes_after'] == 0
            assert failure_audit['phases']['run']['kinds']['ffi_error']['allocations'] == 1
            assert failure_audit['phases']['run']['arena_finalizers'] == 1
            assert failure_audit['tracked_live_bytes'] == (16 if persistent else 0)
            for scope in (0, 1):
                for reps in (1, 2, 17):
                    pair = []
                    for impl in ('generated', 'c'):
                        result = runner.run([exe, impl, scope, reps, 1], phase='allocation_audit')
                        outputs = [json.loads(line) for line in result['stdout'].splitlines()]
                        assert len(outputs) == 2
                        costs, audit = outputs
                        validate(audit, scope, reps, variant, impl, cleanup)
                        pair.append(costs)
                        rows.append(dict(case=case['case'], variant=variant, scope=scope, repetitions=reps,
                                         implementation=impl, costs=costs, audit=audit))
                        tree.dump(out / 'allocations.json', rows)
                    tree.compare_pair(*pair)
    tree.verify_inputs(inputs)
    environment['recorded_inputs_unchanged'] = True
    tree.dump(out / 'environment.json', environment)
    tree.dump(out / 'status.json', {'schema': 2, 'status': 'passed', 'rows': len(rows), 'performance': 'not measured'})
    print(json.dumps({'status':'passed','rows':len(rows),'output':str(out)}))


if __name__ == '__main__': main()
