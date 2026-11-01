#!/usr/bin/env python3
"""Join checked source, selected Lean object costs and exact backend event spans."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import shlex
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def module(name,path):
    spec = importlib.util.spec_from_file_location(name,path)
    loaded = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(loaded)
    return loaded


audit = module('source_workspace_allocation',ROOT/'experiments/allocation_audit/run.py')
backend_verify = module('source_workspace_backend_verify',ROOT/'experiments/openblas_workspace/verify.py')
tree,fixtures = audit.tree,audit.fixtures


class Runner(tree.Runner):
    """Bind stdin-only kernel commands to the case that actually ran them."""
    context = None

    def run(self,args,**kwargs):
        required = kwargs.pop('required',True)
        environment = dict(kwargs.get('env') or self.env)
        # Lake needs its task manager; only the executed observations disable
        # Lean workers. Neither setting changes sequential BLAS configuration.
        if kwargs.get('phase') in ('source_workspace','public_execute'):
            environment['LEAN_NUM_THREADS'] = '0'
        kwargs['env'] = environment
        entry = super().run(args,required=False,**kwargs)
        entry['context'] = self.context
        if kwargs.get('input') is not None:
            data = kwargs['input'].encode()
            entry['stdin'] = {'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
        entry['compiler_environment'] = {key:environment[key] for key in
            ('LEAN_CC','LEAN_NUM_THREADS','VASTITAS_KERNEL','VASTITAS_KERNEL_ROOT') if key in environment}
        tree.dump(self.out/'commands.json',self.commands)
        if required and entry['returncode']:
            raise RuntimeError(shlex.join(entry['command'])+'\n'+entry['stderr']+'\n'+entry['stdout'])
        return entry

CLOCK = '''static uint64_t now_ns(void) {
    struct timespec t;
#if defined(__APPLE__) || defined(CLOCK_MONOTONIC_RAW)
    require(clock_gettime(CLOCK_MONOTONIC_RAW, &t) == 0);
#else
    require(clock_gettime(CLOCK_MONOTONIC, &t) == 0);
#endif
    return (uint64_t)t.tv_sec * UINT64_C(1000000000) + (uint64_t)t.tv_nsec;
}'''


def decorate(work,backend):
    """Strict additions to a private runtime; ordinary source/runtime unchanged."""
    native = work/'native'
    for name in ('bridge.c','bridge.h'):
        shutil.copyfile(HERE/name,native/name)
    shutil.copyfile(ROOT/'experiments/openblas_workspace/observer.h',native/'observer.h')
    path = native/'audit.c'
    text = '#include "bridge.h"\n'+path.read_text()
    text = audit.replace_once(text,'require(next < PHASES); phase = next;',
                              'require(next < PHASES); phase = next; source_workspace_mark(next);')
    path.write_text(text)
    path = native/'ffi.c'
    text = '#include "bridge.h"\n'+path.read_text()
    text = audit.replace_once(text,'bench_report(); audit_report(); return untracked_report_result();',
                              'bench_report(); audit_report(); source_workspace_report(); return untracked_report_result();')
    path.write_text(text)
    path = native/'storage.c'
    text = '#include "bridge.h"\n'+path.read_text()
    text = audit.replace_once(text,CLOCK,'static uint64_t now_ns(void) { return 0; } /* clocks disabled for cost observation */')
    real = '    cblas_dgemm(o, ta, tb, m, n, k, a, x, lx, y, ly, b, z, lz);'
    text = audit.replace_once(text,real,
        '    source_workspace_begin(0,o,ta,tb,m,n,k,lx,ly,lz,a,0.0,b,0.0);\n'+real+'\n    source_workspace_end();')
    complex_call = '    cblas_zgemm(o, ta, tb, m, n, k, a, x, lx, y, ly, b, z, lz);'
    text = audit.replace_once(text,complex_call,
        '    const double *av = a, *bv = b;\n'
        '    source_workspace_begin(1,o,ta,tb,m,n,k,lx,ly,lz,av[0],av[1],bv[0],bv[1]);\n'+
        complex_call+'\n    source_workspace_end();')
    path.write_text(text)
    lake = native/'lakefile.lean'
    text = lake.read_text()
    target = '''input_file bridgeSource where path := "bridge.c"
input_file bridgeHeader where path := "bridge.h"
input_file observerHeader where path := "observer.h"
target bridgeObject pkg : FilePath := do
  let source ← bridgeSource.fetch
  let headers := #[← bridgeHeader.fetch, ← observerHeader.fetch]
  let source ← source.bindM fun path => (Job.collectArray headers).mapM fun _ => pure path
  buildLeanO (pkg.buildDir / "bridge.o") source #[] #["-std=c11", "-O3", "-fno-lto", "-Wall", "-Wextra", "-Werror", "-DSOURCE_WORKSPACE_DIAGNOSTIC=DIAGNOSTIC"]

'''.replace('DIAGNOSTIC"]',str(int(backend == 'diagnostic'))+'"]')
    text = audit.replace_once(text,'extern_lib storageNative pkg := do',target+'extern_lib storageNative pkg := do')
    text = audit.replace_once(text,'← auditObject.fetch]','← auditObject.fetch, ← bridgeObject.fetch]')
    lake.write_text(text)


def check_backend(record_path,stock,diagnostic):
    backend_verify.verify(record_path)
    reader = backend_verify.Reader(record_path)
    record = reader.json('record.json')
    for name,prefix in (('stock',stock),('diagnostic',diagnostic)):
        if tree.sha(prefix/'lib/libopenblas.a') != record['builds'][name]['archive_sha256']:
            raise ValueError('Backend archive is not the calibrated '+name+' build')
        for header in ('cblas.h','openblas_config.h'):
            if (prefix/'include'/header).read_bytes() != reader.read('inputs/'+name+'/include/'+header):
                raise ValueError('Backend header changed: '+name+'/'+header)
    for relative in ('observer.c','observer.h','wrappers.c','patch.py'):
        path = 'experiments/openblas_workspace/'+relative
        if tree.sha(ROOT/path) != record['repository']['inputs'][path]['sha256']:
            raise ValueError('Backend observer must be calibrated from the current exact source: '+relative)
    return reader,record


def main():
    if not __debug__: raise ValueError('Run without -O: inherited validation uses assertions')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix',required=True,type=Path,help='the paired unchanged stock backend')
    parser.add_argument('--diagnostic-prefix',required=True,type=Path)
    parser.add_argument('--backend-record',required=True,type=Path,help='completed workspace calibration directory or ZIP')
    parser.add_argument('--output',required=True,type=Path)
    parser.add_argument('--frontend',type=Path,default=ROOT/'target/debug/vastitas')
    parser.add_argument('--kernel',type=Path,default=ROOT/'lean-kernel/.lake/build/bin/vastitas-kernel')
    parser.add_argument('--cc',default='cc',help='one compiler executable')
    parser.add_argument('--smoke',action='store_true',help='tiny real/complex with/without padding; default all 12 cases')
    parser.add_argument('--one-case',action='store_true',help='explicit debugging coverage, never a full record')
    args = parser.parse_args()
    out,stock,diagnostic = args.output.resolve(),args.prefix.resolve(),args.diagnostic_prefix.resolve()
    if out.is_relative_to(ROOT): raise ValueError('output must be outside the checkout')
    out.mkdir(parents=True,exist_ok=False)
    cc = shutil.which(args.cc)
    if not cc: raise ValueError('Compiler executable not found')
    reader,calibration = check_backend(args.backend_record,stock,diagnostic)
    # Preserve the full successful calibration as a nested record; no archived
    # code is executed. The prefixes remain external, pinned by their hashes.
    calibration_dir = out/'backend-calibration'
    for name in sorted(reader.names):
        path = calibration_dir/name
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes(reader.read(name))
    env = {k:os.environ[k] for k in ('PATH','HOME','TMPDIR','SDKROOT','DEVELOPER_DIR','LANG') if k in os.environ}
    env.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',GOTO_NUM_THREADS='1',LEAN_NUM_THREADS='1',LC_ALL='C')
    runner = Runner(out,env)
    head = runner.run(['git','rev-parse','HEAD'])['stdout'].strip()
    status = runner.run(['git','status','--porcelain'])['stdout']
    runner.run(['git','diff','--binary','HEAD'])
    runner.run([cc,'--version'])
    inputs = {}
    for directory in (HERE,ROOT/'experiments/allocation_audit',ROOT/'experiments/contraction_trees',
                      ROOT/'experiments/openblas_workspace',ROOT/'lean-kernel/native',ROOT/'lean-kernel/numerical'):
        for path in sorted(directory.rglob('*')):
            if path.is_file() and not {'.lake','__pycache__','results'}.intersection(path.relative_to(directory).parts):
                relative = path.relative_to(ROOT).as_posix()
                target = out/'source'/relative
                target.parent.mkdir(parents=True,exist_ok=True)
                shutil.copyfile(path,target)
                inputs[relative] = tree.sha(path)
    for relative in ('examples/packages/contraction-tree/src/profiles/mod.vast',
                     'lean-toolchain','lean-kernel/lean-toolchain'):
        path = ROOT/relative
        target = out/'source'/relative
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(path,target)
        inputs[relative] = tree.sha(path)
    lean_prefix = Path(runner.run(['lean','--print-prefix'])['stdout'].strip())
    external = {}
    for path in (args.frontend.resolve(),args.kernel.resolve(),stock/'lib/libopenblas.a',
                 diagnostic/'lib/libopenblas.a',lean_prefix/'lib/lean/libleanrt.a',lean_prefix/'bin/lean'):
        external[str(path)] = tree.sha(path)
    for name in ('lean.h','config.h'):
        path = lean_prefix/'include/lean'/name
        shutil.copyfile(path,out/('pinned-'+name))
        external[str(path)] = tree.sha(path)
    cases = fixtures.cases(args.smoke)
    if args.one_case: cases = cases[:1]
    tree.dump(out/'cases.json',cases)
    rows,failures = [],[]
    for case in cases:
        for backend,prefix in (('stock',stock),('diagnostic',diagnostic)):
            runner.context = {'case':case['case'],'backend':backend}
            work = out/'programs'/case['case']/backend
            exe = audit.build(runner,case,work,stock,args.frontend.resolve(),args.kernel.resolve(),cc,
                'production_shared',link_prefix=prefix,runtime_hook=lambda w:decorate(w,backend))
            runner.run(['nm','-g',exe],phase='linked_symbols')
            runner.run(['otool','-L',exe] if platform.system()=='Darwin' else ['ldd',exe],phase='linked_libraries')
            for impl,scope,reps in [('failure',0,1)]+[(impl,scope,reps) for scope in (0,1)
                    for reps in (1,2,17) for impl in ('generated','c')]:
                execution = runner.run([exe,impl,scope,reps,1],phase='source_workspace')
                parsed = [json.loads(line) for line in execution['stdout'].splitlines()]
                if len(parsed) != (4 if backend == 'diagnostic' else 3):
                    raise ValueError('Missing or unexpected observation stream')
                row = dict(case=case['case'],backend=backend,implementation=impl,scope=scope,repetitions=reps,
                           costs=parsed[0],allocation=parsed[1],calls=parsed[2],
                           workspace=parsed[3] if backend == 'diagnostic' else None)
                if impl != 'failure': audit.validate(parsed[1],scope,reps,'production_shared',impl)
                (failures if impl == 'failure' else rows).append(row)
                tree.dump(out/'observations.json',dict(rows=rows,failures=failures))
    runner.context = None
    tree.verify_inputs(inputs)
    tree.verify_inputs(external)
    if runner.run(['git','rev-parse','HEAD'])['stdout'].strip()!=head or runner.run(['git','status','--porcelain'])['stdout']!=status:
        raise ValueError('Repository revision/status changed during measurement')
    binaries = {}
    for case in cases:
        for backend in ('stock','diagnostic'):
            prefix = Path('programs')/case['case']/backend
            for name in ('canonical','.lake/build/bin/audit'):
                relative = (prefix/name).as_posix()
                path = out/relative
                binaries[relative] = {'sha256':tree.sha(path),'bytes':path.stat().st_size}
    # Executables and Lake caches stay in the scratch tree. The compact record
    # retains executable fingerprints, generated Lean/C and complete raw outputs.
    files = {p.relative_to(out).as_posix():{'sha256':tree.sha(p),'bytes':p.stat().st_size}
             for p in sorted(out.rglob('*')) if p.is_file() and not '.lake' in p.relative_to(out).parts
             and not 'openblas_include' in p.relative_to(out).parts
             and p.relative_to(out).as_posix() not in binaries}
    record = {'schema':1,'kind':'source-workspace-costs','head':head,'status':status,
              'selection':'debug-one' if args.one_case else 'smoke' if args.smoke else 'full',
              'host':{'platform':platform.platform(),'cc':cc},'environment':env,
              'tools':{'frontend':str(args.frontend.resolve()),'kernel':str(args.kernel.resolve())},
              'inputs':inputs,'external_inputs':external,'backend_record':'backend-calibration',
              'backend_archives':{name:calibration['builds'][name]['archive_sha256'] for name in ('stock','diagnostic')},
              'prefixes':{'stock':str(stock),'diagnostic':str(diagnostic)},
              'claims':{'operation_timings':False,'total_heap':False,'backend_packing_bytes':False,
                        'native_refinement':False,'controlled_host':False,'source_execution_observed':True},
              'files':files,'binaries':binaries}
    tree.dump(out/'record.json',record)
    verifier = module('source_workspace_verify',HERE/'verify.py')
    print(json.dumps(verifier.verify(out),indent=2))


if __name__ == '__main__': main()
