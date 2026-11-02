#!/usr/bin/env python3
"""Build paired stock/diagnostic pinned OpenBLAS and observe workspace lifetimes."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tarfile
import urllib.request

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
from build_openblas import VERSION, URL, SHA256, OPTIONS
from patch import patched_memory


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True)+'\n')


class Runner:
    def __init__(self, out, env):
        self.out, self.env, self.commands = out, env, []
        (out/'logs').mkdir()

    def run(self, argv, label, cwd=ROOT):
        argv = list(map(str, argv))
        stem = f'logs/{len(self.commands):03d}-{label}'
        with (self.out/(stem+'.stdout')).open('w') as stdout, (self.out/(stem+'.stderr')).open('w') as stderr:
            result = subprocess.run(argv, cwd=cwd, env=self.env, stdout=stdout, stderr=stderr, text=True)
        self.commands.append({'argv': argv, 'cwd': str(cwd), 'label': label,
                              'returncode': result.returncode, 'stdout': stem+'.stdout', 'stderr': stem+'.stderr'})
        dump(self.out/'commands.json', self.commands)
        if result.returncode:
            raise RuntimeError(f'{label} exited {result.returncode}; see {self.out/stem}.stderr')
        return (self.out/(stem+'.stdout')).read_text(), stem+'.stdout'


def objects(source):
    return {p.relative_to(source).as_posix(): digest(p) for p in sorted(source.rglob('*.o'))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True, help='new record directory outside the repository')
    parser.add_argument('--build-dir', type=Path, required=True, help='new separate scratch directory; retained, not part of the record')
    parser.add_argument('--archive', type=Path, help='already downloaded pinned release archive')
    parser.add_argument('--cc', default='cc', help='compiler executable, not shell text')
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--target', choices=['HASWELL', 'ARMV8'])
    args = parser.parse_args()
    if not 1 <= args.jobs <= 64:
        parser.error('--jobs must be between 1 and 64')
    if platform.system() not in ('Darwin', 'Linux'):
        raise ValueError('Only macOS/Linux 64-bit sequential profiles are supported')
    out, build = args.out.resolve(), args.build_dir.resolve()
    if out.is_relative_to(ROOT) or build.is_relative_to(ROOT) or out.is_relative_to(build) or build.is_relative_to(out):
        raise ValueError('Output and build directories must be separate and outside the repository')
    out.mkdir(parents=True, exist_ok=False)
    build.mkdir(parents=True, exist_ok=False)
    cc = shutil.which(args.cc)
    if not cc:
        raise ValueError('Compiler not found')
    cc = str(Path(cc).resolve())
    # Deliberately do not inherit Make/C/compiler/preload options. Preserve only
    # host tool discovery, SDK/temp paths and locale; this is not a hermetic SDK.
    env = {k: os.environ[k] for k in ('PATH','HOME','ELAN_HOME','TMPDIR','SDKROOT','DEVELOPER_DIR','LANG') if k in os.environ}
    env.update(OPENBLAS_NUM_THREADS='1', GOTO_NUM_THREADS='1', OMP_NUM_THREADS='1', LC_ALL='C')
    run = Runner(out, env)
    head = run.run(['git','rev-parse','HEAD'], 'git-head')[0].strip()
    status = run.run(['git','status','--porcelain'], 'git-status')[0]
    run.run(['git','diff','--binary','HEAD'], 'git-diff')
    cc_version = run.run([cc,'--version'], 'cc-version')[0]
    sources = [p for p in HERE.rglob('*') if p.is_file() and
               not {'results','__pycache__'}.intersection(p.relative_to(HERE).parts)]
    sources += [ROOT/p for p in ('scripts/build_openblas.py', 'lean-kernel/native/storage.c',
        'lean-kernel/native/storage.h', 'lean-kernel/native/diagonal.c', 'lean-kernel/native/diagonal.h',
        'lean-kernel/numerical/gemm.c', 'lean-kernel/numerical/gemm.h')]
    inputs = {}
    for path in sorted(sources):
        relative = path.relative_to(ROOT).as_posix()
        target = out/'inputs/repository'/relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path,target)
        inputs[relative] = {'snapshot': target.relative_to(out).as_posix(), 'sha256': digest(path)}
    archive = args.archive.resolve() if args.archive else build/'OpenBLAS.tar.gz'
    if args.archive is None:
        with urllib.request.urlopen(URL, timeout=120) as src, archive.open('wb') as dst:
            shutil.copyfileobj(src,dst)
    if digest(archive) != SHA256:
        raise ValueError('OpenBLAS release archive checksum mismatch')
    with tarfile.open(archive) as tar:
        tar.extractall(build, filter='data')
    source = build/f'OpenBLAS-{VERSION}'
    upstream = out/'inputs/upstream'
    upstream.mkdir()
    for name in ('driver/others/memory.c','interface/gemm.c','LICENSE'):
        target = upstream/name
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source/name,target)
    options = [*OPTIONS, f'CC={cc}', *([f'TARGET={args.target}'] if args.target else [])]
    snapshots = out/'inputs/repository'
    experiment = snapshots/'experiments/openblas_workspace'
    native, numerical = snapshots/'lean-kernel/native', snapshots/'lean-kernel/numerical'
    (out/'binaries').mkdir()
    builds = {}
    for variant in ('stock','diagnostic'):
        if variant == 'diagnostic':
            (source/'driver/others/memory.c').write_bytes(patched_memory((upstream/'driver/others/memory.c').read_bytes()))
            for a,b in (('observer.c','vobs-observer.c'),('wrappers.c','vobs-wrappers.c'),('observer.h','observer.h')):
                shutil.copyfile(experiment/a,source/'driver/others'/b)
            shutil.copyfile(source/'driver/others/memory.c',upstream/'memory-diagnostic.c')
        run.run(['make',f'-j{args.jobs}',*options,'libs'], variant+'-build', source)
        prefix = build/variant
        run.run(['make',*options,f'PREFIX={prefix}','install'], variant+'-install', source)
        library = prefix/'lib/libopenblas.a'
        object_hashes = objects(source)
        dump(out/(variant+'-objects.json'),object_hashes)
        includes = out/'inputs'/variant
        shutil.copytree(prefix/'include',includes/'include')
        for name in ('config.h','config_kernel.h','Makefile.conf'):
            if (source/name).exists(): shutil.copyfile(source/name,includes/name)
        binary = out/'binaries'/variant
        flags = ['-std=c11','-O2','-fno-lto','-Wall','-Wextra','-Werror',
                 '-I'+str(native),'-I'+str(numerical),'-I'+str(experiment),'-I'+str(prefix/'include')]
        run.run([cc,*flags,*(['-DVOBS_DIAGNOSTIC'] if variant == 'diagnostic' else []),
                 native/'storage.c',native/'diagonal.c',numerical/'gemm.c',experiment/'probe.c',
                 library,'-lm','-lpthread','-o',binary],variant+'-link')
        run.run(['nm','-g',binary],variant+'-symbols')
        run.run(['otool','-L',binary] if platform.system() == 'Darwin' else ['ldd',binary],variant+'-linkage')
        builds[variant] = {'archive_sha256':digest(library),'archive_bytes':library.stat().st_size,
                           'objects':variant+'-objects.json','binary':'binaries/'+variant}
    old = json.loads((out/'stock-objects.json').read_text())
    new = json.loads((out/'diagnostic-objects.json').read_text())
    changed = sorted(p for p in old if old[p] != new.get(p))
    if old.keys() != new.keys() or changed != ['driver/others/memory.o']:
        raise ValueError(f'Diagnostic build changed unexpected objects: {changed}')
    runs = []
    cases = [['calibration']] + [[str(s),str(n),str(t)] for s in range(2) for n in (0,2,32,256) for t in range(3)]
    for repeat in range(1,4):
        for index, case in enumerate(cases):
            for variant in ('stock','diagnostic'):
                label = f'{variant}-{repeat}-{index:02d}'
                raw, stdout = run.run([out/'binaries'/variant,*case],label)
                rows = [json.loads(line) for line in raw.splitlines()]
                parsed = f'{label}.json'
                dump(out/parsed,rows)
                runs.append({'variant':variant,'repeat':repeat,'case':case,'stdout':stdout,'parsed':parsed})
    for relative, entry in inputs.items():
        if digest(ROOT/relative) != entry['sha256']:
            raise ValueError(f'Source changed during observation: {relative}')
    if (run.run(['git','rev-parse','HEAD'],'git-head-after')[0].strip() != head or
        run.run(['git','status','--porcelain'],'git-status-after')[0] != status):
        raise ValueError('Repository revision/status changed during observation')
    files = {p.relative_to(out).as_posix():{'sha256':digest(p),'bytes':p.stat().st_size}
             for p in sorted(out.rglob('*')) if p.is_file()}
    record = {'schema':1,'kind':'diagnostic-openblas-workspace','created_utc':datetime.now(timezone.utc).isoformat(),
              'repository':{'head':head,'status':status,'inputs':inputs},
              'upstream':{'version':VERSION,'url':URL,'sha256':SHA256,'options':options,'changed_objects':changed},
              'host':{'system':platform.system(),'platform':platform.platform(),'machine':platform.machine(),
                      'cc':cc,'cc_version':cc_version},'environment':env,'builds':builds,'runs':runs,
              'claims':{'timing':False,'unchanged_backend':False,'total_process_memory':False,
                        'actual_packing_bytes':False,'controlled_host':False,'stock_kernel_objects_unchanged':True},
              'commands':'commands.json','files':files}
    dump(out/'record.json',record)
    from verify import verify
    summary = verify(out)
    print(json.dumps({k:v for k,v in summary.items() if k != 'observations'},indent=2))


if __name__ == '__main__':
    main()
