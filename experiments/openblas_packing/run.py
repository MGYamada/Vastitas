#!/usr/bin/env python3
"""Build pinned paired backends; calibrate and observe actual GEMM packing."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import re
import shutil
import sys
import tarfile
import urllib.request

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT/'experiments/openblas_workspace'))
from experiments.openblas_workspace.run import Runner, digest, dump, objects
from experiments.openblas_packing.patch import PINS, patch
from scripts.build_openblas import VERSION, URL, SHA256, OPTIONS

SHAPES = ((0,5,7),(5,0,7),(5,7,0),(1,17,23),(17,1,23),(1,1,7),
          (2,2,2),(17,19,23),(2,50000,7),(3,5,2051),(2051,5,7),(256,256,256))


def cases():
    return [('adapter',['calibration'])] + [
        ('adapter',list(map(str,(s,n,t)))) for s in range(2) for n in (0,2,32,256) for t in range(3)] + [
        ('rectangle',list(map(str,(s,*shape,ta,tb,beta))))
        for s in range(2) for shape in SHAPES for ta in range(3) for tb in range(3) for beta in range(2)]


def widths(config):
    result = {}
    for scalar in ('D','Z'):
        for axis in ('M','N'):
            found = re.findall(rf'^{scalar}GEMM_UNROLL_{axis}=([0-9]+)$',config,re.M)
            if len(found)!=1 or int(found[0]) not in (1,2,4,8,16):
                raise ValueError('unsupported/missing unroll configuration')
            result[scalar+'_'+axis]=int(found[0])
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--build-dir',type=Path,required=True)
    parser.add_argument('--archive',type=Path)
    parser.add_argument('--cc',default='cc')
    parser.add_argument('--jobs',type=int,default=4)
    parser.add_argument('--target',choices=['HASWELL','ARMV8'])
    args=parser.parse_args()
    if not 1<=args.jobs<=64 or platform.system() not in ('Darwin','Linux'):
        parser.error('requires macOS/Linux and 1..64 build jobs')
    out,build=args.out.resolve(),args.build_dir.resolve()
    if any(p.is_relative_to(ROOT) for p in (out,build)) or out.is_relative_to(build) or build.is_relative_to(out):
        parser.error('record/build must be separate new directories outside the checkout')
    out.mkdir(parents=True,exist_ok=False); build.mkdir(parents=True,exist_ok=False)
    cc=shutil.which(args.cc)
    if not cc: raise ValueError('compiler not found')
    cc=str(Path(cc).resolve())
    env={k:os.environ[k] for k in ('PATH','HOME','ELAN_HOME','TMPDIR','SDKROOT','DEVELOPER_DIR','LANG') if k in os.environ}
    env.update(OPENBLAS_NUM_THREADS='1',GOTO_NUM_THREADS='1',OMP_NUM_THREADS='1',LC_ALL='C')
    run=Runner(out,env)
    head=run.run(['git','rev-parse','HEAD'],'git-head')[0].strip()
    status=run.run(['git','status','--porcelain'],'git-status')[0]
    run.run(['git','diff','--binary','HEAD'],'git-diff')
    compiler=run.run([cc,'--version'],'cc-version')[0]
    paths=[]
    for directory in (HERE,ROOT/'experiments/openblas_workspace'):
        paths += [p for p in directory.rglob('*') if p.is_file() and
                  not {'results','__pycache__'}.intersection(p.relative_to(directory).parts)]
    paths += [ROOT/p for p in ('scripts/build_openblas.py','lean-kernel/native/storage.c',
        'lean-kernel/native/storage.h','lean-kernel/native/diagonal.c','lean-kernel/native/diagonal.h',
        'lean-kernel/numerical/gemm.c','lean-kernel/numerical/gemm.h')]
    inputs={}
    for p in sorted(paths):
        relative=p.relative_to(ROOT).as_posix(); target=out/'inputs/repository'/relative
        target.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(p,target)
        inputs[relative]={'snapshot':target.relative_to(out).as_posix(),'sha256':digest(p)}
    archive=args.archive.resolve() if args.archive else build/'OpenBLAS.tar.gz'
    if not args.archive:
        with urllib.request.urlopen(URL,timeout=120) as src, archive.open('wb') as dst:
            shutil.copyfileobj(src,dst)
    if digest(archive)!=SHA256: raise ValueError('release archive checksum')
    with tarfile.open(archive) as tar: tar.extractall(build,filter='data')
    source=build/f'OpenBLAS-{VERSION}'
    upstream=out/'inputs/upstream'
    for name in (*PINS,'LICENSE'):
        target=upstream/name; target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source/name,target)
    options=[*OPTIONS,f'CC={cc}',*([f'TARGET={args.target}'] if args.target else [])]
    snapshots=out/'inputs/repository'; experiment=snapshots/'experiments/openblas_packing'
    workspace=snapshots/'experiments/openblas_workspace'
    native,numerical=snapshots/'lean-kernel/native',snapshots/'lean-kernel/numerical'
    (out/'binaries').mkdir()
    builds={}; calibrations=[]
    for variant in ('stock','diagnostic'):
        if variant=='diagnostic':
            for name in PINS:
                data=patch(name,(upstream/name).read_bytes()); (source/name).write_bytes(data)
                target=upstream/'diagnostic'/name; target.parent.mkdir(parents=True,exist_ok=True)
                target.write_bytes(data)
            for original,target in (('observer.c','vobs-observer.c'),('wrappers.c','vobs-wrappers.c'),('observer.h','observer.h')):
                shutil.copyfile(workspace/original,source/'driver/others'/target)
            for original,target in (('observer.c','vpack-observer.c'),('observer.h','vpack.h')):
                shutil.copyfile(experiment/original,source/'driver/others'/target)
        run.run(['make',f'-j{args.jobs}',*options,'libs'],variant+'-build',source)
        prefix=build/variant
        run.run(['make',*options,f'PREFIX={prefix}','install'],variant+'-install',source)
        library=prefix/'lib/libopenblas.a'
        dump(out/(variant+'-objects.json'),objects(source))
        includes=out/'inputs'/variant; shutil.copytree(prefix/'include',includes/'include')
        for name in ('config.h','config_kernel.h','Makefile.conf'):
            if (source/name).exists(): shutil.copyfile(source/name,includes/name)
        unroll=widths((source/'Makefile.conf').read_text())
        flags=['-std=c11','-O2','-fno-lto','-Wall','-Wextra','-Werror']
        inc=['-I'+str(native),'-I'+str(numerical),'-I'+str(workspace),'-I'+str(prefix/'include')]
        # Keep the existing adapter fixture itself unchanged. Only append the
        # private report after its complete cleanup/workspace dump.
        adapter=(workspace/'probe.c').read_text()
        if adapter.count('vobs_dump();')!=1: raise ValueError('adapter report anchor')
        adapter=adapter.replace('vobs_dump();','vobs_dump();\n#ifdef VOBS_DIAGNOSTIC\n    vpack_dump();\n#endif')
        adapter='void vpack_dump(void);\n'+adapter
        adapter_source=out/'inputs/adapter-probe.c'; adapter_source.write_text(adapter)
        for family in ('adapter','rectangle'):
            binary=out/'binaries'/f'{variant}-{family}'
            extra=[native/'storage.c',native/'diagonal.c',numerical/'gemm.c'] if family=='adapter' else []
            define='-DVOBS_DIAGNOSTIC' if family=='adapter' else '-DVPACK_DIAGNOSTIC'
            fixture=adapter_source if family=='adapter' else experiment/'probe.c'
            run.run([cc,*flags,*inc,*([define] if variant=='diagnostic' else []),*extra,fixture,
                     library,'-lm','-lpthread','-o',binary],f'{variant}-{family}-link')
            run.run(['nm','-g',binary],f'{variant}-{family}-symbols')
            run.run(['otool','-L',binary] if platform.system()=='Darwin' else ['ldd',binary],f'{variant}-{family}-linkage')
        for sanitized in (False,True):
            label=f'{variant}-calibration'+('-sanitized' if sanitized else '')
            binary=out/'binaries'/label
            run.run([cc,*flags,*['-DVP_'+key+'='+str(v) for key,v in unroll.items()],
                     *(['-fsanitize=address,undefined','-fno-omit-frame-pointer'] if sanitized else []),
                     experiment/'calibrate.c',library,'-lm','-lpthread','-o',binary],label+'-link')
            raw,stdout=run.run([binary],label)
            calibrations.append({'variant':variant,'sanitized':sanitized,'stdout':stdout,'result':json.loads(raw)})
        builds[variant]={'archive_sha256':digest(library),'archive_bytes':library.stat().st_size,
                         'objects':variant+'-objects.json','unroll':unroll}
    old,new=(json.loads((out/(v+'-objects.json')).read_text()) for v in ('stock','diagnostic'))
    changed=sorted(p for p in old if old[p]!=new.get(p))
    allowed={'driver/others/memory.o','interface/cblas_dgemm.o','interface/cblas_zgemm.o'} | {
        p for p in old if re.fullmatch(r'driver/level3/[dz]gemm_[ntrc]{2}\.o',p)}
    if old.keys()!=new.keys() or set(changed)!=allowed:
        raise ValueError(f'unexpected changed objects: {changed}')
    runs=[]
    for repeat in (1,2):
        for index,(family,case) in enumerate(cases()):
            for variant in ('stock','diagnostic'):
                label=f'{variant}-{repeat}-{index:03d}'
                raw,stdout=run.run([out/'binaries'/f'{variant}-{family}',*case],label)
                parsed=label+'.json'; dump(out/parsed,[json.loads(line) for line in raw.splitlines()])
                runs.append({'variant':variant,'repeat':repeat,'family':family,'case':case,'stdout':stdout,'parsed':parsed})
    # The broad grid is not sufficient evidence for every observed block/lda.
    # Replay the actual distinct copy contracts against each unchanged kernel,
    # with complete input/output canaries and both plain/sanitized harnesses.
    contracts=set()
    for observed in runs:
        if observed['variant']=='diagnostic':
            for call in json.loads((out/observed['parsed']).read_text())[2]['calls']:
                contracts.add(tuple(call[key] for key in ('kernel','m','n','lda')))
    footprints=[]
    for index,contract in enumerate(sorted(contracts)):
        for variant in ('stock','diagnostic'):
            for sanitized in (False,True):
                binary=out/'binaries'/(variant+'-calibration'+('-sanitized' if sanitized else ''))
                raw,stdout=run.run([binary,*contract],f'footprint-{index:03d}-{variant}-{int(sanitized)}')
                footprints.append({'variant':variant,'sanitized':sanitized,'contract':contract,
                                   'stdout':stdout,'result':json.loads(raw)})
    for p,entry in inputs.items():
        if digest(ROOT/p)!=entry['sha256']: raise ValueError('input changed during observation: '+p)
    if run.run(['git','rev-parse','HEAD'],'git-head-after')[0].strip()!=head or run.run(['git','status','--porcelain'],'git-status-after')[0]!=status:
        raise ValueError('repository changed during observation')
    files={p.relative_to(out).as_posix():{'sha256':digest(p),'bytes':p.stat().st_size} for p in sorted(out.rglob('*')) if p.is_file()}
    record={'schema':2,'kind':'diagnostic-openblas-packing','created_utc':datetime.now(timezone.utc).isoformat(),
        'repository':{'head':head,'status':status,'inputs':inputs},'upstream':{'version':VERSION,'url':URL,
            'sha256':SHA256,'options':options,'changed_objects':changed},'host':{'system':platform.system(),
            'platform':platform.platform(),'machine':platform.machine(),'cc':cc,'cc_version':compiler},
        'environment':env,'builds':builds,'calibrations':calibrations,'footprints':footprints,
        'runs':runs,'commands':'commands.json','files':files}
    dump(out/'record.json',record)
    from experiments.openblas_packing.verify import verify
    print(json.dumps(verify(out),indent=2))


if __name__=='__main__': main()
