#!/usr/bin/env python3
"""Independent schema-v2 production-helper allocation/cost record verification."""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import zipfile

VARIANTS = ('production_shared', 'private_fresh')
SIZES = {'tiny':(2,3,4,5,6), 'small':(7,17,5,11,13), 'bulk':(24,40,32,48,56)}
KINDS = {'ffi_ok','arena_external','generated_ctor','control','ffi_error','persistent_unit'}
COUNT_FIELDS = {'allocations','bytes','final_releases','released_bytes','retained_returns'}
ARENA_FIELDS = {'arena_finalizers','closed_arena_cycles','arena_allocations','arena_frees',
                'arena_peak_bytes','arena_written_bytes','arena_copied_bytes',
                'arena_metadata_allocations','arena_peak_metadata_bytes'}


def nonnegative_counts(record, fields):
    assert all(type(record[field]) is int and record[field]>=0 for field in fields)


def balanced(audit):
    assert audit['schema']==2 and audit['variant'] in VARIANTS
    shared=audit['variant']=='production_shared'
    assert audit['shared_result'] is shared
    nonnegative_counts(audit, ('tracked_live_bytes','tracked_peak_bytes'))
    assert audit['tracked_live_bytes']==(16 if shared else 0)
    assert set(audit['phases'])=={'startup','cold','setup','run','cleanup'}
    for phase in audit['phases'].values():
        assert set(phase)==ARENA_FIELDS|{'kinds'} and set(phase['kinds'])==KINDS
        nonnegative_counts(phase, ARENA_FIELDS)
        for kind,counts in phase['kinds'].items():
            assert set(counts)==COUNT_FIELDS
            nonnegative_counts(counts, COUNT_FIELDS)
            if kind!='persistent_unit' or not shared:assert counts['retained_returns']==0
    for kind in KINDS:
        records=[phase['kinds'][kind] for phase in audit['phases'].values()]
        retained=int(kind=='persistent_unit' and shared)
        assert sum(x['allocations']-x['final_releases'] for x in records)==retained
        assert sum(x['bytes']-x['released_bytes'] for x in records)==16*retained


def costs(case,scope,reps):
    i,k,j,a,b,p=(case[x] for x in ('i','k','j','a','b','pad'))
    width=16 if case['scalar'] else 8
    dims=[(i,k*j),(k,a),(j,b),(i*j,k),(i*j,a),(i*a,b),(i*a,j)]
    capacity=[(idx+1)*p+(rows+(idx+2)*p)*columns+3*p for idx,(rows,columns) in enumerate(dims)]
    peak=width*(sum(capacity[:6])-capacity[3]+max(capacity[3],capacity[6]))
    packed=width*(i*k*j+i*j*a)
    writes=width*(i*k*j+2*i*j*a+i*a*b)
    init=peak+width*(i*k*j+k*a+j*b+6)
    lives=reps if scope==0 else 1
    expected=dict(data_allocations=6*lives,data_frees=6*lives,live_bytes_after=0,peak_data_bytes=peak,
        written_bytes=init*lives+writes*reps,copied_bytes=packed*reps,metadata_allocations=2*lives,
        timed_data_allocations=6*reps if scope==0 else 0,timed_data_frees=6*reps if scope==0 else 0,
        timed_written_bytes=(init+writes)*reps if scope==0 else writes*reps,timed_copied_bytes=packed*reps,
        timed_metadata_allocations=2*reps if scope==0 else 0,selected_pack_calls_timed=0,blas_calls_timed=0)
    return expected,dict(peak=peak,init=init,writes=writes,packed=packed,lives=lives)


def verify(read,names):
    load=lambda name:json.loads(read(name))
    environment=load('environment.json')
    assert environment['schema']==2 and environment['variants']==list(VARIANTS)
    assert environment['recorded_inputs_unchanged'] is True
    # The prototype verifier/record remains separate and unmodified.
    raw_cases=load('cases.json');cases={case['case']:case for case in raw_cases}
    assert len(raw_cases)==len(cases)
    expected_case_names=set()
    selection=environment['selection']
    assert selection in ('smoke','full','debug-one')
    sizes=SIZES if selection=='full' else {'tiny':SIZES['tiny']}
    for size,scalar,pad in itertools.product(sizes,range(2),range(2)):
        expected_case_names.add(f"{size}-{'complex' if scalar else 'f64'}-p{pad}")
    if selection=='debug-one':assert len(cases)==1
    else:assert set(cases)==expected_case_names
    for case in cases.values():
        assert type(case['scalar']) is int and type(case['pad']) is int
        assert case['scalar'] in (0,1) and case['pad'] in (0,1)
        size=case['case'].split('-')[0]
        assert size in SIZES and tuple(case[x] for x in ('i','k','j','a','b'))==SIZES[size]
        assert case['case']==f"{size}-{'complex' if case['scalar'] else 'f64'}-p{case['pad']}"
    rows=load('allocations.json')
    fields=('case','variant','scope','repetitions','implementation')
    keys=[tuple(row[x] for x in fields) for row in rows]
    assert all(type(row[x]) is int for row in rows for x in ('scope','repetitions'))
    assert len(keys)==len(set(keys))
    assert set(keys)==set(itertools.product(cases,VARIANTS,(0,1),(1,2,17),('generated','c')))
    lookup=dict(zip(keys,rows))
    for row in rows:
        shared=row['variant']=='production_shared';scope=row['scope'];reps=row['repetitions']
        audit=row['audit'];balanced(audit);assert audit['variant']==row['variant']
        nonnegative_counts(row['costs'], set(row['costs'])-{'checksum','observed'})
        run=audit['phases']['run'];kinds=run['kinds']
        if row['implementation']=='generated':
            ffi=(reps if shared else 36*reps) if scope==0 else (0 if shared else 4*reps)
            external=reps if scope==0 else 0
            fallback=reps if shared and scope==0 else 0
            assert kinds['ffi_ok']['allocations']==kinds['ffi_ok']['final_releases']==ffi
            assert kinds['ffi_ok']['bytes']==16*ffi
            assert kinds['arena_external']['allocations']==kinds['arena_external']['final_releases']==external
            assert kinds['arena_external']['bytes']==24*external
            assert kinds['generated_ctor']['allocations']==2+fallback
            assert kinds['generated_ctor']['bytes']==48+16*fallback
            assert kinds['control']['allocations']==1 and kinds['control']['bytes']==16
            assert kinds['persistent_unit']['retained_returns']==((35*reps if scope==0 else 4*reps) if shared else 0)
            allocation_count=((3*reps+3 if shared else 37*reps+3) if scope==0 else
                              (3 if shared else 4*reps+3))
            allocation_bytes=((56*reps+64 if shared else 600*reps+64) if scope==0 else
                              (64 if shared else 64*reps+64))
            peak=88 if shared else 72
        else:
            allocation_count=allocation_bytes=0
            peak=40
            assert kinds['persistent_unit']['retained_returns']==0
        assert audit['tracked_peak_bytes']==peak
        # Balance alone permits an unexpected allocation that is subsequently
        # freed. Check the complete observed run cost, including absent kinds.
        for kind in ('ffi_error','persistent_unit'):
            assert all(kinds[kind][field]==0 for field in COUNT_FIELDS-{'retained_returns'})
        for field in ('allocations','final_releases'):
            assert sum(counts[field] for counts in kinds.values())==allocation_count
        for field in ('bytes','released_bytes'):
            assert sum(counts[field] for counts in kinds.values())==allocation_bytes
        cold=audit['phases']['cold']
        assert cold['closed_arena_cycles']==cold['arena_finalizers']==1
        assert cold['arena_allocations']==cold['arena_frees']==6 and cold['arena_metadata_allocations']==2
        assert cold['kinds']['ffi_ok']['allocations']==(1 if shared else 36)
        assert cold['kinds']['persistent_unit']['allocations']==int(shared)
        assert cold['kinds']['persistent_unit']['retained_returns']==(35 if shared else 0)
        assert cold['kinds']['arena_external']['allocations']==1
        assert sum(p['kinds']['persistent_unit']['allocations'] for p in audit['phases'].values())==int(shared)
        expected,dimensions=costs(cases[row['case']],scope,reps)
        for name,value in expected.items():assert row['costs'][name]==value,(name,row)
        assert cold['arena_peak_bytes']==dimensions['peak']
        assert cold['arena_written_bytes']==dimensions['init']+dimensions['writes']
        assert cold['arena_copied_bytes']==dimensions['packed']
        end=audit['phases']['run' if scope==0 else 'cleanup']
        assert end['closed_arena_cycles']==dimensions['lives']
        assert end['arena_finalizers']==(dimensions['lives'] if row['implementation']=='generated' else 0)
        assert end['arena_allocations']==end['arena_frees']==6*dimensions['lives']
        assert end['arena_written_bytes']==row['costs']['written_bytes'] and end['arena_copied_bytes']==row['costs']['copied_bytes']
        other=lookup[(row['case'],row['variant'],scope,reps,'c' if row['implementation']=='generated' else 'generated')]
        assert all(row['costs'][k]==other['costs'][k] for k in row['costs'] if k not in ('elapsed_ns','process_maxrss_kib'))
        assert row['costs']['checksum']!='0000000000000000'
    commands=load('commands.json')
    normal=[c for c in commands if c['phase']=='allocation_audit'];assert len(normal)==len(rows)
    for row,command in zip(rows,normal):
        assert command['returncode']==0
        cost,audit=map(json.loads,command['stdout'].splitlines())
        assert cost==row['costs'] and audit==row['audit']
        assert command['command'][-4:]==[row['implementation'],str(row['scope']),str(row['repetitions']),'1']
        assert '/'+row['case']+'/'+row['variant']+'/' in command['command'][0]
    failures=[c for c in commands if c['phase']=='failure_cleanup'];assert len(failures)==2*len(cases)
    failure_keys=set()
    for command in failures:
        assert command['returncode']==0
        cost,audit=map(json.loads,command['stdout'].splitlines());balanced(audit)
        nonnegative_counts(cost, set(cost)-{'checksum','observed'})
        assert audit['tracked_peak_bytes']==(56 if audit['variant']=='production_shared' else 40)
        case=next(name for name in cases if '/'+name+'/' in command['command'][0]);failure_keys.add((case,audit['variant']))
        assert cost['data_allocations']==cost['data_frees']==6 and cost['live_bytes_after']==0
        assert audit['phases']['run']['kinds']['ffi_error']['allocations']==1
        assert audit['phases']['run']['arena_finalizers']==1
    assert failure_keys==set(itertools.product(cases,VARIANTS))
    threads=[c for c in commands if c['phase']=='production_thread_test'];assert len(threads)==4
    for command in threads:
        assert command['returncode']==0
        result=json.loads(command['stdout'])
        nonnegative_counts(result, set(result)-{'production_thread_test'})
        assert result==dict(production_thread_test='passed',workers=8,initializations=1,calls=8001,fresh_arena_results=2,fresh_stats_results=2,fresh_errors=2)
    assert all(type(c['returncode']) is int for c in commands)
    assert all(c['phase']=='frontend_capture' and c['returncode']==1 and 'E_CAPTURED' in c['stderr'] for c in commands if c['returncode'])
    counts=Counter(c['phase'] for c in commands)
    assert all(counts[p]==2*len(cases) for p in ('frontend_capture','public_check','public_build','public_execute','kernel_emit','kernel_failure_emit','audit_build'))
    snapshots=0;root=environment['checkout_root']+'/'
    for path,digest in environment['inputs'].items():
        if path.startswith(root):
            relative=path[len(root):]
            if 'source/'+relative in names:
                assert hashlib.sha256(read('source/'+relative)).hexdigest()==digest;snapshots+=1
            else:assert relative in ('target/debug/vastitas','target/release/vastitas','lean-kernel/.lake/build/bin/vastitas-kernel')
        elif path.endswith('/include/lean/lean.h'):assert hashlib.sha256(read('pinned-lean.h')).hexdigest()==digest
        elif path.endswith('/include/lean/config.h'):assert hashlib.sha256(read('pinned-config.h')).hexdigest()==digest
    for case,variant in itertools.product(cases,VARIANTS):
        prefix=case+'/'+variant+'/'
        response=load(prefix+'response.json');failure=load(prefix+'failure-response.json')
        assert response['ok'] and failure['ok'] and response['version']==failure['version']==8
        assert response['lean_source'].encode()==read(prefix+'Generated.lean')
        assert failure['lean_source'].encode()==read(prefix+'GeneratedFailure.lean')
        assert b'lean_is_exclusive' in read(prefix+'Emitted.c') and b'lean_alloc_ctor' in read(prefix+'Emitted.c')
        ffi=read(prefix+'native/ffi.c')
        if variant=='production_shared':
            for item in (b'lean_obj_once(&unit_success, &success_once, initialize_success)',b'lean_mark_persistent(result)',b'audit_shared_create()',b'audit_shared_return(result)'):assert item in ffi
        else:assert b'lean_obj_once' not in ffi and b'EXPERIMENT ONLY: fresh-result comparator' in ffi
        assert b'allocation_persistent_unit' not in ffi
    thread=read('production-thread-test/native/ffi.c')
    assert b'lean_obj_once(&unit_success, &success_once, initialize_success)' in thread
    assert b'lean_mark_persistent(result);\n    allocation_thread_initialize(result);' in thread
    assert b'audit_shared_create' not in thread
    assert load('status.json')==dict(schema=2,status='passed',rows=len(rows),performance='not measured')
    return dict(status='passed',schema=2,records=len(rows),pairs=len(rows)//2,source_snapshots=snapshots,failure_cleanups=len(failures),thread_processes=4,performance='not measured')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('record',type=Path);args=parser.parse_args()
    if args.record.is_dir():
        names=[str(p.relative_to(args.record)) for p in args.record.rglob('*') if p.is_file()]
        result=verify(lambda name:(args.record/name).read_bytes(),names)
    else:
        manifest=json.loads((args.record.parent/'manifest.json').read_text())
        archive_bytes=args.record.read_bytes()
        assert manifest['schema']==2 and manifest['archive']==args.record.name
        assert len(archive_bytes)==manifest['archive_bytes']
        assert hashlib.sha256(archive_bytes).hexdigest()==manifest['archive_sha256']
        with zipfile.ZipFile(args.record) as archive:
            assert archive.testzip() is None and len(archive.namelist())==len(set(archive.namelist()))
            assert all(not x.startswith('/') and '..' not in Path(x).parts for x in archive.namelist())
            assert set(archive.namelist())=={item['path'] for item in manifest['files']}
            for item in manifest['files']:
                data=archive.read(item['path'])
                assert len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256']
            for name,digest in manifest['plain_copies'].items():
                data=(args.record.parent/name).read_bytes()
                assert data==archive.read(name) and hashlib.sha256(data).hexdigest()==digest
            result=verify(archive.read,archive.namelist())
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
