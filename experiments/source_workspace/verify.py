#!/usr/bin/env python3
"""Replay the source/object/arena/backend composition; never execute archived code."""
import argparse
from collections import Counter
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def module(name,path):
    spec = importlib.util.spec_from_file_location(name,path)
    loaded = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(loaded)
    return loaded


backend = module('source_cost_backend',ROOT/'experiments/openblas_workspace/verify.py')
objects = module('source_cost_objects',ROOT/'experiments/allocation_audit/verify.py')
allocator = module('source_cost_allocator',HERE/'allocator.py')
packing = module('source_cost_packing',HERE/'packing.py')
require = backend.require
CLAIMS = {'operation_timings':False,'total_heap':False,'backend_packing_bytes':False,
          'native_refinement':False,'controlled_host':False,'source_execution_observed':True}


def check_cases(raw,selection):
    """Independently fix dimensions and coverage; archive labels grant no scope."""
    require(selection in ('full','smoke','debug-one','streaming','debug-streaming-one'), 'selection')
    streaming = selection in ('streaming','debug-streaming-one')
    sizes = {'streaming':(512,2,2,64,512)} if streaming else objects.SIZES
    expected_sizes = {'tiny':sizes['tiny']} if selection=='smoke' else sizes
    require(len(raw)==len({c['case'] for c in raw}), 'duplicate case')
    expected = {f"{name}-{'complex' if scalar else 'f64'}-p{pad}"
                for name,scalar,pad in itertools.product(expected_sizes,(0,1),(0,1))}
    debug = selection in ('debug-one','debug-streaming-one')
    require(len(raw)==1 if debug else {c['case'] for c in raw}==expected, 'case coverage')
    for c in raw:
        require(all(type(c[k]) is int for k in ('i','k','j','a','b','scalar','pad')) and
                c['scalar'] in (0,1) and c['pad'] in (0,1), 'case domain')
        size = c['case'].split('-')[0]
        require(size in sizes and tuple(c[k] for k in ('i','k','j','a','b'))==sizes[size], 'case dimensions')
        require(c['case']==f"{size}-{'complex' if c['scalar'] else 'f64'}-p{c['pad']}", 'case name')
    # Large outputs use smaller batches so the same fixed-capacity packing
    # observer remains bounded. Missing or substituted repetitions still fail.
    return {c['case']:c for c in raw}, (1,2) if streaming else (1,2,17)


class Prefixed:
    def __init__(self,parent,prefix):
        self.parent,self.prefix = parent,prefix+'/'
        self.names = {n[len(self.prefix):] for n in parent.names if n.startswith(self.prefix)}

    def read(self,name): return self.parent.read(self.prefix+name)
    def json(self,name): return json.loads(self.read(name))


def check_calls(trace,events,case,reps,*,with_packing=False):
    require(set(trace) == {'kind','schema','backend_events_observed','observer_static_bytes','capacity','calls'}, 'call envelope')
    require(trace['kind']=='source_cblas_calls' and type(trace['schema']) is int and
            trace['schema']==(2 if with_packing else 1) and trace['capacity']==256, 'call schema')
    require(type(trace['backend_events_observed']) is bool and trace['backend_events_observed']==(events is not None), 'backend observation domain')
    backend.natural(trace['observer_static_bytes'],'bridge bytes',positive=True)
    calls = trace['calls']
    require(len(calls)==2*(1+reps) and len(calls)<=256, 'missing/extra actual CBLAS calls')
    i,k,j,a,b,p = (case[x] for x in ('i','k','j','a','b','pad'))
    leading = ((i*j+5*p,k+3*p,i*j+6*p),(i*a+8*p,j+4*p,i*a+7*p))
    shapes = ((i*j,a,k),(i*a,b,j))
    signatures,covered = [],set()
    for index,call in enumerate(calls):
        fields = {'sequence','phase','scalar','order','transforms','shape','leading','alpha','beta','begin','end'}
        require(set(call)==fields|({'addresses'} if with_packing else set()), 'call fields')
        if with_packing:
            require(isinstance(call['addresses'],list) and len(call['addresses'])==3, 'source address coverage')
            for address in call['addresses']: packing.backend.address(address)
        for name in ('sequence','phase','scalar','order'): backend.natural(call[name],name)
        phase = 1 if index < 2 else 3
        stage = index%2
        require(call['sequence']==index and call['phase']==phase and call['scalar']==case['scalar'], 'call identity')
        require(call['order']==102 and call['transforms']==[111,111], 'unexpected order/transform')
        require(tuple(call['shape'])==shapes[stage] and tuple(call['leading'])==leading[stage], 'actual call shape/layout')
        require(all(type(v) is int for name in ('shape','leading','transforms') for v in call[name]), 'call numeric domain')
        require(call['alpha']==['3ff0000000000000','0000000000000000'] and
                call['beta']==['0000000000000000','0000000000000000'], 'actual coefficients')
        signatures.append({key:value for key,value in call.items() if key not in ('begin','end','addresses')})
        if events is None:
            require(call['begin'] is None and call['end'] is None, 'unobserved is not zero events')
            continue
        lo,hi = call['begin'],call['end']
        backend.natural(lo,'event start');backend.natural(hi,'event end')
        require(lo<=hi<=len(events['events']), 'event interval bounds')
        require(index==0 or calls[index-1]['end']<=lo, 'overlapping/reordered call intervals')
        loans = {}
        for cursor in range(lo,hi):
            require(cursor not in covered, 'event reused by two calls')
            covered.add(cursor)
            event = events['events'][cursor]
            require(event['phase']==10+phase and event['operation'] not in ('mark','shutdown_begin','shutdown_end'), 'wrong event attribution')
            op = event['operation']
            if event['ok'] and op in ('borrow','direct_borrow'):
                require(event['address'] not in loans,'duplicate call loan')
                loans[event['address']]=op
            if op in ('return','direct_return'):
                want = 'borrow' if op=='return' else 'direct_borrow'
                require(loans.pop(event['address'],None)==want, 'call returned an unrelated loan')
        require(not loans, 'loan escaped a CBLAS call')
    if events is not None:
        observed = backend.replay(events)
        require(observed['markers']==[11,12,13,14,18,19], 'source phase markers')
        for phase in (11,12,13,14):
            require(observed['phases'][phase]['end']['borrowed_capacity_bytes']==0, 'borrow escaped source phase')
        required = {index for index,event in enumerate(events['events'])
                    if event['phase'] in (11,12,13,14) and event['operation']!='mark'}
        require(required==covered, 'backend event has no actual CBLAS call')
    return signatures


def check_allocation(row,case,cleanup='finally'):
    allocation,cost = row['allocation'],row['costs']
    objects.balanced(allocation)
    require(allocation['variant']=='production_shared', 'different Unit implementation')
    require(cleanup in ('finally','unit-catch'), 'unsupported cleanup')
    check_surrounding_objects(allocation,row['implementation'],row['scope'],cleanup)
    objects.nonnegative_counts(cost,set(cost)-{'checksum','observed'})
    require(cost['elapsed_ns']==0, 'operation clocks must be disabled')
    require(cost['repetitions']==row['repetitions'], 'cost repetition domain')
    require(row['implementation'] in ('generated','c','failure'), 'implementation')
    expected,d = objects.costs(case,row['scope'],row['repetitions'])
    require(all(cost[name]==value for name,value in expected.items()), 'arena/copy/write cost')
    cold = allocation['phases']['cold']
    require(cold['closed_arena_cycles']==cold['arena_finalizers']==1 and cold['arena_allocations']==cold['arena_frees']==6,
            'missing complete cold source operation')
    require(cold['arena_metadata_allocations']==2 and cold['arena_peak_bytes']==d['peak'] and
            cold['arena_written_bytes']==d['init']+d['writes'] and cold['arena_copied_bytes']==d['packed'], 'cold data cost')
    require(cold['kinds']['persistent_unit']['allocations']==1 and cold['kinds']['persistent_unit']['retained_returns']==35 and
            cold['kinds']['ffi_ok']['allocations']==1 and cold['kinds']['arena_external']['allocations']==1, 'cold object cost')
    if row['implementation']=='failure':
        require(row['scope']==0 and row['repetitions']==1, 'failure domain')
        require(allocation['tracked_peak_bytes']==56 and cost['data_allocations']==cost['data_frees']==6 and cost['live_bytes_after']==0,
                'failed operation cleanup')
        run=allocation['phases']['run']
        require(run['arena_finalizers']==run['closed_arena_cycles']==1 and
                run['arena_allocations']==run['arena_frees']==6 and run['arena_metadata_allocations']==2 and
                run['arena_written_bytes']==cost['written_bytes'] and run['arena_copied_bytes']==cost['copied_bytes'],
                'missing propagated failure/finalizer')
        for kind in objects.KINDS:
            item=run['kinds'][kind]
            count=int(kind!='persistent_unit')
            size=24 if kind=='arena_external' else 16*count
            require(item['allocations']==item['final_releases']==count and
                    item['bytes']==item['released_bytes']==size, 'failure selected object cost')
        require(run['kinds']['persistent_unit']['retained_returns']==26 and
                cost['checksum']==cost['observed']=='0000000000000000', 'failure observation boundary')
        return
    scope,reps = row['scope'],row['repetitions']
    require(cost['checksum']!='0000000000000000', 'missing output checksum')
    kinds = allocation['phases']['run']['kinds']
    if row['implementation']=='generated':
        ffi = reps if scope==0 else 0
        external = reps if scope==0 else 0
        fallback = reps if scope==0 and cleanup=='finally' else 0
        expected_kinds = {'ffi_ok':(ffi,16*ffi),'arena_external':(external,24*external),
                          'generated_ctor':(2+fallback,48+16*fallback),'control':(1,16),
                          'ffi_error':(0,0),'persistent_unit':(0,0)}
        require(allocation['tracked_peak_bytes']==88, 'generated object peak')
        require(kinds['persistent_unit']['retained_returns']==(35*reps if scope==0 else 4*reps), 'persistent result use')
    else:
        expected_kinds = dict.fromkeys(objects.KINDS,(0,0))
        require(allocation['tracked_peak_bytes']==40 and kinds['persistent_unit']['retained_returns']==0, 'C object scope')
    for kind,(count,size) in expected_kinds.items():
        item = kinds[kind]
        require(item['allocations']==item['final_releases']==count and item['bytes']==item['released_bytes']==size,
                'unexpected selected object cost: '+kind)
    end = allocation['phases']['run' if scope==0 else 'cleanup']
    require(end['closed_arena_cycles']==d['lives'] and end['arena_allocations']==end['arena_frees']==6*d['lives'] and
            end['arena_metadata_allocations']==2*d['lives'], 'operation data lifecycle')
    require(end['arena_finalizers']==(d['lives'] if row['implementation']=='generated' else 0), 'operation finalizer')
    require(end['arena_written_bytes']==cost['written_bytes'] and end['arena_copied_bytes']==cost['copied_bytes'], 'operation data traffic')


def check_surrounding_objects(allocation,implementation,scope,cleanup='finally'):
    """Unexpected balanced churn outside the selected run is still a cost."""
    def item(count=0,size=16,release=None,retained=0):
        release=count if release is None else release
        return dict(allocations=count,bytes=count*size,final_releases=release,
                    released_bytes=release*size,retained_returns=retained)

    empty={kind:item() for kind in objects.KINDS}
    expected={'startup':dict(empty),'cold':dict(empty),'setup':dict(empty),'cleanup':dict(empty)}
    for kind in ('ffi_ok','generated_ctor','control'):expected['cold'][kind]=item(1)
    if cleanup=='unit-catch':expected['cold']['generated_ctor']=item()
    expected['cold']['arena_external']=item(1,24)
    expected['cold']['persistent_unit']=item(1,release=0,retained=35)
    expected['setup']['control']=item(1)
    expected['cleanup']['control']=item(1)
    if implementation=='generated' and scope==1:
        expected['setup']['ffi_ok']=item(1)
        expected['setup']['arena_external']=item(1,24,release=0)
        expected['setup']['persistent_unit']=item(retained=21)
        expected['cleanup']['arena_external']=item(0,24,release=1)
        expected['cleanup']['persistent_unit']=item(retained=10)
        expected['cleanup']['control']=item(2)
    for phase,kinds in expected.items():
        require(allocation['phases'][phase]['kinds']==kinds, 'selected object cost outside run: '+phase)
    zero_phases=('startup','setup','run') if scope==1 else ('startup','setup','cleanup')
    for phase in zero_phases:
        require(all(allocation['phases'][phase][key]==0 for key in objects.ARENA_FIELDS), 'arena cycle in wrong phase')


def check_backend_pair(left,right):
    # Addresses differ between fresh processes. Replay compares requested/live
    # bytes, event counts, phase boundaries and releases, not virtual addresses.
    require(backend.replay(left)==backend.replay(right), 'generated/C backend cost mismatch')


def check_input(command,wire):
    require(command['stdin']=={'bytes':len(wire),'sha256':hashlib.sha256(wire).hexdigest()}, 'actual kernel input')


def verify(path):
    if not __debug__: raise ValueError('Run without -O: the inherited object verifier uses assertions')
    reader = backend.Reader(path)
    return verify_reader(reader,allow_build_tree=reader.zip is None)


def verify_reader(r,*,allow_build_tree=False):
    if not __debug__: raise ValueError('Run without -O: the inherited object verifier uses assertions')
    record = r.json('record.json')
    require(type(record['schema']) is int and record['schema'] in (1,2,3) and
            record['kind']=='source-workspace-costs', 'record schema')
    with_packing = record['schema']==3
    with_allocator = record['schema']==2 or (with_packing and 'lean_allocator' in record)
    require(('packing' in record)==with_packing, 'packing needs schema 3')
    configurations = allocator.configurations(with_allocator)
    backends = tuple(configurations)
    diagnostic = tuple(b for b in backends if configurations[b]['backend']=='diagnostic')
    if with_allocator:
        require(record['configurations']==configurations, 'source configuration coverage')
    else:
        require('lean_allocator' not in record and 'configurations' not in record, 'allocator needs schema 2')
    require(record['claims']==CLAIMS and all(type(v) is bool for v in record['claims'].values()), 'unsupported claim')
    if not allow_build_tree:
        require(r.names==set(record['files'])|{'record.json'}, 'archive must contain only compact evidence')
    visible = {n for n in r.names if '.lake' not in Path(n).parts and 'openblas_include' not in Path(n).parts
               and n not in record['binaries']}
    require(visible==set(record['files'])|{'record.json'}, 'compact file inventory')
    for name,item in record['files'].items():
        data = r.read(name)
        require(len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256'], 'file fingerprint: '+name)
    for name,item in record['binaries'].items():
        if name in r.names:
            data = r.read(name)
            require(len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256'], 'binary fingerprint')
    for name,digest in record['inputs'].items():
        require(hashlib.sha256(r.read('source/'+name)).hexdigest()==digest, 'source fingerprint')
    require(record['environment']['LEAN_NUM_THREADS']=='1' and record['environment']['OPENBLAS_NUM_THREADS']=='1', 'build thread profile')
    calibration = Prefixed(r,record['backend_record'])
    calibrated = calibration.json('record.json')
    if with_packing:
        require(calibrated['schema']==2, 'source packing needs actual footprint calibration')
        packing_calibration = packing.backend.verify_reader(calibration)
        kernels = packing.backend.calibration(calibrated['builds']['stock']['unroll'])['kernels']
    else:
        backend.verify_reader(calibration)
    require(record['backend_archives']=={k:calibrated['builds'][k]['archive_sha256'] for k in ('stock','diagnostic')}, 'uncalibrated backend')
    for name,digest in record['backend_archives'].items():
        require(record['external_inputs'][record['prefixes'][name]+'/lib/libopenblas.a']==digest, 'linked archive fingerprint')
    for name in ('observer.c','observer.h','wrappers.c','patch.py'):
        relative = 'experiments/openblas_workspace/'+name
        require(record['inputs'][relative]==calibrated['repository']['inputs'][relative]['sha256'], 'changed observer source')
    if with_packing:
        for name in ('observer.c','observer.h','patch.py','calibrate.c'):
            relative = 'experiments/openblas_packing/'+name
            require(record['inputs'][relative]==calibrated['repository']['inputs'][relative]['sha256'],
                    'changed packing source')
    if with_allocator: allocator.check_calibration(r,record,Prefixed)
    cases,repetitions = check_cases(r.json('cases.json'),record['selection'])
    expected_binaries = {f'programs/{name}/{b}/{file}' for name,b,file in
        itertools.product(cases,backends,('canonical','.lake/build/bin/audit'))}
    require(set(record['binaries'])==expected_binaries, 'executable fingerprint coverage')
    for item in record['binaries'].values():
        backend.natural(item['bytes'],'executable size',positive=True)
        require(isinstance(item['sha256'],str) and len(item['sha256'])==64 and
                all(c in '0123456789abcdef' for c in item['sha256']), 'executable digest')
    for path in record['tools'].values(): require(path in record['external_inputs'], 'compiler executable fingerprint')
    observations = r.json('observations.json')
    all_rows = observations['rows']+observations['failures']
    keys = [(x['case'],x['backend'],x['implementation'],x['scope'],x['repetitions']) for x in all_rows]
    required = set(itertools.product(cases,backends,('generated','c'),(0,1),repetitions))
    required |= {(name,b,'failure',0,1) for name,b in itertools.product(cases,backends)}
    require(len(keys)==len(set(keys)) and set(keys)==required, 'observation coverage')
    require(all(type(x[k]) is int for x in all_rows for k in ('scope','repetitions')), 'observation numeric domain')
    signatures,allocator_summaries,packing_summaries = {},{},{}
    styles = {(name,b):objects.cleanup_style(r.read,'programs/'+name+'/'+b+'/')
              for name,b in itertools.product(cases,backends)}
    if 'unit-catch' in styles.values():
        require('experiments/native_cleanup.py' in record['inputs'], 'missing cleanup input')
    for key,row in zip(keys,all_rows):
        require((row['workspace'] is not None)==(row['backend'] in diagnostic), 'stock/diagnostic distinction')
        require(('lean_allocator' in row)==with_allocator, 'allocator observation domain')
        require(('packing' in row)==with_packing, 'packing observation domain')
        check_allocation(row,cases[row['case']],styles[row['case'],row['backend']])
        signatures[key] = check_calls(row['calls'],row['workspace'],cases[row['case']],row['repetitions'],
                                      with_packing=with_packing)
        if with_packing:
            require((row['packing'] is not None)==(row['backend'] in diagnostic), 'stock packing is unavailable')
            packing_summaries[key] = packing.replay(row['calls'],row['packing'],row['workspace'],
                                                     kernels,packing_calibration['metadata'])
        if with_allocator:
            allocator_summaries[key] = allocator.replay(row['lean_allocator'],row['allocation'],
                                                       configurations[row['backend']]['runtime'])
    lookup = dict(zip(keys,all_rows))
    for name in cases:
        reference = lookup[(name,backends[0],'failure',0,1)]
        for b in backends[1:]:
            other = lookup[(name,b,'failure',0,1)]
            require(reference['allocation']==other['allocation'] and
                    {k:v for k,v in reference['costs'].items() if k!='process_maxrss_kib'}==
                    {k:v for k,v in other['costs'].items() if k!='process_maxrss_kib'}, 'failure backend mismatch')
            require(signatures[(name,backends[0],'failure',0,1)]==signatures[(name,b,'failure',0,1)], 'failure call mismatch')
    for name,scope,reps in itertools.product(cases,(0,1),repetitions):
        group = [(name,b,impl,scope,reps) for b,impl in itertools.product(backends,('generated','c'))]
        reference = {k:v for k,v in lookup[group[0]]['costs'].items() if k!='process_maxrss_kib'}
        require(all({k:v for k,v in lookup[key]['costs'].items() if k!='process_maxrss_kib'}==reference for key in group), 'output/explicit cost mismatch')
        require(all(signatures[key]==signatures[group[0]] for key in group), 'actual CBLAS call mismatch')
        for impl in ('generated','c'):
            require(all(lookup[(name,backends[0],impl,scope,reps)]['allocation']==
                        lookup[(name,b,impl,scope,reps)]['allocation'] for b in backends[1:]), 'backend changed selected Lean costs')
        for b in diagnostic:
            check_backend_pair(lookup[(name,b,'generated',scope,reps)]['workspace'],
                               lookup[(name,b,'c',scope,reps)]['workspace'])
            check_backend_pair(lookup[(name,diagnostic[0],'generated',scope,reps)]['workspace'],
                               lookup[(name,b,'generated',scope,reps)]['workspace'])
    if with_allocator:
        for name,impl,scope,reps in ((n,i,s,r) for n in cases for i,s,r in
                [('failure',0,1)]+list(itertools.product(('generated','c'),(0,1),repetitions))):
            require(allocator_summaries[(name,'stock-diagnostic2',impl,scope,reps)]==
                    allocator_summaries[(name,'diagnostic-diagnostic2',impl,scope,reps)],
                    'backend changed allocator phase costs')
    if with_packing:
        for name,impl,scope,reps in ((n,i,s,r) for n in cases for i,s,r in
                [('failure',0,1)]+list(itertools.product(('generated','c'),(0,1),repetitions))):
            reference = packing_summaries[(name,diagnostic[0],impl,scope,reps)]
            for b in diagnostic:
                require(packing_summaries[(name,b,impl,scope,reps)]==reference,
                        'Lean variant changed backend packing')
                if impl=='generated':
                    require(packing_summaries[(name,b,'c',scope,reps)]==reference,
                            'generated/C packing cost mismatch')
    commands = r.json('commands.json')
    samples = [c for c in commands if c['phase']=='source_workspace']
    require(len(samples)==len(all_rows), 'raw sample command coverage')
    raw_keys = set()
    for command in samples:
        require(command['compiler_environment']['LEAN_NUM_THREADS']=='0', 'observation worker profile')
        if with_allocator:
            require(command['compiler_environment']['LEAN_MAIN_USE_THREAD']=='1', 'allocator entry thread profile')
            require(not command['stderr'].strip(), 'unexpected allocator execution diagnostic')
        argv = command['command']; impl,scope,reps = argv[-4:-1]
        matches = [key for key in keys if f'/programs/{key[0]}/{key[1]}/' in argv[0] and key[2:]==(impl,int(scope),int(reps))]
        require(len(matches)==1 and matches[0] not in raw_keys and argv[-1]=='1' and command['returncode']==0, 'raw command identity')
        key = matches[0];raw_keys.add(key);row=lookup[key]
        require(command['context']=={'case':key[0],'backend':key[1]}, 'sample context')
        parsed = [json.loads(line) for line in command['stdout'].splitlines()]
        want = [row['costs'],row['allocation'],row['calls']]+([row['workspace']] if row['workspace'] is not None else [])
        if with_packing and row['packing'] is not None: want.append(row['packing'])
        if with_allocator: want.append(row['lean_allocator'])
        require(parsed==want, 'raw/parsed correspondence')
    require(all(c['returncode']==0 or (c['phase']=='frontend_capture' and c['returncode']==1 and 'E_CAPTURED' in c['stderr']) for c in commands), 'unexpected command failure')
    for name,b in itertools.product(cases,backends):
        prefix = f'programs/{name}/{b}/'
        for phase in ('frontend_capture','public_check','public_build','public_execute','kernel_emit','kernel_failure_emit','audit_build','linked_symbols','linked_libraries'):
            match = [c for c in commands if c['phase']==phase and c['context']=={'case':name,'backend':b}]
            require(len(match)==1, 'public/build command provenance: '+phase)
            command = match[0]
            if phase not in ('kernel_emit','kernel_failure_emit'):
                require(any('/'+prefix in a or a.endswith('/'+prefix.rstrip('/'))
                            for a in command['command']+[command['cwd']]), 'command path/context mismatch')
            if phase=='public_build':
                index = match[0]['command'].index('--openblas-prefix')
                require(match[0]['command'][index+1]==record['prefixes']['stock'], 'public build must use unchanged stock backend')
            if phase in ('frontend_capture','public_check','public_build'):
                require(command['command'][0]==record['tools']['frontend'], 'actual frontend executable')
            if phase in ('public_check','public_build'):
                require(command['compiler_environment']['VASTITAS_KERNEL']==record['tools']['kernel'], 'actual independent checker')
            if phase=='public_execute':
                require(match[0]['stdout'].strip()=='0', 'canonical source output')
                require(command['compiler_environment']['LEAN_NUM_THREADS']=='0', 'canonical worker profile')
            if phase=='linked_symbols':
                require(('vobs_cursor' in match[0]['stdout'])==(b in diagnostic), 'linked observer symbol')
                if with_packing:
                    require(('vpack_dump' in command['stdout'])==(b in diagnostic), 'linked packing observer')
                if with_allocator:
                    require('mi_stats_get' in command['stdout'],
                            'linked source allocator observer')
            if phase in ('kernel_emit','kernel_failure_emit'):
                file = prefix+('response.json' if phase=='kernel_emit' else 'failure-response.json')
                require(json.loads(match[0]['stdout'])==r.json(file), 'exact kernel response')
                wire = r.read(prefix+'package/wire.json') if phase=='kernel_emit' else json.dumps(r.json(prefix+'failure-wire.json')).encode()
                check_input(command,wire)
                require(command['command']==[record['tools']['kernel'],'emit'], 'kernel emit invocation')
        for response_name,source_name in (('response.json','Generated.lean'),('failure-response.json','GeneratedFailure.lean')):
            response = r.json(prefix+response_name)
            require(response['ok'] is True and response['version']==8 and response['numerical_runtime'] is True and
                    response['lean_source'].encode()==r.read(prefix+source_name), 'exact checked generated source')
        ffi = r.read(prefix+'native/ffi.c')
        for token in (b'lean_obj_once(&unit_success, &success_once, initialize_success)',b'lean_mark_persistent(result)',
                      b'audit_shared_create()',b'audit_shared_return(result)',b'bench_report(); audit_report(); source_workspace_report();'):
            require(token in ffi, 'actual production helper/report connection')
        require(b'lean_alloc_ctor' in r.read(prefix+'Emitted.c') and b'lean_is_exclusive' in r.read(prefix+'Emitted.c'), 'emitted caller inspection')
        native = r.read(prefix+'native/storage.c')
        require(b'clocks disabled for cost observation' in native and native.count(b'source_workspace_begin(')==2 and
                native.count(b'source_workspace_end();')==2, 'actual CBLAS bracketing')
        require(record['prefixes'][configurations[b]['backend']].encode() in r.read(prefix+'lakefile.lean'), 'private backend link')
        if with_packing:
            require(r.read(prefix+'native/bridge.c')==r.read('source/experiments/source_workspace/bridge.c') and
                    r.read(prefix+'native/packing_observer.h')==calibration.read('inputs/repository/experiments/openblas_packing/observer.h'),
                    'actual source packing observer')
            require(b'-DSOURCE_WORKSPACE_PACKING=1' in r.read(prefix+'native/lakefile.lean'), 'packing bridge compilation')
            for arguments in (b'0,o,ta,tb,m,n,k,lx,ly,lz,a,0.0,b,0.0,x,y,z',
                              b'1,o,ta,tb,m,n,k,lx,ly,lz,av[0],av[1],bv[0],bv[1],x,y,z'):
                require(native.count(b'source_workspace_begin('+arguments+b');')==1, 'actual CBLAS address capture')
        if with_allocator: allocator.check_program(r,record,prefix,configurations[b])
    summaries = []
    counts = Counter()
    for row in all_rows:
        if row['workspace'] is not None:
            counts.update(e['operation'] for e in row['workspace']['events'])
    for name in sorted(cases):
        row = lookup[(name,diagnostic[0],'generated',1,repetitions[-1])]
        observed = backend.replay(row['workspace'])
        summaries.append({'case':name,'buffer_bytes':observed['buffer_bytes'],'peak':observed['peak'],
            'before_shutdown':observed['before_shutdown'],
            'cold_counts':observed['phases'][11]['counts'],f'reuse_{repetitions[-1]}_counts':observed['phases'][13]['counts']})
    summary = {'status':'passed','selection':record['selection'],'cases':len(cases),'records':len(observations['rows']),
            'failure_cleanups':len(observations['failures']),'canonical_executions':len(backends)*len(cases),
            'diagnostic_processes':len(all_rows)//2,'actual_cblas_calls':sum(len(row['calls']['calls']) for row in all_rows),
            'diagnostic_event_counts':dict(counts),f'reuse_{repetitions[-1]}_generated_workspace':summaries,'claims':CLAIMS}
    if with_allocator:
        summary['lean_allocator'] = dict(claims=allocator.CLAIMS,variants=list(allocator.VARIANTS),
            snapshots=10*len(all_rows),observations=[dict(case=key[0],backend=key[1],implementation=key[2],
            scope=key[3],repetitions=key[4],**value) for key,value in allocator_summaries.items()])
    if with_packing:
        footprints = packing.check_footprints(r,record,all_rows,calibrated,kernels,commands)
        summary['packing'] = {'claims':packing.CLAIMS,'observed_footprints':footprints,
            'metadata':packing_calibration['metadata'],
            f'reuse_{repetitions[-1]}_generated':[{'case':name,**packing_summaries[(name,diagnostic[0],'generated',1,repetitions[-1])]}
                                  for name in sorted(cases)]}
    return summary


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('record',type=Path)
    print(json.dumps(verify(parser.parse_args().record),indent=2))
