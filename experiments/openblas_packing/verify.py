#!/usr/bin/env python3
"""Replay packing source/destination spans, unchanged objects and exact outputs.

Reads records without extracting or executing their contents. Logical packed
payload is neither hardware traffic nor a bound on shortcut/whole-process costs.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import re
import struct
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from experiments.openblas_workspace import verify as workspace

require=workspace.require
natural=workspace.natural
PINS={
    'driver/others/memory.c':'3b5bedc19c4555de21fb0c649177d9be1545d28fc61a8cbcc475e4a9bffc9935',
    'driver/level3/level3.c':'c48438aa2339a40441906901616dd8bcc2a8122e6bc9e57d61b81841998290a1',
    'driver/level3/gemm.c':'4f434191599394697eb36040ced6a6a81d9746d8c71034a973137e10df89d959',
    'interface/gemm.c':'c4dcc9c213f54a4acddb559d8bd6effb4ad6fc4d9cd16aabfd04941fd2ee6107',
}
SHAPES=((0,5,7),(5,0,7),(5,7,0),(1,17,23),(17,1,23),(1,1,7),
        (2,2,2),(17,19,23),(2,50000,7),(3,5,2051),(2051,5,7),(256,256,256))
SIZES=(1,2,3,4,5,7,8,9,15,16,17,31,32,33,63,64,65,127,128,129,255,256,257)


def address(value):
    require(isinstance(value,str) and re.fullmatch(r'0x[0-9a-f]+',value), 'packing address')
    result=int(value,16)
    require(0<result<2**64 and result%8==0, 'packing address domain')
    return result


def calibration(unroll):
    require(set(unroll)=={'D_M','D_N','Z_M','Z_N'} and
            all(type(v) is int and v in (1,2,4,8,16) for v in unroll.values()), 'unroll domain')
    kernels=[]
    for scalar,components in (('D',1),('Z',2)):
        for side,axis in (('i','M'),('o','N')):
            if side=='i' and unroll[scalar+'_M']==unroll[scalar+'_N']: continue
            for form,transpose in (('n',0),('t',1)):
                kernels.append({'name':scalar.lower()+'gemm_'+side+form+'copy',
                                'width':unroll[scalar+'_'+axis],'components':components,'transpose':transpose})
    return {'kind':'kernel_calibration','cases':len(kernels)*len(SIZES)**2*2,
            'checked_output_words':sum(k['components'] for k in kernels)*sum(SIZES)**2*2,
            'kernels':sorted(kernels,key=lambda k:k['name'])}


def union_area(rectangles):
    """Exact union of bounded integer rectangles, without enumerating elements."""
    events={}
    for r,c,rows,cols in rectangles:
        events.setdefault(c,[]).append((r,r+rows,1))
        events.setdefault(c+cols,[]).append((r,r+rows,-1))
    active=Counter(); last=0; total=0
    for x,changes in sorted(events.items()):
        length=0; end=0
        for (a,b),count in sorted(active.items()):
            require(count>0,'rectangle coverage counter')
            length+=max(0,b-max(a,end)); end=max(end,b)
        total+=(x-last)*length; last=x
        for a,b,delta in changes:
            active[a,b]+=delta
            if not active[a,b]: del active[a,b]
    require(not active,'unfinished rectangle coverage')
    return total


def replay(packing,backing,kernels):
    workspace.replay(backing)
    require(set(packing)=={'kind','schema','observer_static_bytes','call_capacity','route_capacity','metadata','routes','calls'}
            and packing['kind']=='packing' and type(packing['schema']) is int and packing['schema']==1, 'packing envelope')
    require(packing['call_capacity']==16384 and packing['route_capacity']==256 and
            len(packing['calls'])<=16384 and len(packing['routes'])<=256,'packing capacity')
    natural(packing['observer_static_bytes'],'packing observer bytes',positive=True)
    meta=packing['metadata']
    require(set(meta)=={'pool_entries','memory_entry_bytes','memory_array_bytes','release_entry_bytes','release_array_bytes','declared_bytes'},'metadata fields')
    for name in set(meta)-{'declared_bytes'}: natural(meta[name],name,positive=True)
    declared=meta['declared_bytes']
    names={'memory','release_info','newmemory','new_release_info','release_pos','alloc_lock','base_address',
           'memory_initialized','memory_overflowed','hugetlb_allocated','gotoblas_initialized'}
    require(set(declared) in (names,names|{'hot_alloc','init_lock'}),'declared metadata coverage')
    for value in declared.values(): natural(value,'declared metadata size',positive=True)
    require(meta['memory_array_bytes']==meta['pool_entries']*meta['memory_entry_bytes']==declared['memory'] and
            meta['release_array_bytes']==meta['pool_entries']*meta['release_entry_bytes']==declared['release_info'], 'metadata array units')
    require(meta['release_entry_bytes']==24 and all(declared[k]==8 for k in ('newmemory','new_release_info','base_address')) and
            all(declared[k]==4 for k in ('release_pos','memory_initialized','memory_overflowed','hugetlb_allocated','gotoblas_initialized')), 'metadata ABI')
    events=backing['events']; previous=0
    by_name={k['name']:k for k in kernels}
    routes=packing['routes']; parts=[[] for _ in routes]
    for route in routes:
        require(set(route)=={'path','components','m','n','k','ta','tb','a','b','c','lda','ldb','ldc','before','after'}, 'route fields')
        for key in ('components','m','n','k','ta','tb','lda','ldb','ldc','before','after'): natural(route[key],key)
        require(route['path'] in ('empty','gemv','small','packed') and route['components'] in (1,2) and
                route['ta'] in (0,1,3) and route['tb'] in (0,1,3),'route domain')
        require(previous<=route['before']<=route['after']<=len(events),'route ordering')
        require(route['before'] and events[route['before']-1]['phase'] in (11,12,13), 'route phase')
        require(all(e['phase']==events[route['before']-1]['phase'] for e in events[route['before']:route['after']]),'route crosses phase')
        previous=route['after']
        require((not route['m'] or not route['n']) == (route['path']=='empty'),'empty route')
        if route['path']=='empty': require(route['before']==route['after'],'empty route performed workspace work')
        if route['path']=='gemv': require(route['components']==1 and route['k'] and (route['m']==1 or route['n']==1),'GEMV route')
        for key in ('a','b','c'): address(route[key])
        rowsa=route['k'] if route['ta']&1 else route['m']
        rowsb=route['n'] if route['tb']&1 else route['k']
        require(route['lda']>=rowsa and route['ldb']>=rowsb and route['ldc']>=route['m'],'route leading dimensions')
    cursor=0; loans={}; last_route=0
    for call in packing['calls']:
        require(set(call)=={'kernel','role','components','m','n','lda','source','destination','before','after','route'},'packing call fields')
        for key in ('role','components','m','n','lda','before','after','route'): natural(call[key],key)
        index=call['route']; require(last_route<=index<len(routes),'packing route index'); last_route=index
        route=routes[index]
        require(route['path']=='packed' and route['before']<=call['before']==call['after']<=route['after'], 'copy interval/route')
        require(cursor<=call['before']<=len(events),'copy ordering')
        while cursor<call['before']:
            event=events[cursor]; cursor+=1; ptr=int(event['address'],16)
            if event['operation']=='borrow' and event['ok']: loans[ptr]=event['bytes']
            if event['operation']=='return': require(loans.pop(ptr,None) is not None,'unknown packing loan return')
        require(call['role'] in (0,1) and call['m'] and call['n'] and call['components']==route['components'],'copy domain')
        require(call['kernel'] in by_name,'uncalibrated packing kernel')
        kernel=by_name[call['kernel']]; role=call['role']; prefix='d' if call['components']==1 else 'z'
        side='i' if role==0 and prefix+'gemm_incopy' in by_name else 'o'
        trans=(not (route['ta']&1)) if role==0 else bool(route['tb']&1)
        require(call['kernel']==prefix+'gemm_'+side+('t' if trans else 'n')+'copy' and
                kernel['components']==call['components'] and kernel['transpose']==int(trans),'packing role/kernel')
        width=8*call['components']; size=call['m']*call['n']*width
        target=address(call['destination']); source=address(call['source'])
        require(size<2**64 and target+size<2**64 and sum(a<=target and target+size<=a+b for a,b in loans.items())==1,'packing outside live loan')
        base=address(route['a' if role==0 else 'b']); ld=route['lda' if role==0 else 'ldb']
        require(call['lda']==ld and ld>0 and source>=base and (source-base)%width==0,'packing source alignment/stride')
        col,row=divmod((source-base)//width,ld)
        rows,cols=(call['n'],call['m']) if kernel['transpose'] else (call['m'],call['n'])
        logical=(route['m'],route['k']) if role==0 else (route['k'],route['n'])
        actual=logical[::-1] if route['ta' if role==0 else 'tb']&1 else logical
        require(row+rows<=actual[0] and col+cols<=actual[1],'packing outside input rectangle')
        require(all(target+size<=address(route[key]) or address(route[key])+extent<=target
                    for key,extent in [('a',(route['lda']*(route['m'] if route['ta']&1 else route['k']))*width),
                                       ('b',(route['ldb']*(route['k'] if route['tb']&1 else route['n']))*width),
                                       ('c',route['ldc']*route['n']*width)]),'packing aliases caller storage')
        parts[index].append((role,size,(row,col,rows,cols)))
    summaries=[]
    for route,items in zip(routes,parts):
        require(route['path']=='packed' or not items,'unexpected shortcut copy events')
        if route['path']=='packed' and route['k']:
            for role,area in ((0,route['m']*route['k']),(1,route['k']*route['n'])):
                require(union_area([rect for which,_,rect in items if which==role])==area,'incomplete input packing coverage')
        summaries.append({'path':route['path'],'calls':len(items),
                          'logical_payload_bytes':[sum(size for r,size,_ in items if r==role) for role in (0,1)]
                          if route['path'] in ('empty','packed') else None})
    return {'routes':summaries,'declared_metadata_bytes':sum(declared.values()),
            'observer_static_bytes':packing['observer_static_bytes']}


@lru_cache(maxsize=None)
def checksums(scalar,m,n,k,ta,tb,beta):
    def value(which,r,c): return ((r+2*c+which)%5-2,(2*r+c+which)%3-1 if scalar else 0)
    @lru_cache(maxsize=None)
    def dot(r,c):
        full=[0,0]; tail=[0,0]
        for t in range(15):
            ar,ai=value(0,t,r) if ta else value(0,r,t)
            br,bi=value(1,c,t) if tb else value(1,t,c)
            if ta==2: ai=-ai
            if tb==2: bi=-bi
            term=(ar*br-ai*bi,ar*bi+ai*br)
            for part in (0,1):
                full[part]+=term[part]
                if t<k%15: tail[part]+=term[part]
        old=value(2,r,c)
        return tuple((k//15)*full[p]+tail[p]+beta*old[p] for p in (0,1))
    shapes=((k,m) if ta else (m,k),(n,k) if tb else (k,n),(m,n))
    result=[]
    for which,(rows,cols) in enumerate(shapes):
        h=1469598103934665603; ld=rows+3; components=scalar+1
        for i in range(ld*cols*components+64):
            word=0x7ff8123456789abc
            if 32<=i<32+ld*cols*components:
                col,row=divmod((i-32)//components,ld)
                if row<rows:
                    val=value(which,row,col) if which<2 else dot(row%15,col%15)
                    word=struct.unpack('<Q',struct.pack('<d',float(val[(i-32)%components])))[0]
            h=((h^word)*1099511628211)%2**64
        result.append(f'{h:016x}')
    return result


def check_patch(reader):
    for name,pin in PINS.items():
        original=reader.read('inputs/upstream/'+name)
        require(hashlib.sha256(original).hexdigest()==pin,'upstream source pin: '+name)
        text=reader.read('inputs/upstream/diagnostic/'+name).decode()
        # Reverse the admitted hooks, then require the exact original bytes.
        if name=='driver/others/memory.c':
            require(all(text.count('#include "'+header+'"')==1 for header in
                        ('vobs-observer.c','vobs-wrappers.c','vpack-observer.c')),'observer include coverage')
            for entry in ('blas_memory_alloc','blas_memory_free','blas_memory_alloc_nolock','blas_memory_free_nolock','blas_shutdown'):
                require(len(re.findall(r'^void (?:\*)?vobs_real_'+entry+r'\(',text,re.M))==2,'workspace entry hook coverage')
            for op,count in (('malloc',7),('free',6),('mmap',14),('munmap',12)):
                require(len(re.findall(r'\bvobs_'+op+r'\(',text))==count,'backing hook coverage')
            text=text.replace('#include "vobs-observer.c"\n','').replace('\n#include "vobs-wrappers.c"\n','').replace('\n#include "vpack-observer.c"\n','')
            text=text.replace('vobs_real_blas_','blas_')
            text=re.sub(r'\bvobs_(malloc|free|mmap|munmap)\(',r'\1(',text)
        elif name=='driver/level3/gemm.c':
            require(text.count('#define VPACK_GEMM_PROFILE 1\n#include "level3.c"')==1,'GEMM-only packing activation')
            text=text.replace('#define VPACK_GEMM_PROFILE 1\n','')
        elif name=='driver/level3/level3.c':
            for op,role in (('I',0),('O',1)):
                require(len(re.findall(r'^#define '+op+r'COPY_OPERATION[^\n]+VPACK_CALL\('+str(role)+',',text,re.M))==2,'copy role hook coverage')
            text=text.replace('#include "../others/vpack.h"\n','')
            text,count=re.subn(r'VPACK_CALL\([01], (GEMM_[A-Z]+), ([^\n]*)\);',r'\1(\2);',text)
            require(count==4,'packing hook coverage')
        else:
            require(text.count('VPACK_ROUTE("empty")')==2 and text.count('VPACK_ROUTE("gemv")')==2 and
                    text.count('VPACK_ROUTE("small")')==2 and text.count('VPACK_ROUTE("packed")')==1,'route hook coverage')
            require(text.count('if ((args.m == 0) || (args.n == 0)) { VPACK_ROUTE("empty"); VPACK_END(); return; }')==2 and
                    text.count('  VPACK_ROUTE("packed");\n  buffer = (XFLOAT *)blas_memory_alloc(0);')==1 and
                    text.count(' blas_memory_free(buffer);\n VPACK_END();')==1,'route hook placement')
            require(len(re.findall(r'VPACK_ROUTE\("gemv"\);\n        GEMV\([^\n]+\);\n        VPACK_END\(\);',text))==2 and
                    len(re.findall(r'if\(GEMM_SMALL_MATRIX_PERMIT[^\n]+\{\n          VPACK_ROUTE\("small"\);',text))==2,'shortcut hook placement')
            text=text.replace('#include "../driver/others/vpack.h"\n','')
            text=text.replace('{ VPACK_ROUTE("empty"); VPACK_END(); return; }','return;')
            text=text.replace('VPACK_ROUTE("gemv");\n        ','').replace('\n        VPACK_END();','')
            text=text.replace('\n          VPACK_ROUTE("small");','').replace('\t  VPACK_END();\n','')
            text=text.replace('  VPACK_ROUTE("packed");\n','').replace('\n VPACK_END();','')
        require(text.encode()==original,'unapproved source instrumentation: '+name)


def verify(path): return verify_reader(workspace.Reader(path))


def check_footprints(reader,record,contracts,kernels,commands):
    expected={(v,s,c) for v in ('stock','diagnostic') for s in (False,True) for c in contracts}
    seen=set(); definitions={k['name']:k for k in kernels}
    for receipt in record['footprints']:
        contract=tuple(receipt['contract']); key=(receipt['variant'],receipt['sanitized'],contract)
        require(type(receipt['sanitized']) is bool and key in expected and key not in seen,'footprint coverage/duplicate')
        seen.add(key); kernel,m,n,lda=contract; definition=definitions[kernel]
        raw=json.loads(reader.read(receipt['stdout']))
        require(raw==receipt['result']=={'kind':'observed_kernel_footprint','kernel':kernel,'m':m,'n':n,'lda':lda,
                'checked_input_words':lda*(m if definition['transpose'] else n)*definition['components'],
                'checked_output_words':m*n*definition['components']},'observed kernel footprint')
        calls=[c for c in commands if c['stdout']==receipt['stdout']]
        name=receipt['variant']+'-calibration'+('-sanitized' if receipt['sanitized'] else '')
        require(len(calls)==1 and Path(calls[0]['argv'][0]).name==name and
                calls[0]['argv'][1:]==list(map(str,contract)),'observed footprint command')
    require(seen==expected,'missing observed footprint calibration')
    return {'contracts':len(contracts),'executions':len(seen)}


def check_command_diagnostics(reader, commands):
    for command in commands:
        diagnostics=reader.read(command['stderr']).decode(errors='replace')
        require(not any(marker in diagnostics for marker in
                        ('runtime error:', 'UndefinedBehaviorSanitizer', 'AddressSanitizer')),
                'sanitizer diagnostic in retained command')


def verify_reader(reader):
    record=reader.json('record.json')
    require(type(record['schema']) is int and record['schema'] in (1,2) and record['kind']=='diagnostic-openblas-packing','record schema')
    require(record['upstream']['version']=='0.3.34' and record['upstream']['sha256']==workspace.PIN,'release pin')
    require(set(record['files'])|{'record.json'}==reader.names,'record inventory')
    for name,entry in record['files'].items():
        data=reader.read(name)
        require(len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],'file fingerprint: '+name)
    for name,entry in record['repository']['inputs'].items():
        require(entry['snapshot']=='inputs/repository/'+name and
                hashlib.sha256(reader.read(entry['snapshot'])).hexdigest()==entry['sha256'],'input fingerprint: '+name)
    required={'experiments/openblas_packing/'+p for p in ('run.py','verify.py','patch.py','observer.c','observer.h','probe.c','calibrate.c')}
    required|={'experiments/openblas_workspace/'+p for p in ('run.py','verify.py','patch.py','observer.c','observer.h','wrappers.c','probe.c')}
    required|={'scripts/build_openblas.py','lean-kernel/native/storage.c','lean-kernel/native/storage.h',
               'lean-kernel/native/diagonal.c','lean-kernel/native/diagonal.h','lean-kernel/numerical/gemm.c','lean-kernel/numerical/gemm.h'}
    require(required<=record['repository']['inputs'].keys(),'required source snapshots')
    check_patch(reader)
    old,new=reader.json('stock-objects.json'),reader.json('diagnostic-objects.json')
    changed=sorted(p for p in old if old[p]!=new.get(p))
    allow={'driver/others/memory.o','interface/cblas_dgemm.o','interface/cblas_zgemm.o'}|{
        p for p in old if re.fullmatch(r'driver/level3/[dz]gemm_[ntrc]{2}\.o',p)}
    require(old.keys()==new.keys() and set(changed)==allow and len(allow)==23 and
            changed==record['upstream']['changed_objects'],'changed object boundary')
    require(len([p for p in old if p.startswith('kernel/')])>100,'missing kernel objects')
    commands=reader.json(record['commands']); labels={c['label']:c for c in commands}
    require(len(labels)==len(commands) and all(c['returncode']==0 for c in commands),'command receipts')
    check_command_diagnostics(reader, commands)
    require(record['builds']['stock']['unroll']==record['builds']['diagnostic']['unroll'],'changed kernel configuration')
    for variant in ('stock','diagnostic'):
        conf=reader.read('inputs/'+variant+'/Makefile.conf').decode()
        for scalar in ('D','Z'):
            for axis in ('M','N'):
                values=re.findall(rf'^{scalar}GEMM_UNROLL_{axis}=([0-9]+)$',conf,re.M)
                require(len(values)==1 and int(values[0])==record['builds'][variant]['unroll'][scalar+'_'+axis], 'unroll build receipt')
        for family in ('adapter','rectangle'):
            cmd=labels.get(variant+'-'+family+'-link',{})
            argv=cmd.get('argv',[])
            define='-DVOBS_DIAGNOSTIC' if family=='adapter' else '-DVPACK_DIAGNOSTIC'
            require((define in argv)==(variant=='diagnostic') and argv[-2:-1]==['-o'] and
                    Path(argv[-1]).name==variant+'-'+family,'link variant receipt')
            require(len([x for x in argv if x.endswith('/lib/libopenblas.a')])==1,'static backend link')
    wanted=calibration(record['builds']['stock']['unroll']); seen_cal=set()
    for c in record['calibrations']:
        key=(c['variant'],c['sanitized']); require(key in itertools.product(('stock','diagnostic'),(False,True)) and key not in seen_cal,'calibration identity')
        seen_cal.add(key); raw=json.loads(reader.read(c['stdout'])); require(raw==c['result'],'calibration raw receipt')
        label=c['variant']+'-calibration'+('-sanitized' if c['sanitized'] else '')
        require(labels[label]['stdout']==c['stdout'] and
                ('-fsanitize=address,undefined' in labels[label+'-link']['argv'])==c['sanitized'],'calibration command receipt')
        raw['kernels']=sorted(raw['kernels'],key=lambda k:k['name']); require(raw==wanted,'kernel coordinate/guard calibration')
    require(len(seen_cal)==4,'missing calibration')
    expected_cases={('adapter',('calibration',))}|{('adapter',tuple(map(str,(s,n,t)))) for s in range(2) for n in (0,2,32,256) for t in range(3)}|{
        ('rectangle',tuple(map(str,(s,*shape,ta,tb,b)))) for s in range(2) for shape in SHAPES for ta in range(3) for tb in range(3) for b in range(2)}
    expected={(v,r,f,c) for v in ('stock','diagnostic') for r in (1,2) for f,c in expected_cases}
    seen=set(); pairs={}; count=0; payload=[0,0]; route_counts=Counter(); metadata=set(); configs=set(); shortcuts=0
    actual_contracts=set()
    for run in record['runs']:
        key=(run['variant'],run['repeat'],run['family'],tuple(run['case']))
        require(key in expected and key not in seen,'run coverage/duplicate'); seen.add(key)
        rows=reader.json(run['parsed']); require(rows==[json.loads(line) for line in reader.read(run['stdout']).decode().splitlines()],'raw observation receipt')
        require(len(rows)==(3 if run['variant']=='diagnostic' else 1),'observation row count')
        receipt=[c for c in commands if c['stdout']==run['stdout']]
        require(len(receipt)==1 and receipt[0]['argv'][1:]==run['case'] and
                Path(receipt[0]['argv'][0]).name==run['variant']+'-'+run['family'],'run executable receipt')
        row=rows[0]; configs.add(row['configuration'])
        expected_routes=0
        if run['family']=='rectangle':
            s,m,n,k,ta,tb,beta=map(int,run['case'])
            require(set(row)=={'kind','configuration','scalar','m','n','k','ta','tb','beta','checksums','matrices'} and row['kind']=='gemm','rectangle envelope')
            require([row[x] for x in ('scalar','m','n','k','ta','tb','beta')]==[s,m,n,k,ta,tb,beta] and row['checksums']==checksums(s,m,n,k,ta,tb,beta),'coordinate reference output')
            shapes=((k,m) if ta else (m,k),(n,k) if tb else (k,n),(m,n))
            require(len(row['matrices'])==3,'matrix count')
            for matrix,(r,c) in zip(row['matrices'],shapes):
                require(set(matrix)=={'address','rows','cols','ld'} and (matrix['rows'],matrix['cols'],matrix['ld'])==(r,c,r+3),'actual matrix contract')
                address(matrix['address'])
            expected_routes=1
        elif run['case']==['calibration']:
            require(set(row)=={'kind','configuration','distinct','reuse'} and row['kind']=='calibration' and row['distinct'] is True and row['reuse'] is True,'workspace calibration')
        else:
            s,n,t=map(int,run['case']); expected_routes=3 if n else 0
            require(set(row)=={'kind','configuration','scalar','n','transform','kernel_calls','checksums','arena_data_bytes'} and
                    (row['scalar'],row['n'],row['transform'])==(s,n,t) and row['kind']=='gemm' and
                    row['kernel_calls']==expected_routes and row['checksums']==workspace.expected_checksums(s,n,t) and
                    row['arena_data_bytes']==3*((n+1)*n+2)*8*(s+1),'adapter result/reference')
        normalized={k:v for k,v in row.items() if k!='matrices'}
        pairkey=(run['repeat'],run['family'],tuple(run['case']))
        require(pairkey not in pairs or pairs[pairkey]==normalized,'stock/diagnostic result differs'); pairs[pairkey]=normalized
        if run['variant']=='diagnostic':
            summary=replay(rows[2],rows[1],wanted['kernels']); routes=rows[2]['routes']
            require(len(routes)==expected_routes,'actual CBLAS route coverage')
            if run['case']==['calibration']: workspace.check_calibration(workspace.replay(rows[1]))
            if run['family']=='rectangle':
                route=routes[0]; tr=(0,1,3) if s else (0,1,1)
                require([route[x] for x in ('components','m','n','k','ta','tb')]==[s+1,m,n,k,tr[ta],tr[tb]],'CBLAS argument reconstruction')
                require(all(route[key]==matrix['address'] and route['ld'+key]==matrix['ld'] for key,matrix in zip(('a','b','c'),row['matrices'])),'CBLAS input receipt')
            elif run['case']!=['calibration']:
                tr=(0,1,3) if s else (0,1,1)
                require(all([r[x] for x in ('components','m','n','k','ta','tb','lda','ldb','ldc')]==[s+1,n,n,n,tr[t],0,n+1,n+1,n+1] for r in routes),'adapter CBLAS contract')
            metadata.add(json.dumps(rows[2]['metadata'],sort_keys=True)); count+=len(rows[2]['calls'])
            actual_contracts.update(tuple(c[key] for key in ('kernel','m','n','lda')) for c in rows[2]['calls'])
            for r in summary['routes']:
                route_counts[r['path']]+=1
                if r['logical_payload_bytes'] is None: shortcuts+=1
                else:
                    for i in (0,1): payload[i]+=r['logical_payload_bytes'][i]
    require(seen==expected and len(configs)==1 and len(metadata)==1,'incomplete run/configuration coverage')
    result={'schema':record['schema'],'head':record['repository']['head'],'executions':len(seen),'pairs':len(pairs),
            'calibration_cases_per_binary':wanted['cases'],'unchanged_kernel_objects':len([p for p in old if p.startswith('kernel/')]),
            'packing_calls':count,'logical_packed_payload_bytes':payload,'routes':dict(route_counts),
            'shortcut_routes_without_payload_measurement':shortcuts,'metadata':json.loads(next(iter(metadata))),
            'timing':False,'hardware_traffic':False,'whole_process_memory':False,'controlled_host':False}
    if record['schema']==2:
        result['observed_footprints']=check_footprints(reader,record,actual_contracts,wanted['kernels'],commands)
    else:
        require('footprints' not in record,'footprints need schema 2')
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('record',type=Path)
    print(json.dumps(verify(parser.parse_args().record),indent=2))
