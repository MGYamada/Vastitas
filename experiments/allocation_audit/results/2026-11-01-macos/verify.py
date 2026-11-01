"""Independent consistency audit; does not rebuild or import the experiment."""
from collections import Counter
import hashlib
import io
import itertools
import json
from pathlib import Path
import subprocess
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
HEAD = 'df16b7010cd4113bd3d832d5be68c32d6bd93c0b'
SHA = '740f6e6a142ae1bb67e5284892cd9daf45edf91126e127c5802ddfec711e2ae8'
raw = (HERE/'evidence.zip').read_bytes()
assert len(raw) == 690485 and hashlib.sha256(raw).hexdigest() == SHA
manifest = json.loads((HERE/'manifest.json').read_text())
assert (manifest['measured_head'],manifest['archive_bytes'],manifest['archive_sha256']) == (HEAD,len(raw),SHA)
with zipfile.ZipFile(io.BytesIO(raw)) as z:
    assert z.testzip() is None
    assert len(z.namelist()) == len(set(z.namelist())) == 401
    files = {name:z.read(name) for name in z.namelist()}
assert set(files) == {f['path'] for f in manifest['files']}
for item in manifest['files']:
    data = files[item['path']]
    assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256']
for name in ('allocations.json','cases.json','environment.json','status.json','openblas-build.json'):
    assert (HERE/name).read_bytes() == files[name]
load = lambda name: json.loads(files[name])
env = load('environment.json')
assert env['head'] == HEAD and env['git_status'] == '' and env['recorded_inputs_unchanged']
source_count = 0
for path,digest in env['inputs'].items():
    prefix = '/private/tmp/vastitas-allocation-audit/'
    if path.startswith(prefix) and not path.endswith(('/vastitas','/vastitas-kernel')):
        rel = path[len(prefix):]
        data = files['source/'+rel]
        assert hashlib.sha256(data).hexdigest() == digest
        original = subprocess.run(['git','show',HEAD+':'+rel],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        assert data == original
        source_count += 1
    elif path.endswith('/include/lean/lean.h'):
        assert hashlib.sha256(files['pinned-lean.h']).hexdigest() == digest
    elif path.endswith('/include/lean/config.h'):
        assert hashlib.sha256(files['pinned-config.h']).hexdigest() == digest
assert source_count == 35 and len(env['inputs']) == 40
cases = {c['case']:c for c in load('cases.json')}
assert len(cases) == 4 and {(c['scalar'],c['pad']) for c in cases.values()} == set(itertools.product(range(2),repeat=2))
rows = load('allocations.json')
keys = {(r['case'],r['persistent'],r['scope'],r['repetitions'],r['implementation']) for r in rows}
assert len(rows) == len(keys) == 96
assert keys == set(itertools.product(cases,(False,True),(0,1),(1,2,17),('generated','c')))


def balanced(audit):
    assert audit['tracked_live_bytes'] == (16 if audit['persistent_experiment'] else 0)
    for kind in audit['phases']['run']['kinds']:
        records = [p['kinds'][kind] for p in audit['phases'].values()]
        retained = 1 if kind == 'persistent_unit' and audit['persistent_experiment'] else 0
        assert sum(x['allocations']-x['final_releases'] for x in records) == retained
        assert sum(x['bytes']-x['released_bytes'] for x in records) == 16*retained


for row in rows:
    c = cases[row['case']]; n=row['repetitions']; scope=row['scope']; persistent=row['persistent']
    audit=row['audit']; balanced(audit)
    assert audit['persistent_experiment'] == persistent
    phase=audit['phases']['run']; kinds=phase['kinds']
    if row['implementation']=='generated':
        ffi = (n if persistent else 36*n) if scope==0 else (0 if persistent else 4*n)
        external = n if scope==0 else 0
        extra = n if scope==0 and persistent else 0
        assert kinds['ffi_ok']['allocations'] == kinds['ffi_ok']['final_releases'] == ffi
        assert kinds['ffi_ok']['bytes'] == 16*ffi
        assert kinds['arena_external']['allocations'] == kinds['arena_external']['final_releases'] == external
        assert kinds['arena_external']['bytes'] == 24*external
        assert kinds['generated_ctor']['allocations'] == 2+extra
        assert kinds['generated_ctor']['bytes'] == 48+16*extra
        assert kinds['control']['allocations'] == 1 and kinds['control']['bytes'] == 16
        assert kinds['persistent_unit']['retained_returns'] == ((35*n if scope==0 else 4*n) if persistent else 0)
    else:
        assert all(kinds[k]['allocations']==0 for k in ('ffi_ok','arena_external','generated_ctor','control'))
    cold = audit['phases']['cold']
    assert cold['closed_arena_cycles']==cold['arena_finalizers']==1
    assert cold['arena_allocations']==cold['arena_frees']==6
    assert cold['arena_metadata_allocations']==2
    assert cold['kinds']['ffi_ok']['allocations']==(1 if persistent else 36)
    assert cold['kinds']['persistent_unit']['allocations']==int(persistent)
    assert cold['kinds']['arena_external']['allocations']==1
    i,k,j,a,b,p=(c[x] for x in ('i','k','j','a','b','pad')); w=16 if c['scalar'] else 8
    dims=[(i,k*j),(k,a),(j,b),(i*j,k),(i*j,a),(i*a,b),(i*a,j)]
    capacity=[(index+1)*p+(r+(index+2)*p)*col+3*p for index,(r,col) in enumerate(dims)]
    peak=w*(sum(capacity[:6])-capacity[3]+max(capacity[3],capacity[6]))
    packed=w*(i*k*j+i*j*a); written=w*(i*k*j+2*i*j*a+i*a*b)
    init=peak+w*(i*k*j+k*a+j*b+6); lives=n if scope==0 else 1
    cost=row['costs']
    expected=dict(data_allocations=6*lives,data_frees=6*lives,live_bytes_after=0,peak_data_bytes=peak,
        written_bytes=init*lives+written*n,copied_bytes=packed*n,metadata_allocations=2*lives,peak_metadata_bytes=280,
        timed_data_allocations=6*n if scope==0 else 0,timed_data_frees=6*n if scope==0 else 0,
        timed_written_bytes=(init+written)*n if scope==0 else written*n,timed_copied_bytes=packed*n,
        timed_metadata_allocations=2*n if scope==0 else 0,selected_pack_calls_timed=0,blas_calls_timed=0)
    for name,value in expected.items(): assert cost[name]==value,(row['case'],name,cost[name],value)
    assert cold['arena_peak_bytes']==peak and cold['arena_written_bytes']==init+written and cold['arena_copied_bytes']==packed
    end=audit['phases']['run' if scope==0 else 'cleanup']
    assert end['closed_arena_cycles']==lives and end['arena_allocations']==end['arena_frees']==6*lives
    assert end['arena_written_bytes']==cost['written_bytes'] and end['arena_copied_bytes']==cost['copied_bytes']
    counterpart=next(x for x in rows if all(x[field]==row[field] for field in ('case','persistent','scope','repetitions')) and x['implementation']!=row['implementation'])
    assert {k:v for k,v in cost.items() if k not in ('elapsed_ns','process_maxrss_kib')} == {k:v for k,v in counterpart['costs'].items() if k not in ('elapsed_ns','process_maxrss_kib')}
    assert cost['checksum']!='0000000000000000'
commands=load('commands.json')
normal=[c for c in commands if c['phase']=='allocation_audit']
assert len(normal)==96
for row,command in zip(rows,normal):
    assert command['returncode']==0
    cost,audit=map(json.loads,command['stdout'].splitlines())
    assert cost==row['costs'] and audit==row['audit']
    assert command['command'][-4:]==[row['implementation'],str(row['scope']),str(row['repetitions']),'1']
failures=[c for c in commands if c['phase']=='failure_cleanup']
assert len(failures)==8
for command in failures:
    assert command['returncode']==0
    cost,audit=map(json.loads,command['stdout'].splitlines()); balanced(audit)
    assert cost['data_allocations']==cost['data_frees']==6 and cost['live_bytes_after']==0
    assert audit['phases']['run']['kinds']['ffi_error']['allocations']==1
    assert audit['phases']['run']['arena_finalizers']==1
threads=[c for c in commands if c['phase']=='persistent_thread_test']
assert len(threads)==4
for command in threads:
    assert command['returncode']==0
    assert json.loads(command['stdout'])==dict(persistent_thread_test='passed',workers=8,initializations=1,calls=8001)
assert all(c['phase']=='frontend_capture' and c['returncode']==1 and 'E_CAPTURED' in c['stderr'] for c in commands if c['returncode'])
counts=Counter(c['phase'] for c in commands)
assert all(counts[phase]==8 for phase in ('frontend_capture','public_check','public_build','public_execute','kernel_emit','kernel_failure_emit','audit_build'))
for case in cases:
    for variant in ('fresh','persistent'):
        prefix=case+'/'+variant+'/'
        response=load(prefix+'response.json');failure=load(prefix+'failure-response.json')
        assert response['ok'] and failure['ok'] and response['version']==failure['version']==8
        assert response['lean_source'].encode()==files[prefix+'Generated.lean']
        assert failure['lean_source'].encode()==files[prefix+'GeneratedFailure.lean']
        assert b'lean_is_exclusive' in files[prefix+'Emitted.c'] and b'lean_alloc_ctor' in files[prefix+'Emitted.c']
        assert b'if error.toString != "E_NATIVE_EXPECT: stored bit pattern differs"' in files[prefix+'Main.lean']
assert load('status.json')==dict(status='passed',rows=96,performance='not measured')
print(json.dumps(dict(status='passed',members=len(files),sources_exact_git=source_count,allocation_records=96,
                     output_cost_pairs=48,failure_cleanups=8,thread_processes=4,thread_calls_each=8001),indent=2))
