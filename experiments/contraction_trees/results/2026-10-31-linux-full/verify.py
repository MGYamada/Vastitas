"""Recheck this preserved run's source records, paired costs and statistics.
Run with Python 3; uses only the standard library and a temporary directory.
This verifies evidence consistency, not native refinement or performance acceptance.
"""
from pathlib import Path
from collections import Counter,defaultdict
import csv,hashlib,json,random,statistics,tempfile,zipfile
saved=Path(__file__).resolve().parent
archive=saved/'evidence.zip'
temporary=tempfile.TemporaryDirectory()
root=Path(temporary.name).resolve()
assert archive.stat().st_size==418479
assert hashlib.sha256(archive.read_bytes()).hexdigest()=='596a69ad396d60741d985fd0db75cf5c89bf2044c3c8d419f78fbebcf7cebcfa'
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None
 manifest=json.loads((saved/'artifact-manifest.json').read_text())
 assert {x['path'] for x in manifest['files']}==set(z.namelist())
 for entry in manifest['files']:
  data=z.read(entry['path']);assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256']
  dest=root/entry['path'];assert root in dest.resolve().parents
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
  retained=saved/entry['path']
  if retained.is_file():assert retained.read_bytes()==data
rows=list(csv.DictReader((root/'raw.csv').open()))
cases=json.loads((root/'cases.json').read_text());assert len(cases)==12
bycase={c['case']:c for c in cases}; order={c['case']:i for i,c in enumerate(cases)}
scopes=['lifecycle','reused_buffers','pack3_adapter','regroup3_adapter','first_blas','second_blas']
commands=json.loads((root/'commands.json').read_text())
env=json.loads((root/'environment.json').read_text())
assert env['toolchains']['git']['stdout'].strip()=='69eafbee74ca7cbecea74824d25e65d931f51a7c'
assert env['toolchains']['git_status']['stdout']=='' and env['leak_sanitizer']=='enabled'
assert env['recorded_inputs_unchanged'] is True
assert '--smoke' not in env['argv'] and env['argv'][env['argv'].index('--samples')+1]=='11'
assert env['argv'][env['argv'].index('--target-ms')+1]=='5'

def cost(row,c,scope):
 n=int(row['repetitions']);w=16 if c['scalar'] else 8;i,k,j,a,b,p=(c[x] for x in ('i','k','j','a','b','pad'))
 dims=[(i,k*j),(k,a),(j,b),(i*j,k),(i*j,a),(i*a,b),(i*a,j)]
 caps=[(v+1)*p+(r+(v+2)*p)*col+3*p for v,(r,col) in enumerate(dims)]
 cap=(sum(caps[:6])-caps[3]+max(caps[3],caps[6]))*w
 first=i*k*j*w;second=i*j*a*w;output=i*a*b*w
 writes=first+2*second+output;copies=first+second
 init=cap+(i*k*j+k*a+j*b+6)*w;life=scope=='lifecycle';lives=n if life else 1
 want={'data_allocations':6*lives,'data_frees':6*lives,'live_bytes_after':0,'peak_data_bytes':cap,'written_bytes':init*lives+writes*n,'copied_bytes':copies*n,'metadata_allocations':2*lives,'timed_data_allocations':6*n if life else 0,'timed_data_frees':6*n if life else 0,'timed_written_bytes':(init+writes)*n if life else writes*n,'timed_copied_bytes':copies*n,'timed_metadata_allocations':2*n if life else 0,'selected_pack_calls_timed':n if scope in ('pack3_adapter','regroup3_adapter') else 0,'blas_calls_timed':n if scope in ('first_blas','second_blas') else 0}
 for key,val in want.items():assert int(row[key])==val,(c,scope,key,row[key],val)

def match(a,b):
 assert a.keys()==b.keys()
 for key in a:
  if key not in {'implementation','order','elapsed_ns','process_maxrss_kib'}:assert a[key]==b[key],(key,a[key],b[key])

pairs=defaultdict(dict)
for row in rows:
 key=tuple(row[k] for k in ('case','scope','phase','pair'))
 assert row['implementation'] not in pairs[key]
 pairs[key][row['implementation']]=row;cost(row,bycase[row['case']],row['scope'])
for key,pair in pairs.items():
 assert set(pair)=={'generated','c'} and {r['order'] for r in pair.values()}=={'0','1'}
 match(pair['generated'],pair['c'])
 first='generated' if (int(key[3])+(order[key[0]] if key[2]=='measurement' else 0))%2==0 else 'c'
 assert pair[first]['order']=='0'
summaries=json.loads((root/'summary.json').read_text());assert len(summaries)==72
recomputed=[]
for summary in summaries:
 case,scope=summary['case'],summary['scope'];rs=[r for r in rows if r['case']==case and r['scope']==scope and r['phase']=='measurement']
 assert Counter(r['implementation'] for r in rs)==Counter(generated=11,c=11)
 assert {int(r['pair']) for r in rs}==set(range(11)) and len({r['repetitions'] for r in rs})==1
 ratios=[];deltas=[]
 for pair in range(11):
  pp=pairs[case,scope,'measurement',str(pair)];g=int(pp['generated']['elapsed_ns'])/int(pp['generated']['repetitions']);c=int(pp['c']['elapsed_ns'])/int(pp['c']['repetitions'])
  ratios.append(g/c);deltas.append(g-c)
 assert statistics.median(ratios)==summary['paired_ratio']['median']
 assert statistics.median(deltas)==summary['paired_delta_ns']['median']
 rates={name:[int(r['elapsed_ns'])/int(r['repetitions']) for r in rs if r['implementation']==name] for name in ('generated','c')}
 assert statistics.median(rates['generated'])/statistics.median(rates['c'])==summary['ratio_of_separate_medians']
 for impl in ('generated','c'):
  ns=[int(r['elapsed_ns'])/int(r['repetitions']) for r in rs if r['implementation']==impl]
  assert statistics.median(ns)==summary['implementations'][impl]['ns_per_operation']['median']
 rng=random.Random(20261030);samples=sorted(statistics.median(rng.choices(ratios,k=11)) for _ in range(5000))
 def percentile(q):
  p=(len(samples)-1)*q;lo=int(p);return samples[lo]+(samples[min(lo+1,len(samples)-1)]-samples[lo])*(p-lo)
 assert [percentile(.025),percentile(.975)]==summary['paired_ratio_bootstrap_95_interval']
 recomputed.append({'case':case,'scope':scope,'paired_ratio':statistics.median(ratios),'paired_delta_ns':statistics.median(deltas),'median_ratio':summary['ratio_of_separate_medians'],'interval':summary['paired_ratio_bootstrap_95_interval']})
native=json.loads((root/'native-validation.json').read_text());assert len(native)==24
for record in native:
 assert record['status']=='passed' and len(record['rows'])==12
 for s,scope in enumerate(scopes):
  a,b=record['rows'][s*2:s*2+2];match(a,b);cost(a,bycase[record['case']],scope);cost(b,bycase[record['case']],scope)
verifications=[c for c in commands if c['phase']=='runtime_validation'];assert len(verifications)==288
for n in range(0,len(verifications),2):
 a,b=verifications[n:n+2];assert a['returncode']==b['returncode']==0
 assert a['command'][-3:]==b['command'][-3:] and {a['command'][-4],b['command'][-4]}=={'generated','c'}
 case=next(x for x in Path(a['command'][0]).parts if x in bycase);scope=scopes[int(a['command'][-3])]
 aa,bb=json.loads(a['stdout']),json.loads(b['stdout']);match(aa,bb);cost(aa,bycase[case],scope);cost(bb,bycase[case],scope)
failed=[c for c in commands if c['returncode']]
assert len(failed)==12 and all(c['phase']=='frontend_capture' and c['returncode']==1 and 'E_CAPTURED' in c['stderr'] for c in failed)
source_hashes=0
for rel,sha in env['source_sha256'].items():
 p=root/'source'/rel
 if not rel.startswith('/'):
  assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==sha,rel
  source_hashes+=1
for case in bycase:
 work=root/'cases'/case;response=json.loads((work/'response.json').read_text())
 assert response['ok'] and response['version']==8
 assert response['lean_source']==(work/'Generated.lean').read_text()
phases=Counter(c['phase'] for c in commands)
assert all(phases[k]==12 for k in ['independent_lean_check','independent_lean_emit','public_check_total','public_build_total','canonical_execution_validation','generated_native_compile'])
report={'raw_rows':len(rows),'pairs':len(pairs),'phase_rows':dict(Counter(r['phase'] for r in rows)),'groups':len(summaries),'native_records':len(native),'verification_commands':len(verifications),'archived_source_hashes_verified':source_hashes,'measured_head':env['toolchains']['git']['stdout'].strip(),'measurement_batches_below_5ms':dict(Counter(r['scope'] for r in rows if r['phase']=='measurement' and int(r['elapsed_ns'])<5000000)),'minimum_measurement_batch_ns':min(int(r['elapsed_ns']) for r in rows if r['phase']=='measurement'),'unexpected_command_failures':0,'recomputed':recomputed}
# Preserve the original evidence; the audit writes no project file.
print(json.dumps({k:v for k,v in report.items() if k!='recomputed'},indent=2))
for r in recomputed:
 if r['scope'] in ('lifecycle','reused_buffers'): print(r)

temporary.cleanup()
