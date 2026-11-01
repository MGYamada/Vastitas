#!/usr/bin/env python3
"""Independently replay diagnostic backing/checkout events and paired results."""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import struct
import zipfile

CLAIMS = {'timing':False,'unchanged_backend':False,'total_process_memory':False,
          'actual_packing_bytes':False,'controlled_host':False,'stock_kernel_objects_unchanged':True}
PIN = 'cd7e129868320cc2d033afa920e31202dfe0b8066a5b66661900ccc0f197dfed'
MEMORY_PIN = '3b5bedc19c4555de21fb0c649177d9be1545d28fc61a8cbcc475e4a9bffc9935'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def natural(value, label, *, positive=False):
    require(type(value) is int and (value > 0 if positive else value >= 0) and value < 2**64,
            f'invalid {label}')
    return value


def replay(row):
    require(set(row) == {'kind','buffer_bytes','page_bytes','observer_static_bytes','event_capacity','events'}
            and row['kind'] == 'workspace', 'workspace envelope')
    capacity = natural(row['buffer_bytes'],'buffer capacity',positive=True)
    page = natural(row['page_bytes'],'page size',positive=True)
    require(page & (page-1) == 0 and capacity % page == 0, 'page/capacity alignment')
    natural(row['observer_static_bytes'],'observer bytes',positive=True)
    require(row['event_capacity'] == 4096 and 0 < len(row['events']) <= 4096, 'event capacity')
    # Regions are requested malloc bytes or page-rounded mmap address ranges.
    # Neither means resident bytes, allocator usable size, or actual packing.
    regions, loans = [], {}
    phase, markers, shutdown = 0, [], 0
    counts, by_phase = Counter(), {}
    peak = {'mmap_bytes':0,'malloc_requested_bytes':0,'borrowed_capacity_bytes':0}
    before_shutdown = None

    def state():
        return {'mmap_bytes':sum(b-a for a,b,k in regions if k == 'mmap'),
                'malloc_requested_bytes':sum(b-a for a,b,k in regions if k == 'malloc'),
                'borrowed_capacity_bytes':len(loans)*capacity}

    for sequence, event in enumerate(row['events']):
        require(set(event) == {'sequence','phase','operation','address','bytes','ok','errno'}, 'event fields')
        require(type(event['sequence']) is int and event['sequence'] == sequence, 'sequence')
        p = natural(event['phase'],'phase')
        op = event['operation']
        require(isinstance(event['address'],str) and re.fullmatch(r'0x[0-9a-f]+',event['address']), 'address')
        address = int(event['address'],16)
        require(address < 2**64, 'address overflow')
        size = natural(event['bytes'],'size')
        require(type(event['ok']) is int and event['ok'] in (0,1), 'success domain')
        natural(event['errno'],'errno')
        require(op in ('mark','mmap','munmap','malloc','free','borrow','return',
                       'direct_borrow','direct_return','shutdown_begin','shutdown_end'), 'operation')
        if op == 'mark':
            require(p > phase and address == size == event['errno'] == 0 and event['ok'] == 1, 'marker')
            phase = p
            markers.append(p)
        require(p == phase, 'unmarked phase')
        require(shutdown != 2 or op == 'mark', 'operation after shutdown')
        counts[op] += 1
        current = by_phase.setdefault(p, {'counts':Counter(),'end':state()})
        current['counts'][op] += 1
        if not event['ok']:
            require(op in ('mmap','malloc','munmap') and event['errno'] > 0, 'unexplained failed operation')
            if op == 'mmap': require(address == 2**64-1, 'MAP_FAILED value')
            if op == 'malloc': require(address == 0, 'failed malloc pointer')
        elif op in ('mmap','malloc'):
            require(address and size and event['errno'] == 0, 'allocation domain')
            actual = ((size+page-1)//page)*page if op == 'mmap' else size
            end = address+actual
            require(end < 2**64 and (op != 'mmap' or address % page == 0), 'allocation range')
            require(all(end <= a or b <= address for a,b,_ in regions), 'overlapping backing allocation')
            regions.append((address,end,op))
        elif op in ('free','munmap'):
            if op == 'free':
                require(size == 0 and event['errno'] == 0, 'free domain')
                if address:
                    candidates = [(a,b,k) for a,b,k in regions if a == address and k == 'malloc']
                    require(len(candidates) == 1, 'unknown/double free')
                    end = candidates[0][1]
                    require(all(end <= a or a+capacity <= address for a in loans), 'free during borrow')
                    regions.remove(candidates[0])
            else:
                require(size and address % page == 0 and event['errno'] == 0, 'munmap domain')
                end = address+((size+page-1)//page)*page
                require(end < 2**64, 'munmap overflow')
                covered = sum(max(0,min(end,b)-max(address,a)) for a,b,k in regions if k == 'mmap')
                require(covered == end-address, 'unknown/double/partly uncovered munmap')
                require(all(end <= a or a+capacity <= address for a in loans), 'unmap during borrow')
                updated = []
                for a,b,k in regions:
                    if k != 'mmap' or b <= address or end <= a:
                        updated.append((a,b,k))
                    else:
                        if a < address: updated.append((a,address,k))
                        if end < b: updated.append((end,b,k))
                regions = updated
        elif op in ('borrow','direct_borrow'):
            require(not shutdown and size == capacity and address and event['errno'] == 0, 'borrow domain')
            backing = [(a,b,k) for a,b,k in regions if a <= address and address+capacity <= b]
            require(len(backing) == 1, 'borrow lacks observed backing')
            require(op != 'direct_borrow' or backing[0][2] == 'malloc', 'direct backing kind')
            require(all(address+capacity <= a or a+capacity <= address for a in loans), 'overlapping active loans')
            loans[address] = op
        elif op in ('return','direct_return'):
            require(not shutdown and size == capacity and event['errno'] == 0, 'return domain')
            require(loans.get(address) == ('borrow' if op == 'return' else 'direct_borrow'), 'unmatched/double return')
            del loans[address]
        elif op == 'shutdown_begin':
            require(phase == 18 and not shutdown and not loans and address == size == event['errno'] == 0,
                    'invalid shutdown begin')
            before_shutdown = state()
            shutdown = 1
        elif op == 'shutdown_end':
            require(phase == 18 and shutdown == 1 and not regions and not loans and address == size == event['errno'] == 0,
                    'unreleased backing at shutdown')
            shutdown = 2
        current['end'] = state()
        for key,value in state().items(): peak[key] = max(peak[key],value)
    require(shutdown == 2 and markers[-1:] == [19] and not regions and not loans, 'incomplete lifetime')
    require(all(item['end']['borrowed_capacity_bytes'] == 0 for p,item in by_phase.items() if p in (0,10,15,17,18,19)),
            'unexpected retained borrow')
    return {'buffer_bytes':capacity,'observer_static_bytes':row['observer_static_bytes'],
            'counts':dict(counts),'phases':by_phase,'peak':peak,'before_shutdown':before_shutdown,'markers':markers}


def check_calibration(observed):
    b, phases = observed['buffer_bytes'], observed['phases']
    require(observed['markers'] == list(range(10,20)), 'calibration phases')
    expected = {11:b,12:2*b,13:b,14:2*b,15:0,16:b,17:0}
    for p,amount in expected.items():
        require(phases[p]['end']['borrowed_capacity_bytes'] == amount, 'known outstanding capacity')
    # Returning/reborrowing a pooled block cannot masquerade as OS free/alloc.
    require(phases[13]['counts'] == {'mark':1,'return':1}, 'return must only return to pool')
    require(phases[14]['counts'] == {'mark':1,'borrow':1}, 'known pool reuse must not allocate backing')
    require(phases[15]['counts'] == {'mark':1,'return':2}, 'two final returns')
    require(phases[16]['counts'] == {'mark':1,'malloc':1,'direct_borrow':1}, 'nolock allocation calibration')
    require(phases[17]['counts'] == {'mark':1,'direct_return':1,'free':1}, 'nolock free calibration')
    require(phases[15]['end']['mmap_bytes']+phases[15]['end']['malloc_requested_bytes'] >= 2*b,
            'returned pool capacity was lost')


@lru_cache(maxsize=None)
def expected_checksums(scalar,n,transform):
    def value(which,r,c):
        return ((r+2*c+which)%5-2, (2*r+c+which)%3-1 if scalar else 0)

    @lru_cache(maxsize=None)
    def dot(r,c):
        terms = []
        for k in range(15):
            ar,ai = value(0,k,r) if transform else value(0,r,k)
            br,bi = value(1,k,c)
            if transform == 2: ai = -ai
            terms.append((ar*br-ai*bi,ar*bi+ai*br))
        return tuple((n//15)*sum(t[p] for t in terms)+sum(t[p] for t in terms[:n%15]) for p in range(2))

    result = []
    for multiplier in (1,2):
        h = 1469598103934665603
        for owner in range(3):
            for index in range((n+1)*n+2):
                r,c = ((index-1)%(n+1),(index-1)//(n+1)) if index else (n,n)
                pair = (-7,-7 if scalar else 0)
                if r < n and c < n:
                    pair = value(owner,r,c) if owner < 2 else tuple(multiplier*x for x in dot(r%15,c%15))
                for number in pair[:scalar+1]:
                    word = struct.unpack('<Q',struct.pack('<d',float(number)))[0]
                    h = ((h ^ word)*1099511628211) % 2**64
        result.append(f'{h:016x}')
    return [result[0],result[0],result[1]]


class Reader:
    def __init__(self,path):
        self.path = Path(path)
        self.zip = zipfile.ZipFile(path) if self.path.is_file() else None
        names = [i.filename for i in self.zip.infolist() if not i.is_dir()] if self.zip else [
            p.relative_to(self.path).as_posix() for p in self.path.rglob('*') if p.is_file()]
        require(len(names) == len(set(names)), 'duplicate archive member')
        for name in names:
            p = PurePosixPath(name)
            require(not p.is_absolute() and '..' not in p.parts and '\\' not in name, 'unsafe member')
        self.names = set(names)

    def read(self,name):
        require(name in self.names, 'missing record member: '+name)
        return self.zip.read(name) if self.zip else (self.path/name).read_bytes()

    def json(self,name):
        return json.loads(self.read(name))


def verify(path):
    r = Reader(path)
    record = r.json('record.json')
    require(record['schema'] == 1 and record['kind'] == 'diagnostic-openblas-workspace', 'schema')
    require(record['claims'] == CLAIMS and all(type(v) is bool for v in record['claims'].values()), 'unsupported claim')
    require(record['upstream']['version'] == '0.3.34' and record['upstream']['sha256'] == PIN, 'upstream pin')
    require(record['upstream']['changed_objects'] == ['driver/others/memory.o'], 'changed object scope')
    require(set(record['files']) | {'record.json'} == r.names, 'record inventory')
    for name,entry in record['files'].items():
        data = r.read(name)
        require(len(data) == entry['bytes'] and hashlib.sha256(data).hexdigest() == entry['sha256'], 'file hash: '+name)
    for relative,entry in record['repository']['inputs'].items():
        require(entry['snapshot'] == 'inputs/repository/'+relative and
                hashlib.sha256(r.read(entry['snapshot'])).hexdigest() == entry['sha256'], 'source input: '+relative)
    required_inputs = {'experiments/openblas_workspace/'+p for p in (
        'README.md','observer.h','observer.c','wrappers.c','patch.py','probe.c','run.py','verify.py','test_workspace.py')}
    required_inputs.update(('scripts/build_openblas.py','lean-kernel/native/storage.c','lean-kernel/native/storage.h',
                           'lean-kernel/native/diagonal.c','lean-kernel/native/diagonal.h',
                           'lean-kernel/numerical/gemm.c','lean-kernel/numerical/gemm.h'))
    require(required_inputs <= set(record['repository']['inputs']), 'missing required source input')
    require(hashlib.sha256(r.read('inputs/upstream/driver/others/memory.c')).hexdigest() == MEMORY_PIN, 'memory source pin')
    # Reconstruct the permitted textual instrumentation without importing the
    # build patcher or executing any code from an archive.
    expected = r.read('inputs/upstream/driver/others/memory.c').decode()
    expected = re.sub(r'^(void (?:\*)?)(blas_memory_(?:alloc|free)(?:_nolock)?|blas_shutdown)\(',
                      r'\1vobs_real_\2(',expected,flags=re.M)
    expected = re.sub(r'\b(malloc|free|mmap|munmap)\(',r'vobs_\1(',expected)
    expected = expected.replace('#include "common.h"\n','#include "common.h"\n#include "vobs-observer.c"\n')
    expected += '\n#include "vobs-wrappers.c"\n'
    require(r.read('inputs/upstream/memory-diagnostic.c') == expected.encode(), 'unexpected memory instrumentation')
    old, new = r.json('stock-objects.json'),r.json('diagnostic-objects.json')
    require(old.keys() == new.keys() and sorted(p for p in old if old[p] != new[p]) == ['driver/others/memory.o'],
            'non-observer object changed')
    require(len(old) > 100, 'missing algorithm objects')
    commands = r.json(record['commands'])
    require(all(c['returncode'] == 0 for c in commands), 'failed command')
    require(len({c['label'] for c in commands}) == len(commands), 'duplicate command')
    for variant in ('stock','diagnostic'):
        link = [c for c in commands if c['label'] == variant+'-link']
        require(len(link) == 1 and ('-DVOBS_DIAGNOSTIC' in link[0]['argv']) == (variant == 'diagnostic'), 'link variant')
        require(link[0]['argv'][-2] == '-o' and Path(link[0]['argv'][-1]).name == variant, 'linked binary target')
    cases = [('calibration',)] + [(str(s),str(n),str(t)) for s in range(2) for n in (0,2,32,256) for t in range(3)]
    required = {(v,repeat,case) for v in ('stock','diagnostic') for repeat in (1,2,3) for case in cases}
    seen, pairs, observations, configs = set(),{},[],set()
    for run in record['runs']:
        key = (run['variant'],run['repeat'],tuple(run['case']))
        require(key in required and key not in seen, 'duplicate/unexpected run')
        seen.add(key)
        entries = r.json(run['parsed'])
        raw = [json.loads(line) for line in r.read(run['stdout']).decode().splitlines()]
        require(raw == entries and len(entries) == (2 if run['variant'] == 'diagnostic' else 1), 'raw/parsed rows')
        matched = [c for c in commands if c['stdout'] == run['stdout']]
        require(len(matched) == 1 and matched[0]['argv'][1:] == run['case'], 'run command')
        require(Path(matched[0]['argv'][0]).name == run['variant'], 'wrong binary')
        row = entries[0]
        configs.add(row['configuration'])
        require(row['configuration'].startswith('OpenBLAS 0.3.34 ') and 'USE64BITINT' not in row['configuration'], 'backend config')
        pairs.setdefault((run['repeat'],tuple(run['case'])),[]).append(row)
        if row['kind'] == 'calibration':
            require(run['case'] == ['calibration'] and row['distinct'] is True and row['reuse'] is True, 'calibration result')
        else:
            s,n,t = map(int,run['case'])
            require(row['kind'] == 'gemm' and (row['scalar'],row['n'],row['transform']) == (s,n,t), 'case identity')
            require(row['kernel_calls'] == (3 if n else 0) and row['arena_data_bytes'] == 3*((n+1)*n+2)*8*(s+1), 'adapter costs')
            require(row['checksums'] == expected_checksums(s,n,t), 'coordinate reference result/padding')
        if run['variant'] == 'diagnostic':
            observation = replay(entries[1])
            if row['kind'] == 'calibration': check_calibration(observation)
            else:
                require(observation['markers'] == [10,11,12,13,14,18,19], 'GEMM phases')
                require(observation['phases'][14]['counts'] == {'mark':1}, 'rejected preflight called backend')
                for p in (10,11,12,13,14):
                    require(observation['phases'][p]['end']['borrowed_capacity_bytes'] == 0, 'GEMM escaped borrow')
                    if p == 10 or row['n'] == 0:
                        require(observation['phases'][p]['counts'] == {'mark':1}, 'setup/empty GEMM workspace events')
            observations.append({'repeat':run['repeat'],'case':run['case'],**observation})
    require(seen == required and len(configs) == 1, 'missing runs/config mismatch')
    require(all(len(rows) == 2 and rows[0] == rows[1] for rows in pairs.values()), 'stock/diagnostic result mismatch')
    return {'runs':len(seen),'paired_fresh_processes':len(pairs),'observations':observations,'claims':CLAIMS}


def compact_summary(result):
    """Group only exactly identical address-free observations; retain all cases."""
    groups = {}
    for observation in result['observations']:
        detail = {k:v for k,v in observation.items() if k not in ('repeat','case')}
        key = json.dumps(detail,sort_keys=True)
        group = groups.setdefault(key,{'observation':detail,'runs':[]})
        group['runs'].append({'repeat':observation['repeat'],'case':observation['case']})
    return {'runs':result['runs'],'paired_fresh_processes':result['paired_fresh_processes'],
            'claims':result['claims'],'groups':list(groups.values())}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('record',type=Path)
    parser.add_argument('--summary',action='store_true',help='emit all grouped observations as JSON')
    args = parser.parse_args()
    result = verify(args.record)
    print(json.dumps(compact_summary(result) if args.summary else
                     {k:v for k,v in result.items() if k != 'observations'},indent=2))
