"""Private source-to-GEMM packing receipts and exact observed-kernel calibration."""
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('source_packing_backend', ROOT/'experiments/openblas_packing/verify.py')
backend = importlib.util.module_from_spec(spec)
spec.loader.exec_module(backend)
require = backend.require
CLAIMS = {'logical_packing_payload': True, 'named_pool_metadata': True,
          'shortcut_payload': False, 'hardware_traffic': False, 'whole_process_peak': False}
FLAGS = ['-std=c11', '-O2', '-fno-lto', '-Wall', '-Wextra', '-Werror']
SANITIZERS = ['-fsanitize=address,undefined', '-fno-omit-frame-pointer']
SOURCE = 'experiments/openblas_packing/calibrate.c'


def replay(trace, packing, backing, kernels, metadata):
    """Bind independently observed backend routes to the actual source calls."""
    require(trace['schema'] == 2, 'packing needs address-bearing source calls')
    if packing is None:
        require(backing is None, 'packing observation absent from diagnostic backend')
        return None
    require(backing is not None and packing['metadata'] == metadata, 'uncalibrated packing metadata')
    observed = backend.replay(packing, backing, kernels)
    require(len(trace['calls']) == len(packing['routes']), 'source/packing route coverage')
    for call, route in zip(trace['calls'], packing['routes']):
        require(call['order'] == 102 and call['transforms'] == [111, 111], 'source packing transform')
        require(call['alpha'] == ['3ff0000000000000', '0000000000000000'] and
                call['beta'] == ['0000000000000000', '0000000000000000'], 'source packing coefficients')
        require(route['components'] == call['scalar'] + 1 and route['ta'] == route['tb'] == 0 and
                [route[k] for k in ('m', 'n', 'k')] == call['shape'] and
                [route[k] for k in ('lda', 'ldb', 'ldc')] == call['leading'], 'source packing arguments')
        require([route[k] for k in ('a', 'b', 'c')] == call['addresses'], 'source packing address binding')
        require((route['before'], route['after']) == (call['begin'], call['end']), 'source packing call span')
        for event in backing['events'][route['before']:route['after']]:
            require(event['phase'] == 10 + call['phase'], 'source packing phase')
    return observed


def contracts(rows):
    return {tuple(call[k] for k in ('kernel', 'm', 'n', 'lda'))
            for row in rows if row['packing'] is not None for call in row['packing']['calls']}


def calibrate(runner, out, cc, prefixes, calibration, rows):
    """Compile current trusted calibration code; never run an archived binary."""
    build = out/'.lake/source-packing'
    build.mkdir(parents=True, exist_ok=False)
    source = out/'source'/SOURCE
    expected = calibration['repository']['inputs'][SOURCE]['sha256']
    require(hashlib.sha256(source.read_bytes()).hexdigest() == expected, 'changed source packing calibrator')
    unroll = calibration['builds']['stock']['unroll']
    binaries = []
    for variant, sanitized in itertools.product(('stock', 'diagnostic'), (False, True)):
        name = variant + '-calibration' + ('-sanitized' if sanitized else '')
        binary = build/name
        runner.run([cc, *FLAGS, *['-DVP_'+k+'='+str(v) for k, v in sorted(unroll.items())],
                    *(SANITIZERS if sanitized else []), source,
                    prefixes[variant]/'lib/libopenblas.a', '-lm', '-lpthread', '-o', binary],
                   phase='source_packing_build')
        data = binary.read_bytes()
        binaries.append({'variant': variant, 'sanitized': sanitized, 'name': name,
                         'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
    footprints = []
    for contract in sorted(contracts(rows)):
        for binary in binaries:
            result = runner.run([build/binary['name'], *contract], phase='source_packing_footprint')
            footprints.append({'variant': binary['variant'], 'sanitized': binary['sanitized'],
                               'contract': list(contract), 'result': json.loads(result['stdout'])})
    return {'schema': 1, 'claims': CLAIMS, 'build_dir': str(build),
            'binaries': binaries, 'footprints': footprints}


def check_footprints(reader, record, rows, calibration, kernels, commands):
    binding = record['packing']
    require(set(binding) == {'schema', 'claims', 'build_dir', 'binaries', 'footprints'} and
            type(binding['schema']) is int and binding['schema'] == 1 and binding['claims'] == CLAIMS,
            'source packing calibration envelope')
    require(all(type(v) is bool for v in binding['claims'].values()), 'source packing claim domain')
    build = Path(binding['build_dir'])
    require(build.is_absolute() and build.parts[-2:] == ('.lake', 'source-packing'), 'source packing build path')
    expected_source = calibration['repository']['inputs'][SOURCE]['sha256']
    require(record['inputs'][SOURCE] == expected_source and
            hashlib.sha256(reader.read('source/'+SOURCE)).hexdigest() == expected_source,
            'source packing calibrator fingerprint')
    variants = set(itertools.product(('stock', 'diagnostic'), (False, True)))
    seen = set()
    links = [c for c in commands if c['phase'] == 'source_packing_build']
    require(len(links) == 4 and len(binding['binaries']) == 4, 'source packing build coverage')
    for binary in binding['binaries']:
        variant, sanitized = binary['variant'], binary['sanitized']
        key = variant, sanitized
        require(type(sanitized) is bool and key in variants and key not in seen, 'source packing binary identity')
        seen.add(key)
        name = variant + '-calibration' + ('-sanitized' if sanitized else '')
        require(binary['name'] == name, 'source packing binary name')
        backend.natural(binary['bytes'], 'source packing binary size', positive=True)
        digest = binary['sha256']
        require(isinstance(digest, str) and len(digest) == 64 and
                all(x in '0123456789abcdef' for x in digest), 'source packing binary digest')
        relative = '.lake/source-packing/'+name
        if relative in reader.names:
            data = reader.read(relative)
            require(len(data) == binary['bytes'] and hashlib.sha256(data).hexdigest() == digest,
                    'source packing executable changed')
        unroll = calibration['builds'][variant]['unroll']
        expected = [record['host']['cc'], *FLAGS,
                    *['-DVP_'+k+'='+str(v) for k, v in sorted(unroll.items())],
                    *(SANITIZERS if sanitized else []), str(build.parent.parent/'source'/SOURCE),
                    record['prefixes'][variant]+'/lib/libopenblas.a', '-lm', '-lpthread', '-o', str(build/name)]
        require(sum(c['command'] == expected and c['returncode'] == 0 for c in links) == 1,
                'source packing compile/link receipt')
    wanted = {(v, s, c) for v, s in variants for c in contracts(rows)}
    seen = set()
    executions = [c for c in commands if c['phase'] == 'source_packing_footprint']
    require(len(executions) == len(wanted) == len(binding['footprints']), 'source packing footprint coverage')
    definitions = {k['name']: k for k in kernels}
    by_command = {tuple(c['command']): c for c in executions}
    require(len(by_command) == len(executions), 'duplicate source packing execution')
    for receipt in binding['footprints']:
        variant, sanitized = receipt['variant'], receipt['sanitized']
        contract = tuple(receipt['contract'])
        key = variant, sanitized, contract
        require(type(sanitized) is bool and key in wanted and key not in seen, 'source packing footprint identity')
        seen.add(key)
        kernel, m, n, lda = contract
        definition = definitions[kernel]
        expected = {'kind': 'observed_kernel_footprint', 'kernel': kernel, 'm': m, 'n': n, 'lda': lda,
                    'checked_input_words': lda*(m if definition['transpose'] else n)*definition['components'],
                    'checked_output_words': m*n*definition['components']}
        name = variant + '-calibration' + ('-sanitized' if sanitized else '')
        command = by_command.get(tuple([str(build/name), *map(str, contract)]))
        require(command is not None and command['returncode'] == 0 and
                json.loads(command['stdout']) == receipt['result'] == expected,
                'source packing footprint command/output')
    require(seen == wanted, 'missing source packing footprint')
    return {'contracts': len(contracts(rows)), 'executions': len(seen)}
