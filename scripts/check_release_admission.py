#!/usr/bin/env python3
"""Check and render the finite v0.1.0 evidence index; never accept a program.

The index refers to check_spec's claims rather than inventing another proof
status. --require-complete is a release reporting gate, not a proof verifier.
"""
import argparse
import json
from pathlib import Path
import re
import sys
import tomllib

import check_spec

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('docs/release/v0.1.0.toml')
CHAPTER = Path('docs/v0.1.0-admission.md')
ISSUES = {199, 206, 282, 318, 417, 455, 462, 533, 686, 689, 749, 750,
          751, 752, 753, 755, 756, 757, 758, 762, 763, 779, 839}
ROWS = ('functions', 'category', 'tensor', 'numerical', 'scalar-indexed',
        'resources', 'edition-verification', 'type-names')
DIMENSIONS = ('source', 'core', 'midir', 'llvm', 'official', 'fast', 'native',
              'performance', 'vocabulary')
STATES = {'planned', 'partial', 'complete', 'not-claimed'}

# Reviewed obligations, independent of the editable progress ledger. A claim's
# status alone says nothing about which release requirement it discharges.
# Additional claims of these same properties may explain partial progress;
# admitting a different property requires a review of this mapping.
COMMON_OBLIGATIONS = {
    'midir': ('compiler-ir.midir@representation',),
    'llvm': ('compiler-ir.llvm-bytes@bytes',),
    'fast': ('compiler-ir.verification-modes@modes',),
    'native': ('compiler-ir.backend@native',),
    'performance': ('compiler-ir.performance@measurement',),
}
ROW_OBLIGATIONS = {
    'functions': {
        'source': ('compiler-ir.families@family', 'compiler-ir.families@public-syntax'),
        'core': ('compiler-ir.families@assembly', 'compiler-ir.families@public-syntax',
                 'compiler-ir.families@revision-replay', 'compiler-ir.families@singleton-source',
                 'compiler-ir.edition@namespace-source'),
        'midir': ('compiler-ir.midir@representation', 'compiler-ir.midir@pure-cfg', 'compiler-ir.midir@direct-call'),
        'llvm': ('compiler-ir.llvm-bytes@bytes', 'compiler-ir.llvm-bytes@static-call',
                 'compiler-ir.llvm-bytes@assembled-bool'),
        'official': ('compiler-ir.stage-validation@soundness', 'compiler-ir.stage-validation@pure-cfg',
                     'compiler-ir.llvm-bytes@static-call', 'compiler-ir.llvm-bytes@assembled-bool',
                     'compiler-ir.families@static-retention'),
    },
    'category': {
        'source': ('compiler-ir.finite-models@source-core', 'compiler-ir.finite-models@category-check',
                   'compiler-ir.finite-models@isomorphism-source', 'compiler-ir.finite-models@opposite-source',
                   'compiler-ir.finite-models@functor-source', 'compiler-ir.finite-models@transformation-monad-source',
                   'compiler-ir.finite-binders@category-functions', 'compiler-ir.finite-binders@monad-functions'),
        'core': ('compiler-ir.finite-binders@admission', 'compiler-ir.finite-binders@concrete-lookup',
                 'compiler-ir.finite-binders@category-functions', 'compiler-ir.finite-binders@monad-functions'),
        'midir': ('compiler-ir.midir@representation', 'compiler-ir.midir@finite-lookup'),
        'llvm': ('compiler-ir.llvm-bytes@bytes', 'compiler-ir.llvm-bytes@switch-regression',
                 'compiler-ir.llvm-bytes@binary-function', 'compiler-ir.llvm-bytes@binary-source',
                 'compiler-ir.llvm-bytes@finite-entry', 'compiler-ir.llvm-bytes@finite-package-source'),
        'official': ('compiler-ir.finite-models@laws', 'compiler-ir.finite-models@category-equations',
                   'compiler-ir.finite-models@isomorphism-equations', 'compiler-ir.finite-models@opposite-equations',
                     'compiler-ir.finite-models@functor-equations', 'compiler-ir.finite-models@transformation-monad-equations',
                     'compiler-ir.finite-models@kleisli-equations',
                     'compiler-ir.finite-binders@typed-substitution',
                     'compiler-ir.llvm-bytes@unary-function', 'compiler-ir.llvm-bytes@finite-entry'),
        'native': ('compiler-ir.finite-models@execution', 'compiler-ir.finite-models@kleisli-run'),
    },
    'tensor': {
        'source': ('compiler-ir.edition@admission', 'compiler-ir.tensor@public-views'),
        'core': ('compiler-ir.tensor@semantics', 'compiler-ir.tensor@public-views'),
        'midir': ('compiler-ir.midir@representation', 'compiler-ir.storage@static-effects', 'compiler-ir.storage@gemm-abi'),
        'llvm': ('compiler-ir.llvm-bytes@bytes', 'compiler-ir.storage@static-effects', 'compiler-ir.storage@gemm-abi'),
        'official': ('compiler-ir.stage-validation@soundness', 'compiler-ir.tensor@coordinate-storage', 'compiler-ir.storage@gemm-abi'),
        'native': ('compiler-ir.tensor@native', 'compiler-ir.tensor@storage-native', 'compiler-ir.storage@gemm-native'),
    },
    'numerical': {
        'source': ('compiler-ir.realization@source', 'compiler-ir.realization@affine-wrappers', 'compiler-ir.realization@identity-source', 'compiler-ir.realization@exact-chart-source'),
        'core': ('compiler-ir.float-carrier@storage', 'compiler-ir.float-carrier@binary64-storage',
                 'compiler-ir.realization@affine-wrappers', 'compiler-ir.realization@identity-source', 'compiler-ir.realization@exact-chart-source'),
        'midir': ('compiler-ir.midir@representation', 'compiler-ir.storage@static-effects', 'compiler-ir.storage@gemm-abi'),
        'llvm': ('compiler-ir.llvm-bytes@bytes', 'compiler-ir.storage@static-effects', 'compiler-ir.storage@gemm-abi'),
        'official': ('compiler-ir.numeric-order@reference', 'compiler-ir.numeric-order@reference-boundaries',
                     'compiler-ir.realization@affine-expansion', 'compiler-ir.realization@identity-origin', 'compiler-ir.float-carrier@reference-laws',
                     'compiler-ir.realization@rational-coordinates', 'compiler-ir.realization@exact-fields',
                     'compiler-ir.realization@exact-chart-selection',
                     'compiler-ir.realization@coordinate-interpretation', 'compiler-ir.storage@static-effects',
                     'compiler-ir.storage@static-cleanup', 'compiler-ir.storage@gemm-abi'),
        'native': ('compiler-ir.native-fast@profile', 'compiler-ir.native-fast@identity-run',
                   'compiler-ir.storage@static-native', 'compiler-ir.storage@gemm-native'),
    },
    'scalar-indexed': {
        'source': ('compiler-ir.operators@binding', 'compiler-ir.operators@exact-integers'),
        'core': ('compiler-ir.coverage@ledger', 'compiler-ir.coverage@inventory'),
        'midir': ('compiler-ir.registry@opcodes', 'compiler-ir.registry@int-literal', 'compiler-ir.registry@exact-arithmetic'),
        'llvm': ('compiler-ir.llvm-bytes@bytes', 'compiler-ir.llvm-bytes@entry-status',
                 'compiler-ir.llvm-bytes@folded-entry', 'compiler-ir.llvm-bytes@entry-regression',
                 'compiler-ir.llvm-bytes@boxed-library', 'compiler-ir.llvm-bytes@boxed-program',
                 'compiler-ir.llvm-bytes@boxed-regression'),
        'official': ('compiler-ir.stage-validation@soundness', 'compiler-ir.llvm-bytes@entry-status',
                     'compiler-ir.llvm-bytes@folded-entry', 'compiler-ir.verification-modes@boxed-stage'),
        'native': ('compiler-ir.runtime@linkage', 'compiler-ir.backend@native', 'compiler-ir.feasibility@qualification'),
    },
    'resources': {
        'source': ('compiler-ir.edition@admission', 'compiler-ir.storage@static-native'),
        'core': ('compiler-ir.storage@refinement', 'compiler-ir.storage@static-effects', 'compiler-ir.storage@erased-unit'),
        'midir': ('compiler-ir.midir@representation', 'compiler-ir.storage@static-effects'),
        'llvm': ('compiler-ir.llvm-bytes@bytes', 'compiler-ir.storage@static-effects'),
        'official': ('compiler-ir.constitution@finite-proofs', 'compiler-ir.storage@static-effects',
                     'compiler-ir.storage@static-cleanup', 'compiler-ir.storage@erased-unit'),
        'native': ('compiler-ir.backend@native', 'compiler-ir.storage@static-native'),
    },
    'edition-verification': {
        'source': ('compiler-ir.edition@manifest', 'compiler-ir.edition@admission',
                   'compiler-ir.edition@finite-tables', 'compiler-ir.finite-binders@category-functions',
                   'compiler-ir.realization@affine-wrappers', 'compiler-ir.realization@identity-source', 'compiler-ir.realization@exact-chart-source'),
        'core': ('compiler-ir.edition@manifest', 'compiler-ir.edition@correspondence',
                 'compiler-ir.edition@finite-tables', 'compiler-ir.edition@finite-declaration-source',
                 'compiler-ir.families@singleton-source', 'compiler-ir.edition@namespace-source'),
        'llvm': ('compiler-ir.llvm-bytes@bytes', 'compiler-ir.check-build@preview'),
        'official': ('compiler-ir.composition@theorem',),
        'fast': ('compiler-ir.proof-binding@authentication',),
        'native': ('compiler-ir.distribution@packaging',),
    },
}
NAMING_DOCUMENT = 'docs/language/types.md#public-type-names'
LLVM_PROOFS = {'compiler-ir.llvm-bytes@bytes', 'compiler-ir.llvm-bytes@static-call', 'compiler-ir.llvm-bytes@assembled-bool',
               'compiler-ir.llvm-bytes@entry-status', 'compiler-ir.llvm-bytes@folded-entry',
               'compiler-ir.llvm-bytes@binary-function', 'compiler-ir.llvm-bytes@finite-entry',
               'compiler-ir.llvm-bytes@boxed-library', 'compiler-ir.llvm-bytes@boxed-program'}


def obligations(row, dimension):
    if row == 'type-names' or dimension == 'vocabulary':
        return ()
    return ROW_OBLIGATIONS[row].get(dimension, COMMON_OBLIGATIONS.get(dimension, ()))


def required_status(dimension, claim):
    if dimension == 'official' and claim == 'compiler-ir.realization@coordinate-interpretation':
        return 'proved-bridge'
    if (claim in {'compiler-ir.storage@static-effects', 'compiler-ir.storage@gemm-abi', 'compiler-ir.storage@erased-unit',
                  'compiler-ir.edition@finite-declaration-source', 'compiler-ir.families@singleton-source',
                  'compiler-ir.edition@namespace-source'}
            or dimension == 'official'
            or (dimension == 'llvm' and claim in LLVM_PROOFS)
            or (dimension == 'midir' and claim == 'compiler-ir.midir@finite-lookup')):
        return 'proved-oracle'
    return 'tested'


def fields(value, expected, where, errors):
    if not isinstance(value, dict) or set(value) != set(expected):
        errors.append(f'{where}: expected fields {", ".join(expected)}')
        return False
    return True


def text(value):
    return isinstance(value, str) and bool(value.strip())


def claim_index(state):
    return {f'{prop.id}@{claim.name}': (spec, prop, claim)
            for spec in state.specs for prop in spec.properties for claim in prop.claims}


def validate(data, claims, root, errors):
    if not fields(data, ('schema', 'release', 'wire', 'baseline', 'issue', 'row'), 'index', errors):
        return
    if type(data['schema']) is not int or data['schema'] != 1 or data['release'] != '0.1.0':
        errors.append('index: unsupported schema or release')
    if type(data['wire']) is not int or data['wire'] != 10:
        errors.append('index: v0.1.0 requires the single wire epoch 10')
    if not isinstance(data['baseline'], str) or not re.fullmatch('[0-9a-f]{40}', data['baseline']):
        errors.append('index: baseline must be a full source commit')
    if not isinstance(data['issue'], list) or not isinstance(data['row'], list):
        errors.append('index: issue and row must be arrays')
        return
    numbers, row_ids = [], []
    for issue in data['issue']:
        if not fields(issue, ('number', 'title', 'state', 'depends', 'remaining'), 'issue', errors):
            continue
        number = issue['number']
        if type(number) is not int or number not in ISSUES:
            errors.append('issue: unknown issue number')
            continue
        numbers.append(number)
        if not text(issue['title']) or not text(issue['remaining']):
            errors.append(f'#{number}: title and remaining scope are required')
        if issue['state'] not in ('open', 'complete'):
            errors.append(f'#{number}: state must be open or complete')
        depends = issue['depends']
        if (not isinstance(depends, list) or any(type(n) is not int or n not in ISSUES or n == number for n in depends)
                or len(depends) != len(set(depends))):
            errors.append(f'#{number}: invalid dependency list')
    if len(numbers) != len(ISSUES) or set(numbers) != ISSUES:
        errors.append('index: each of the 23 issue numbers must occur exactly once')
    by_number = {i['number']: i for i in data['issue'] if isinstance(i, dict) and type(i.get('number')) is int}
    # Dependencies are work prerequisites, not every cross-reference in an issue.
    def visit(number, stack):
        if number in stack:
            errors.append(f'#{number}: cyclic completion dependencies')
            return
        item = by_number.get(number, {})
        dependencies = item.get('depends', [])
        if not isinstance(dependencies, list):
            return
        for dep in dependencies:
            if type(dep) is int and dep in by_number:
                if item.get('state') == 'complete' and by_number[dep].get('state') != 'complete':
                    errors.append(f'#{number}: complete while prerequisite #{dep} is open')
                visit(dep, stack | {number})
    if len(numbers) == len(ISSUES) and set(numbers) == ISSUES:
        for number in sorted(ISSUES):
            visit(number, set())
    covered = set()
    for row in data['row']:
        if not fields(row, ('id', 'title', 'issues', 'requirement', 'dimension'), 'row', errors):
            continue
        name = row['id']
        if not isinstance(name, str) or name not in ROWS:
            errors.append('row: unknown row id')
            continue
        row_ids.append(name)
        if not text(row['title']) or not text(row['requirement']):
            errors.append(f'{name}: title and requirement are required')
        owners = row['issues']
        if (not isinstance(owners, list) or not owners or
                any(type(n) is not int or n not in ISSUES for n in owners) or len(owners) != len(set(owners))):
            errors.append(f'{name}: invalid issue references')
        else:
            covered.update(owners)
        if not fields(row['dimension'], DIMENSIONS, name, errors):
            continue
        for dimension, cell in row['dimension'].items():
            where = f'{name}.{dimension}'
            if not fields(cell, ('state', 'claims', 'note', 'document'), where, errors):
                continue
            status = cell['state']
            if not isinstance(status, str) or status not in STATES or not text(cell['note']):
                errors.append(f'{where}: needs a known state and an explanation')
                continue
            refs = cell['claims']
            if not isinstance(refs, list) or any(not isinstance(r, str) for r in refs):
                errors.append(f'{where}: claims must be strings')
                continue
            if len(refs) != len(set(refs)):
                errors.append(f'{where}: duplicate claim')
            required = obligations(name, dimension)
            missing = set(required) - set(refs)
            if missing:
                errors.append(f'{where}: missing mandatory obligations {sorted(missing)}')
            properties = {ref.partition('@')[0] for ref in required}
            unrelated = [ref for ref in refs if ref.partition('@')[0] not in properties]
            if unrelated:
                errors.append(f'{where}: unrelated evidence properties {unrelated}')
            resolved = []
            for ref in refs:
                if ref not in claims:
                    errors.append(f'{where}: unknown specification claim {ref}')
                else:
                    resolved.append(claims[ref][2])
            doc = cell['document']
            if not isinstance(doc, str):
                errors.append(f'{where}: document must be a string')
            elif doc:
                path, _, anchor = doc.partition('#')
                target = Path(path)
                if (dimension != 'vocabulary' or target.is_absolute() or '..' in target.parts or
                        not path.startswith('docs/') or not path.endswith('.md') or not (root / target).is_file()):
                    errors.append(f'{where}: invalid vocabulary document')
                elif not anchor:
                    errors.append(f'{where}: vocabulary document needs an anchor')
            # A missing executable layer must never be hidden as Not claimed.
            names_only = name == 'type-names'
            if status == 'not-claimed' and not (dimension == 'vocabulary' and not names_only or
                                               names_only and dimension != 'vocabulary'):
                errors.append(f'{where}: required release evidence cannot be excluded')
            if names_only and dimension != 'vocabulary' and status != 'not-claimed':
                errors.append(f'{where}: the naming gate makes no executable claim')
            if status == 'complete':
                if dimension == 'vocabulary':
                    if name != 'type-names' or doc != NAMING_DOCUMENT:
                        errors.append(f'{where}: complete vocabulary needs its reviewed normative document')
                else:
                    incomplete = [f'{ref} ({required_status(dimension, ref)})' for ref in required
                                  if ref not in claims or claims[ref][2].status != required_status(dimension, ref)]
                    if not required or incomplete:
                        errors.append(f'{where}: every mandatory obligation needs its required evidence: {incomplete}')
                if any(c.status == 'planned' for c in resolved):
                    errors.append(f'{where}: a Planned claim cannot complete a dimension')
    if len(row_ids) != len(ROWS) or set(row_ids) != set(ROWS):
        errors.append('index: each of the eight mandatory rows must occur exactly once')
    if covered != ISSUES:
        errors.append('index: every issue must be referenced by a mandatory row')


def rollup(data):
    missing = [f'issue:{i["number"]}' for i in data['issue'] if i['state'] != 'complete']
    missing += [f'{r["id"]}.{d}' for r in data['row'] for d, c in r['dimension'].items()
                if c['state'] not in ('complete', 'not-claimed')]
    return {'release': data['release'], 'complete': not missing, 'missing': missing,
            'authority': 'evidence index only; not a compiler or proof acceptance result'}


def issue_link(number):
    return f'[#{number}](https://github.com/MGYamada/Vastitas/issues/{number})'


def render(data, claims):
    lines = ['# v0.1.0 finite admission and conformance', '',
             '<!-- Generated by scripts/check_release_admission.py from docs/release/v0.1.0.toml. -->', '',
             'This index tracks the finite release requirements of ' + issue_link(417) +
             '. It grants no acceptance and proves no property. Its cells refer to the',
             '[checked specifications](specifications.md); their claim statuses and stated',
             'premises retain their meaning. A complete cell reports reviewed evidence,',
             'not correctness of an external compiler or runtime.', '',
             f'The source inventory starts at `{data["baseline"]}`. The single wire epoch is',
             f'{data["wire"]}. Constructor coverage must follow every admitted change.', '',
             'The dimensions below separate source admission, accepted Core, MidIR,',
             'verified LLVM bytes, Official proof, Fast coverage, native tests, measured',
             'costs and normative vocabulary. The naming row has no executable claim.', '',
             '## Release rollup', '',
             '`python3 scripts/check_release_admission.py --require-complete` fails until',
             'every required dimension and issue has its completion evidence. The command',
             'checks the index and its specification references; it does not run a verifier.', '',
             f'The index has {len(rollup(data)["missing"])} outstanding issue or dimension entries.', '',
             '| Issue | Work | State | Prerequisites | Remaining completion evidence |',
             '| --- | --- | --- | --- | --- |']
    for item in data['issue']:
        lines.append(f'| {issue_link(item["number"])} | {item["title"]} | {item["state"]} | '
                     f'{", ".join(issue_link(n) for n in item["depends"]) or "—"} | {item["remaining"]} |')
    for row in data['row']:
        lines += ['', f'## {row["title"]}', '', row['requirement'], '',
                  'Owners: ' + ', '.join(issue_link(n) for n in row['issues']) + '.', '',
                  '| Dimension | State | Evidence or outstanding obligation |', '| --- | --- | --- |']
        for dimension in DIMENSIONS:
            cell = row['dimension'][dimension]
            links = []
            for ref in cell['claims']:
                spec, prop, claim = claims[ref]
                chapter = spec.chapter.relative_to('docs').as_posix()
                links.append(f'[{prop.title}: {claim.name}]({chapter}#{prop.id})')
            if cell['document']:
                links.append(f'[Naming contract]({cell["document"].removeprefix("docs/")})')
            detail = cell['note'] + (' ' + '; '.join(links) + '.' if links else '')
            lines.append(f'| {dimension} | {cell["state"]} | {detail} |')
    return '\n'.join(lines) + '\n'


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--json', action='store_true', help='print the deterministic rollup')
    parser.add_argument('--require-complete', action='store_true')
    args = parser.parse_args(argv)
    errors = []
    try:
        data = tomllib.loads((ROOT / SOURCE).read_text())
    except (OSError, tomllib.TOMLDecodeError) as error:
        print(f'{SOURCE}: {error}', file=sys.stderr)
        return 1
    state = check_spec.load(ROOT, errors)
    claims = claim_index(state)
    validate(data, claims, ROOT, errors)
    if not errors:
        chapter = render(data, claims)
        if args.write:
            (ROOT / CHAPTER).write_text(chapter)
        elif not (ROOT / CHAPTER).is_file() or (ROOT / CHAPTER).read_text() != chapter:
            errors.append(f'{CHAPTER}: stale; run scripts/check_release_admission.py --write')
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    report = rollup(data)
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(f'Release admission: 23 issues, 8 rows; {len(report["missing"])} outstanding entries')
    if args.require_complete and not report['complete']:
        print('Release evidence incomplete: ' + ', '.join(report['missing']), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
