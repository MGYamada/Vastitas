"""Release reporting must not promote planned or unrelated evidence."""
import copy
from pathlib import Path
import tempfile
import tomllib
from types import SimpleNamespace
import unittest

import check_release_admission as admission


class AdmissionTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / 'docs/language').mkdir(parents=True)
        (self.root / 'docs/language/types.md').write_text('# Types\n\n## Public type names\n')
        self.claims = {}
        self.data = dict(schema=1, release='0.1.0', wire=10, baseline='a' * 40,
            issue=[dict(number=n, title='Work', state='open', depends=[], remaining='Evidence pending.')
                   for n in sorted(admission.ISSUES)], row=[])
        for name in admission.ROWS:
            cells = {}
            for dimension in admission.DIMENSIONS:
                excluded = (name == 'type-names') != (dimension == 'vocabulary')
                required = list(admission.obligations(name, dimension))
                self.claims.update({ref: (None, None, SimpleNamespace(status='planned')) for ref in required})
                cells[dimension] = dict(state='not-claimed' if excluded else 'planned', claims=required,
                                        note='Evidence pending.', document='')
            self.data['row'].append(dict(id=name, title='Required feature',
                issues=sorted(admission.ISSUES), requirement='Full finite profile.', dimension=cells))

    def errors(self, data=None, claims=None):
        errors = []
        admission.validate(self.data if data is None else data,
                           self.claims if claims is None else {**self.claims, **claims}, self.root, errors)
        return errors

    def test_valid_plan_remains_incomplete(self):
        self.assertEqual(self.errors(), [])
        report = admission.rollup(self.data)
        self.assertFalse(report['complete'])
        self.assertIn('functions.llvm', report['missing'])
        self.assertIn('issue:417', report['missing'])
        self.assertNotIn('type-names.native', report['missing'])

    def test_no_missing_duplicate_or_unknown_gate(self):
        for key in ('issue', 'row'):
            for kind in ('missing', 'duplicate', 'extra'):
                data = copy.deepcopy(self.data)
                if kind == 'missing':
                    data[key].pop()
                elif kind == 'duplicate':
                    data[key][-1] = copy.deepcopy(data[key][0])
                else:
                    data[key].append({'unknown': True})
                with self.subTest(key=key, kind=kind):
                    self.assertTrue(self.errors(data))

    def test_cannot_omit_required_layer_or_exclude_native(self):
        cell = self.data['row'][0]['dimension']
        cell.pop('llvm')
        self.assertTrue(self.errors())
        cell['llvm'] = dict(state='not-claimed', claims=[], note='Skip.', document='')
        self.assertTrue(any('cannot be excluded' in e for e in self.errors()))

    def test_planned_claim_and_test_do_not_prove_official_soundness(self):
        cell = self.data['row'][0]['dimension']['official']
        cell.update(state='complete')
        proved = {ref: (None, None, SimpleNamespace(status='proved-oracle')) for ref in cell['claims']}
        for ref in cell['claims']:
            for status in ('planned', 'tested', 'assumed', 'not-claimed', 'proved-bridge'):
                claims = {**proved, ref: (None, None, SimpleNamespace(status=status))}
                with self.subTest(ref=ref, status=status):
                    self.assertTrue(self.errors(claims=claims))
        self.assertEqual(self.errors(claims=proved), [])
        self.assertFalse(admission.rollup(self.data)['complete'])

    def test_complete_native_needs_tested_evidence_and_known_refs(self):
        cell = self.data['row'][0]['dimension']['native']
        cell.update(state='complete')
        ref = cell['claims'][0]
        self.assertTrue(self.errors())
        claims = {ref: (None, None, SimpleNamespace(status='planned'))}
        self.assertTrue(self.errors(claims=claims))
        claims[ref][2].status = 'tested'
        self.assertEqual(self.errors(claims=claims), [])

    def test_complete_parent_cannot_hide_open_dependency_or_cycle(self):
        a, b = self.data['issue'][:2]
        a.update(state='complete', depends=[b['number']])
        self.assertTrue(any('prerequisite' in e for e in self.errors()))
        a['state'] = 'open'
        b['depends'] = [a['number']]
        self.assertTrue(any('cyclic' in e for e in self.errors()))

    def test_naming_contract_cannot_claim_a_native_implementation(self):
        cells = self.data['row'][-1]['dimension']
        cells['vocabulary'].update(state='complete', document=admission.NAMING_DOCUMENT)
        self.assertEqual(self.errors(), [])
        cells['native']['state'] = 'partial'
        self.assertTrue(any('no executable claim' in e for e in self.errors()))

    def test_vocabulary_document_cannot_escape_repository_or_be_missing(self):
        cell = self.data['row'][-1]['dimension']['vocabulary']
        cell['state'] = 'complete'
        for path in ('/tmp/outside.md#names', '../types.md#names', 'docs/missing.md#names', 'docs/types.md'):
            cell['document'] = path
            with self.subTest(path=path):
                self.assertTrue(self.errors())

    def test_unrelated_test_and_oracle_claim_cannot_complete_release(self):
        claims = {'unrelated@test': (None, None, SimpleNamespace(status='tested')),
                  'unrelated@proof': (None, None, SimpleNamespace(status='proved-oracle'))}
        for issue in self.data['issue']:
            issue['state'] = 'complete'
        for row in self.data['row']:
            for dimension, cell in row['dimension'].items():
                if cell['state'] == 'not-claimed':
                    continue
                cell['state'] = 'complete'
                if dimension == 'vocabulary':
                    cell['document'] = admission.NAMING_DOCUMENT
                else:
                    cell['claims'] = ['unrelated@proof' if dimension == 'official' else 'unrelated@test']
        errors = self.errors(claims=claims)
        self.assertTrue(any('missing mandatory' in error for error in errors))
        self.assertTrue(any('unrelated evidence' in error for error in errors))

    def test_complete_requires_all_reviewed_obligations_and_issues(self):
        for issue in self.data['issue']:
            issue['state'] = 'complete'
        for row in self.data['row']:
            for dimension, cell in row['dimension'].items():
                if cell['state'] == 'not-claimed':
                    continue
                cell['state'] = 'complete'
                if dimension == 'vocabulary':
                    cell['document'] = admission.NAMING_DOCUMENT
                for ref in cell['claims']:
                    self.claims[ref][2].status = admission.required_status(dimension, ref)
        self.assertEqual(self.errors(), [])
        self.assertTrue(admission.rollup(self.data)['complete'])

    def test_required_claim_cannot_be_removed_or_replaced_during_partial_progress(self):
        cell = self.data['row'][-2]['dimension']['source']
        cell['state'] = 'partial'
        cell['claims'] = ['compiler-ir.edition@manifest']
        self.assertTrue(any('missing mandatory' in error for error in self.errors()))

    def test_every_required_claim_must_have_the_required_status(self):
        cell = self.data['row'][-2]['dimension']['source']
        cell['state'] = 'complete'
        for ref in admission.obligations('edition-verification', 'source'):
            self.assertTrue(any('every mandatory obligation' in error for error in self.errors()))
            self.claims[ref][2].status = 'tested'
        self.assertEqual(self.errors(), [])

    def test_additional_same_property_evidence_can_explain_partial_progress(self):
        cell = self.data['row'][0]['dimension']['llvm']
        cell.update(state='partial', claims=cell['claims'] + ['compiler-ir.llvm-bytes@parser-test'])
        extra = {'compiler-ir.llvm-bytes@parser-test': (None, None, SimpleNamespace(status='tested'))}
        self.assertEqual(self.errors(claims=extra), [])
        cell['state'] = 'complete'
        self.assertTrue(self.errors(claims=extra))
        for ref in admission.obligations('functions', 'llvm'):
            self.claims[ref][2].status = 'proved-oracle'
        self.assertEqual(self.errors(claims=extra), [])

    def test_byte_replays_cannot_discharge_byte_correspondence(self):
        cell = self.data['row'][1]['dimension']['llvm']
        cell['state'] = 'complete'
        theorem = 'compiler-ir.llvm-bytes@bytes'
        regression = 'compiler-ir.llvm-bytes@switch-regression'
        for ref in admission.obligations('category', 'llvm'):
            self.claims[ref][2].status = admission.required_status('llvm', ref)
        for unproved in ('tested', 'assumed', 'proved-bridge', 'planned'):
            self.claims[theorem][2].status = unproved
            self.assertTrue(self.errors(), unproved)
        self.claims[theorem][2].status = 'proved-oracle'
        self.assertEqual(self.errors(), [])
        self.claims[regression][2].status = 'proved-oracle'
        self.assertTrue(self.errors())

    def test_names_cannot_be_completed_by_an_arbitrary_document(self):
        (self.root / 'docs/other.md').write_text('# Public type names\n')
        self.data['row'][-1]['dimension']['vocabulary'].update(
            state='complete', document='docs/other.md#public-type-names')
        self.assertTrue(any('reviewed normative document' in error for error in self.errors()))

    def test_current_ledger_keeps_every_reviewed_requirement(self):
        data = tomllib.loads((admission.ROOT / admission.SOURCE).read_text())
        for row in data['row']:
            for dimension, cell in row['dimension'].items():
                self.assertEqual(set(admission.obligations(row['id'], dimension)), set(cell['claims']))

    def test_wrong_epoch_and_boolean_schema_are_rejected(self):
        for field, value in (('wire', 9), ('wire', 11), ('schema', True), ('baseline', 'short')):
            data = copy.deepcopy(self.data)
            data[field] = value
            with self.subTest(field=field):
                self.assertTrue(self.errors(data))


if __name__ == '__main__':
    unittest.main()
