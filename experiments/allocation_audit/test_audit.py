"""Fail-closed experiment transformations; runtime validation is run.py's job."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('allocation_runner', HERE / 'run.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AuditTests(unittest.TestCase):
    def test_failure_changes_only_one_expected_bit(self):
        for kind, bits in [('f64', {'bits': 42}), ('complex_f64', {'real': 42, 'imaginary': 84})]:
            statements = [dict(op='expect', loan='output', row=n, column=0,
                               value=dict(kind=kind, **bits)) for n in range(3)]
            original = dict(version=8, body=[dict(op='fill', value=copy.deepcopy(statements[0]['value'])), *statements])
            expected = copy.deepcopy(original)
            key = 'bits' if kind == 'f64' else 'real'
            expected['body'][1]['value'][key] ^= 1
            self.assertEqual(audit.failure_wire(json.dumps(original)), expected)
            self.assertEqual(original['body'][1]['value'][key], 42)

    def test_changed_assertion_profile_is_rejected(self):
        for count in (0, 2, 4):
            with self.subTest(count=count), self.assertRaises(ValueError):
                audit.failure_wire(json.dumps([dict(op='expect', value=dict(kind='f64', bits=1))] * count))

    def test_instrumentation_rejects_missing_or_ambiguous_site(self):
        for text in ('unrelated', 'site and site'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                audit.replace_once(text, 'site', 'observer')
        self.assertEqual(audit.replace_once('before site after', 'site', 'observer'), 'before observer after')

if __name__ == '__main__': unittest.main()
