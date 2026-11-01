"""Fail-closed experiment transformations; runtime validation is run.py's job."""
import copy
import importlib.util
import json
import itertools
from pathlib import Path
import unittest
import zipfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('allocation_runner', HERE / 'run.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
verify_spec = importlib.util.spec_from_file_location('allocation_verifier_v2', HERE / 'verify.py')
verifier = importlib.util.module_from_spec(verify_spec)
verify_spec.loader.exec_module(verifier)


class AuditTests(unittest.TestCase):
    def verify_mutated_record(self, mutate, variant='production_shared', implementation='generated', scope=0):
        """Mutate semantic records and matching raw stdout, not archive hashes."""
        with zipfile.ZipFile(HERE / 'results/2026-11-01-macos-production/evidence.zip') as archive:
            files = {name: archive.read(name) for name in archive.namelist()}
        rows = json.loads(files['allocations.json'])
        index = next(i for i, row in enumerate(rows) if row['variant'] == variant
                     and row['implementation'] == implementation and row['scope'] == scope
                     and row['repetitions'] == 1)
        mutate(rows[index])
        commands = json.loads(files['commands.json'])
        command = [item for item in commands if item['phase'] == 'allocation_audit'][index]
        command['stdout'] = json.dumps(rows[index]['costs']) + '\n' + json.dumps(rows[index]['audit']) + '\n'
        files['allocations.json'] = json.dumps(rows).encode()
        files['commands.json'] = json.dumps(commands).encode()
        return verifier.verify(files.__getitem__, files)

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

    def test_production_once_and_persistence_remain_actual(self):
        source = 'prefix\n' + audit.SHARED_HELPER + '\nsuffix'
        observed = audit.unit_helper(source, 'production_shared')
        self.assertEqual(observed.count('audit_shared_create()'), 1)
        self.assertEqual(observed.count('audit_shared_return(result)'), 1)
        for operation in ('lean_obj_once(&unit_success, &success_once, initialize_success)',
                          'lean_mark_persistent(result)', 'lean_inc(result)'):
            self.assertIn(operation, observed)
        threaded = audit.unit_helper(source, 'production_shared', threaded=True)
        self.assertIn('lean_io_result_mk_ok(lean_box(0))', threaded)
        self.assertIn('allocation_thread_initialize(result)', threaded)
        self.assertNotIn('audit_shared_create', threaded)
        fresh = audit.unit_helper(source, 'private_fresh')
        self.assertNotIn('lean_obj_once', fresh)
        self.assertNotIn('lean_mark_persistent', fresh)
        self.assertIn('EXPERIMENT ONLY', fresh)
        self.assertTrue(fresh.startswith('prefix\n') and fresh.endswith('\nsuffix'))

    def test_changed_production_helper_fails_closed(self):
        for changed in (
            audit.SHARED_HELPER.replace('lean_mark_persistent(result);', ''),
            audit.SHARED_HELPER.replace('lean_inc(result);', ''),
            audit.SHARED_HELPER.replace('lean_obj_once(', 'other_once('),
            audit.SHARED_HELPER + audit.SHARED_HELPER,
        ):
            for variant in ('production_shared', 'private_fresh'):
                with self.subTest(variant=variant), self.assertRaises(ValueError):
                    audit.unit_helper(changed, variant)
        with self.assertRaises(ValueError):audit.unit_helper(audit.SHARED_HELPER, 'prototype')
        with self.assertRaises(ValueError):audit.unit_helper(audit.SHARED_HELPER, 'private_fresh', threaded=True)

    def test_v2_verifier_requires_exact_scenario_domain(self):
        cases = audit.fixtures.cases(True)
        rows = [dict(case=case['case'], variant=variant, scope=scope, repetitions=reps, implementation=impl)
                for case,variant,scope,reps,impl in itertools.product(cases,verifier.VARIANTS,(0,1),(1,2,17),('generated','c'))]
        environment = dict(schema=2,variants=list(verifier.VARIANTS),recorded_inputs_unchanged=True,selection='smoke')
        for field,before,after in (('scope',1,2),('scope',1,True),('variant','production_shared','pthread_prototype'),('repetitions',2,3)):
            changed=copy.deepcopy(rows)
            for row in changed:
                if row[field]==before:row[field]=after
            files={'environment.json':environment,'cases.json':cases,'allocations.json':changed}
            with self.subTest(field=field),self.assertRaises(AssertionError):
                verifier.verify(lambda name:json.dumps(files[name]).encode(),files)

    def test_v2_verifier_does_not_hide_a_second_persistent_object(self):
        kinds=('ffi_ok','arena_external','generated_ctor','control','ffi_error','persistent_unit')
        empty=dict(allocations=0,bytes=0,final_releases=0,released_bytes=0,retained_returns=0)
        record=dict(schema=2,variant='production_shared',shared_result=True,tracked_live_bytes=16,tracked_peak_bytes=16,
                    phases={phase:dict.fromkeys(verifier.ARENA_FIELDS, 0) | dict(kinds={kind:copy.copy(empty) for kind in kinds})
                            for phase in ('startup','cold','setup','run','cleanup')})
        record['phases']['cold']['kinds']['persistent_unit'].update(allocations=1,bytes=16)
        verifier.balanced(record)
        record['phases']['cold']['kinds']['persistent_unit']['allocations']=2
        with self.assertRaises(AssertionError):verifier.balanced(record)

    def test_retained_production_record_passes_stricter_accounting(self):
        result = self.verify_mutated_record(lambda row: None)
        self.assertEqual((result['records'], result['pairs']), (96, 48))

    def test_v2_verifier_rejects_extra_balanced_run_allocations(self):
        for kind, implementation in itertools.product(('ffi_error', 'persistent_unit'), ('generated', 'c')):
            def extra(row):
                counts = row['audit']['phases']['run']['kinds'][kind]
                for field, amount in (('allocations', 1), ('final_releases', 1),
                                      ('bytes', 16), ('released_bytes', 16)):
                    counts[field] += amount
            with self.subTest(kind=kind, implementation=implementation), self.assertRaises(AssertionError):
                self.verify_mutated_record(extra, implementation=implementation)

    def test_v2_verifier_checks_each_implementation_variant_peak(self):
        for variant, implementation, scope in itertools.product(verifier.VARIANTS, ('generated', 'c'), (0, 1)):
            def wrong_peak(row):
                row['audit']['tracked_peak_bytes'] += 1
            with self.subTest(variant=variant, implementation=implementation, scope=scope), self.assertRaises(AssertionError):
                self.verify_mutated_record(wrong_peak, variant, implementation, scope)

    def test_v2_verifier_rejects_negative_boolean_and_fractional_counts(self):
        def negative_balanced(row):
            counts = row['audit']['phases']['startup']['kinds']['ffi_error']
            counts.update(allocations=-1, final_releases=-1, bytes=-16, released_bytes=-16)
        mutations = (
            negative_balanced,
            lambda row: row['audit']['phases']['cold'].__setitem__('arena_finalizers', True),
            lambda row: row['audit']['phases']['cold']['kinds']['arena_external'].__setitem__('allocations', 1.0),
            lambda row: row['costs'].__setitem__('selected_pack_calls_timed', False),
            lambda row: row['costs'].__setitem__('metadata_allocations', 2.0),
            lambda row: row['audit'].__setitem__('tracked_peak_bytes', 88.0),
        )
        for index, mutate in enumerate(mutations):
            with self.subTest(mutation=index), self.assertRaises(AssertionError):
                self.verify_mutated_record(mutate)

if __name__ == '__main__': unittest.main()
