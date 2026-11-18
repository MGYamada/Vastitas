"""Harness transformations and independent cost-oracle mutations."""
import copy
import json
from pathlib import Path
import re
import unittest
import zipfile

from cases import cleanup_envelope, driver, shapes, source, split_generated
from run import pair
from verify import expected, verify


class Tests(unittest.TestCase):
    def test_public_source_has_two_extent_calls_and_explicit_reuse(self):
        for scalar in (0,1):
            for transposed in (0,1):
                text=source(scalar,transposed,True)
                self.assertEqual(text.count("call run("),2)
                self.assertEqual(text.count("call multiply("),2)
                self.assertEqual(text.count("runtime_allocate "),3)
                self.assertNotIn("copy(",text)
                self.assertNotIn("pack3(",text)
        self.assertEqual(len(shapes()),6)

    def test_changed_envelope_is_rejected(self):
        for text in ("", "def main : IO Unit := do\n  pure ()\n"):
            with self.assertRaises(ValueError):split_generated(text)

    def test_status_entry_preserves_runtime_inputs_and_cleanup(self):
        archive=Path(__file__).parent/"results/2026-11-01-macos/evidence.zip"
        with zipfile.ZipFile(archive) as record:
            for profile in ("real-normal", "real-transpose", "complex-normal", "complex-transpose"):
                emitted=json.loads(record.read(profile+"/response.json"))["lean_source"]
                current=emitted.replace('def main : IO Unit := do\n',
                    'def main : IO UInt32 := do\n  let mut status : UInt32 := 0\n')
                current=re.sub(r'    IO.println \((VastitasGenerated\.[A-Za-z0-9_]+(?: resourceValue_[0-9]+)*)\)',
                    lambda m: f'    status := (UInt32.ofNat (Int.toNat (Int.emod ({m[1]}) 256)))', current)
                current=current.replace('  finally\n    close shapeArena\n',
                    '  catch cleanupError =>\n    close shapeArena\n    throw cleanupError\n  close shapeArena\n')+'  pure status\n'
                with self.subTest(profile=profile):
                    self.assertEqual(split_generated(current),split_generated(emitted))
                    wrapped=driver(current)
                    self.assertNotIn('pure status',wrapped)
                    self.assertEqual(wrapped.count('throw cleanupError'),2)
                    cleanup_envelope.require_execution(current,dict(returncode=0,stdout='',stderr=''))
                    with self.assertRaises(ValueError):
                        split_generated(current.replace('  pure status','  pure 0'))

    def test_cost_and_padding_hash_distinguish_scope_shape_and_scalar(self):
        base=dict(profile="real-normal",m=2,k=3,n=4,pad=0,repetitions=3,scope=0,implementation="generated")
        life=expected(base);reuse=expected(dict(base,scope=1))
        self.assertEqual(life["data_allocations"],9)
        self.assertEqual(reuse["data_allocations"],3)
        self.assertEqual(reuse["scope_data_allocations"],0)
        self.assertEqual(reuse["scope_written_bytes"],384)
        self.assertEqual(life["checksum"],reuse["checksum"])
        self.assertNotEqual(life["checksum"],expected(dict(base,pad=2))["checksum"])
        self.assertEqual(expected(dict(base,k=0,pad=1))["blas_calls"],0)
        self.assertEqual(expected(dict(base,m=0,pad=1))["scope_written_bytes"],3*8*3*4)
        self.assertEqual(expected(dict(base,profile="complex-normal"))["written_bytes"],2*life["written_bytes"])

    def test_pair_cannot_hide_wrong_cost_or_output(self):
        base=dict(checksum="abc",written_bytes=32,scope_nat_narrowings=9)
        pair(base,dict(base,scope_nat_narrowings=0))
        for key in ("checksum","written_bytes"):
            bad=copy.copy(base);bad[key]="wrong"
            with self.assertRaises(ValueError):pair(base,bad)

    def test_verifier_rejects_unsupported_scenarios(self):
        archive=Path(__file__).parent/"results/2026-11-01-macos/evidence.zip"
        with zipfile.ZipFile(archive) as record:
            original=json.loads(record.read("records.json"))
            for field,before,after in (("scope",1,2),("scope",1,True),("profile","real-normal","unsupported"),("repetitions",3,5)):
                changed=copy.deepcopy(original)
                for row in changed:
                    if row[field]==before:row[field]=after
                def read(name):
                    return json.dumps(changed).encode() if name=="records.json" else record.read(name)
                with self.subTest(field=field),self.assertRaises(AssertionError):verify(read,record.namelist())

    def test_verifier_rejects_duplicate_native_and_failure_coverage(self):
        archive=Path(__file__).parent/"results/2026-11-01-macos/evidence.zip"
        with zipfile.ZipFile(archive) as record:
            for filename in ("native-validation.json","failure-validation.json"):
                changed=json.loads(record.read(filename));changed[-1]=copy.deepcopy(changed[0])
                def read(name):
                    return json.dumps(changed).encode() if name==filename else record.read(name)
                with self.subTest(filename=filename),self.assertRaises(AssertionError):verify(read,record.namelist())


if __name__=="__main__":unittest.main()
