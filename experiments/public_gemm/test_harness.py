"""Harness regressions, also run by the dedicated optional-experiment workflow."""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

from cases import cases, driver, source, split_generated
from run import Runner, compare_pair

# Codegen-envelope fixture, deliberately not represented as Lean acceptance.
EMITTED = '''import VastitasStorageNative
import VastitasGemmNative
namespace VastitasGenerated
def f0 : Int := 0
end VastitasGenerated
open VastitasStorageNative
def main : IO Unit := do
  let arena ← newArena 9223372036854775807
  try
    allocate arena 0 0 8
    fill arena 0 0 2 4 2 false 0 4593671619917905920 0
    allocate arena 1 0 12
    fill arena 1 0 4 3 4 false 0 13821547256400052224 0
    allocate arena 2 0 6
    VastitasGemmNative.gemmScaled arena 0 0 2 4 2 false false 1 0 4 3 4 false false 2 0 2 3 2 false 0 1 0 4609434218613702656 0 0 0 0 0 0 0 0 0
    drop arena 2
    drop arena 1
    drop arena 0
    IO.println (VastitasGenerated.f0)
  finally
    close arena
'''


class HarnessTests(unittest.TestCase):
    def test_large_inspection_output_is_retained_once(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            runner = Runner(out,dict(os.environ))
            listing = out / "disassembly.txt"
            size = 3 * 1024 * 1024
            runner.run([sys.executable,"-c",f"import sys; sys.stdout.write('x'*{size}); sys.stderr.write('diagnostic')"],
                       phase="inspection",stdout_path=listing)
            runner.run([sys.executable,"-c","print('next command')"])
            self.assertEqual(listing.read_bytes(),b"x"*size)
            log = out / "commands.json"
            self.assertLess(log.stat().st_size,4096)
            entries = json.loads(log.read_text())
            self.assertEqual(entries[0]["stdout"],"")
            self.assertEqual(entries[0]["stdout_file"],"disassembly.txt")
            self.assertEqual(entries[0]["stdout_bytes"],size)
            self.assertEqual(entries[0]["stderr"],"diagnostic")
            self.assertEqual(entries[1]["stdout"],"next command\n")

    def test_unfamiliar_codegen_must_not_be_benchmarked(self):
        for text in [EMITTED.replace("gemmScaled","gemm"),
                     EMITTED.replace("9223372036854775807","1024"),
                     EMITTED.replace("    drop arena 2","    copy arena 0 0 2 4 2 false 2 0 2 3 2 false\n    drop arena 2"),
                     EMITTED.replace("  finally","  pure ()"),
                     EMITTED.replace("    drop arena 2","    drop arena 1")]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                split_generated(text)

    def test_wrapping_preserves_instructions_and_cleanup(self):
        _, _, setup, gemm, cleanup = split_generated(EMITTED)
        wrapped = driver(EMITTED)
        for instruction in setup+[gemm]+cleanup:
            self.assertEqual(wrapped.count(instruction.strip()),2)
        self.assertEqual(wrapped.count("finally\n"),2)
        self.assertNotIn("IO.println",wrapped)
        self.assertIn("benchVerify arena reps.toUInt64",wrapped)
        self.assertIn("  generatedOnce\n  if impl",wrapped)

    def test_cost_or_output_mismatch_fails_pair(self):
        base = dict(elapsed_ns=42,process_maxrss_kib=123,checksum="abcd",
                    peak_data_bytes=120,copied_bytes=0,timed_data_allocations=0)
        for field in ("checksum","peak_data_bytes","copied_bytes","timed_data_allocations"):
            other = copy.deepcopy(base)
            other[field] = "bad" if field == "checksum" else 1
            with self.subTest(field=field), self.assertRaises(ValueError): compare_pair(base,other)
        compare_pair(base,{**base,"elapsed_ns":84,"process_maxrss_kib":234})

    def test_cross_product_and_coefficient_semantics(self):
        cs = cases()
        self.assertEqual(len(cs),24)
        self.assertEqual(len({c["case"] for c in cs}),24)
        for c in cs:
            text = source(c)
            self.assertEqual(text.count("gemm("),1)
            self.assertIn("alpha=",text)
            self.assertEqual("beta=" in text,bool(c["accumulate"]))
            self.assertEqual("read_write(c," in text,bool(c["accumulate"]))
            self.assertEqual(len({c["m"],c["n"],c["k"]}),3)


if __name__ == "__main__":
    unittest.main()
