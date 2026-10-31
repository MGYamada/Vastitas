"""Standalone harness regressions; invoke with unittest discovery."""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

from cases import cases, driver, source, spec, split_generated
from run import Runner, compare_pair

# Codegen-envelope fixture, deliberately not represented as Lean acceptance.
EMITTED = 'import VastitasStorageNative\nimport VastitasGemmNative\nimport VastitasKernel.IndexedRuntime\n\nset_option maxRecDepth 32768\nset_option maxHeartbeats 2000000\nset_option linter.unusedVariables false\n\nnamespace VastitasGenerated\n\ndef f_0 : Int :=\n  (0 : Int)\n\nend VastitasGenerated\n\nopen VastitasStorageNative\n\ndef main : IO Unit := do\n  let arena ← newArena 9223372036854775807\n  try\n    allocate arena 0 1 52\n    fill arena 0 0 52 1 52 false 1 13842939354630062080 4613937818241073152\n    fill arena 0 16 2 12 4 false 1 4593671619917905920 4598175219545276416\n    store arena 0 16 2 12 4 false 0 0 1 4607182418800017408 13826050856027422720\n    store arena 0 16 2 12 4 false 1 11 1 13826050856027422720 4604930618986332160\n    allocate arena 1 1 35\n    fill arena 1 0 35 1 35 false 1 13842939354630062080 4613937818241073152\n    fill arena 1 32 3 5 6 false 1 13821547256400052224 4593671619917905920\n    store arena 1 32 3 5 6 false 0 4 1 4602678819172646912 4598175219545276416\n    store arena 1 32 3 5 6 false 2 0 1 13828302655841107968 13826050856027422720\n    allocate arena 2 1 42\n    fill arena 2 0 42 1 42 false 1 13842939354630062080 4613937818241073152\n    allocate arena 3 1 72\n    fill arena 3 0 72 1 72 false 1 13842939354630062080 4613937818241073152\n    pack3 arena 0 16 2 12 4 false 2 48 8 3 12 false 2 3 4\n    VastitasGemmNative.gemm arena 2 48 8 3 12 false false 1 32 3 5 6 false false 3 64 8 5 13 false 0\n    drop arena 3\n    drop arena 2\n    drop arena 1\n    drop arena 0\n    IO.println (VastitasGenerated.f_0)\n  finally\n    close arena\n'


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
        for text in [EMITTED.replace("gemm arena","gemmScaled arena"),
                     EMITTED.replace("9223372036854775807","1024"),
                     EMITTED.replace("    drop arena 3","    copy arena 0 0 2 4 2 false 3 0 2 3 2 false\n    drop arena 3"),
                     EMITTED.replace("  finally","  pure ()"),
                     EMITTED.replace("    drop arena 3","    drop arena 1"),
                     EMITTED.replace("    pack3 arena", "    fill arena")]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                split_generated(text)

    def test_wrapping_preserves_instructions_and_cleanup(self):
        _, _, setup, operation, cleanup = split_generated(EMITTED)
        wrapped = driver(EMITTED)
        for instruction in setup+operation+cleanup:
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

    def test_every_fixture_detects_omitting_the_pack_permutation(self):
        # Mutation: write the input's logical flat order directly into scratch.
        # First/last-only patches cannot distinguish this wrong implementation.
        for case in cases():
            fixture = spec(case)
            patches = {(r,col):value for r,col,value in fixture["patches"][0]}
            def at(x,z,y):
                return patches.get((x,z+case["k"]*y),fixture["values"][0])
            flat_copy = [at(x,z,y) for y in range(case["j"])
                         for z in range(case["k"]) for x in range(case["i"])]
            packed = [at(x,z,y) for z in range(case["k"])
                      for y in range(case["j"]) for x in range(case["i"])]
            with self.subTest(case=case["case"]):
                self.assertNotEqual(flat_copy,packed)

    def test_cross_product_has_bounded_source_size(self):
        cs = cases()
        self.assertEqual(len(cs),12)
        self.assertEqual(len(cases(True)),4)
        self.assertEqual(len({c["case"] for c in cs}),12)
        for c in cs:
            text = source(c)
            self.assertEqual(text.count("pack3("),1)
            self.assertEqual(text.count("contract3("),1)
            self.assertEqual(text.count("store("),4)
            self.assertEqual(text.count("allocate "),4)
            self.assertEqual(len({c["i"],c["k"],c["j"],c["l"]}),4)
        self.assertLess(max(len(source(c)) for c in cs),4000)


if __name__ == "__main__":
    unittest.main()
