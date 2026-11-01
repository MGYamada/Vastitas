"""Harness-only regressions; actual public/native validation is run.py's job."""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

from cases import cases, driver, entry, middle, product, source, spec, split_generated
from run import Runner, compare_pair, sha, verify_inputs

# Synthetic codegen envelope tests are not represented as Lean acceptance.
EMITTED = "import VastitasStorageNative\nimport VastitasGemmNative\nopen VastitasStorageNative\n" + "def main : IO Unit := do\n  let arena ← newArena 9223372036854775807\n  try\n" + "".join(f"    allocate arena {n} 0 100\n" for n in range(6)) + "    pack3 arena 0 0 2 12 2 false 3 0 8 3 8 false 2 3 4\n    VastitasGemmNative.gemm arena 3 0 8 3 8 false false 1 0 3 5 3 false false 4 0 8 5 8 false 0\n    regroup3 arena 4 0 8 5 8 false 3 0 10 4 10 false 2 4 5 48 42\n    VastitasGemmNative.gemm arena 3 0 10 4 10 false false 2 0 4 6 4 false false 5 0 10 6 10 false 0\n" + "".join(f"    expect arena 5 0 10 6 10 false {n} 0 0 0 0\n" for n in range(3)) + "".join(f"    drop arena {n}\n" for n in range(5,-1,-1)) + "    IO.println (VastitasGenerated.f_0)\n  finally\n    close arena\n"


class HarnessTests(unittest.TestCase):
    def test_changed_compiler_or_source_is_not_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/"compiler"
            path.write_bytes(b"original")
            hashes = {str(path):sha(path)}
            verify_inputs(hashes)
            path.write_bytes(b"changed")
            with self.assertRaises(ValueError): verify_inputs(hashes)

    def test_inspection_log_is_bounded(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory); runner = Runner(out,dict(os.environ))
            listing = out/"disassembly.txt"; size = 3*1024*1024
            runner.run([sys.executable,"-c",f"import sys; sys.stdout.write('x'*{size})"],stdout_path=listing)
            runner.run([sys.executable,"-c","print('done')"])
            self.assertEqual(listing.stat().st_size,size)
            self.assertLess((out/"commands.json").stat().st_size,4096)
            self.assertEqual(json.loads((out/"commands.json").read_text())[0]["stdout"],"")

    def test_unfamiliar_codegen_fails_closed(self):
        for text in [EMITTED.replace("gemm arena","gemmScaled arena"),
                     EMITTED.replace("9223372036854775807","1024"),
                     EMITTED.replace("    regroup3 arena","    copy arena"),
                     EMITTED.replace("    drop arena 5","    drop arena 1"),
                     EMITTED.replace("  finally","  pure ()"),
                     EMITTED.replace("    expect arena 5","    expect arena 4")]:
            with self.subTest(text=text),self.assertRaises(ValueError): split_generated(text)

    def test_wrapper_preserves_actual_order_and_cleanup(self):
        _,_,setup,operations,cleanup = split_generated(EMITTED)
        wrapped = driver(EMITTED)
        for instruction in setup+operations+cleanup:
            self.assertEqual(wrapped.count(instruction.strip()),2)
        self.assertEqual(wrapped.count("finally\n"),2)
        self.assertIn("benchVerify arena reps.toUInt64",wrapped)
        self.assertNotIn("IO.println",wrapped)

    def test_pair_rejects_cost_or_output_mismatch(self):
        base = dict(elapsed_ns=42,process_maxrss_kib=1,checksum="abcd",copied_bytes=512,timed_data_allocations=0)
        for field in ("checksum","copied_bytes","timed_data_allocations"):
            other = copy.deepcopy(base); other[field] = "bad" if field=="checksum" else 1
            with self.assertRaises(ValueError): compare_pair(base,other)
        compare_pair(base,{**base,"elapsed_ns":84,"process_maxrss_kib":2})

    def test_unit_cleanup_keeps_operations_and_rejects_lost_rethrow(self):
        emitted = EMITTED.replace("  finally\n    close arena\n",
            "  catch cleanupError =>\n    close arena\n    throw cleanupError\n  close arena\n")
        self.assertEqual(split_generated(emitted), split_generated(EMITTED))
        wrapped = driver(emitted)
        self.assertNotIn("finally", wrapped)
        self.assertEqual(wrapped.count("catch cleanupError =>"), 2)
        self.assertEqual(wrapped.count("throw cleanupError"), 2)
        self.assertEqual(wrapped.count("close arena"), 4)
        for instructions in split_generated(emitted)[2:]:
            for instruction in instructions:
                self.assertEqual(wrapped.count(instruction.strip()), 2)
        for bad in (emitted.replace("    throw cleanupError\n", ""),
                    emitted.replace("  close arena\n", ""),
                    emitted.replace("throw cleanupError", "pure ()")):
            with self.assertRaises(ValueError): driver(bad)

    def test_both_flat_copy_mutations_change_final_product(self):
        for c in cases():
            s = spec(c); i,k,j,a = (c[x] for x in ("i","k","j","a"))
            def wrong_middle(x,y,col):
                return sum((entry(s,0,x,(y+j*z)%k+k*((y+j*z)//k))*entry(s,1,z,col)
                            for z in range(k)),0j)
            # The first expression intentionally preserves logical flat order:
            # input column y+j*z corresponds to the wrong z/y coordinate.
            for stage in range(2):
                changed = False
                for col in (0,c["b"]-1):
                    for aa in (0,a-1):
                        x=i-1
                        got=sum(((wrong_middle(x,y,aa) if stage==0 else
                                  middle(c,s,x,(aa+a*y)%j,(aa+a*y)//j))*entry(s,2,y,col)
                                 for y in range(j)),0j)
                        changed |= got != product(c,s,x+i*aa,col)
                with self.subTest(case=c["case"],stage=stage): self.assertTrue(changed)

    def test_scratch_capacity_and_two_directions(self):
        directions=set()
        for c in cases():
            s=spec(c); width=s["width"]
            directions.add(c["k"]>c["a"])
            for n in (3,6):
                offset,rows,cols,leading,_=s["layouts"][n]
                self.assertGreaterEqual(s["elements"][3],offset//width+leading*(cols-1)+rows)
        self.assertEqual(directions,{False,True})

    def test_bounded_source_keeps_exact_tree_work(self):
        self.assertEqual(len(cases()),12); self.assertEqual(len(cases(True)),4)
        for c in cases():
            text=source(c)
            self.assertEqual(text.count("allocate "),6)
            self.assertEqual(text.count("regroup("),2)
            self.assertEqual(text.count("join "),2)
            self.assertEqual(text.count("store("),6)
            self.assertEqual(text.count("expect("),3)
            self.assertEqual(len({c[x] for x in ("i","k","j","a","b")}),5)
            self.assertLess(len(text),6500)


if __name__ == "__main__": unittest.main()
