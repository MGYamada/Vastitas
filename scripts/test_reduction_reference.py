"""Mutation, exact arithmetic, binary64 and CLI regressions for #303.

Enumerations below are finite experiments, never proofs of general laws.
"""

from copy import deepcopy
from dataclasses import asdict
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import random
import struct
import subprocess
import sys
import tempfile
import unittest

from reduction_fixtures import float_target, leaf, matrix_target, node, plan, scalar_target, target
from reduction_reference import (
    ADD, BINARY64, EXACT, FLOAT_ADD, MATMUL, MATMUL_V2, MUL, SUB,
    Bits64, Failure, _round_binary64, add_binary64, check, law_reference, load_json, matmul,
)


def trees(ids: tuple[str, ...], binding):
    if len(ids) == 1:
        yield leaf(ids[0])
    for split in range(1, len(ids)):
        for left in trees(ids[:split], binding):
            for right in trees(ids[split:], binding):
                yield node(binding, left, right)


def bits_float(bits: int) -> float:
    return struct.unpack(">d", bits.to_bytes(8, "big"))[0]


def float_bits(value: float) -> int:
    return int.from_bytes(struct.pack(">d", value), "big")


class ReductionTests(unittest.TestCase):
    def assert_result(self, expected, t, c, code=None):
        r = check(t, c)
        self.assertEqual(r["status"], expected, r)
        if code:
            self.assertEqual(r["code"], code, r)
        return r

    def matrix_plan(self):
        t = matrix_target()
        return t, plan(t, node(MATMUL, leaf("A"), node(MATMUL, leaf("B"), leaf("C"))), "matmul-v1-assoc")

    def test_user_exact_noncommutative_example(self):
        a, b, c = (((1, 1), (0, 1)), ((1, 0), (1, 1)), ((1, 2), (0, 1)))
        self.assertEqual(matmul(matmul(a, b), c), ((2, 5), (1, 3)))
        self.assertEqual(matmul(a, matmul(b, c)), ((2, 5), (1, 3)))
        self.assertEqual(matmul(matmul(b, a), c), ((1, 3), (1, 4)))

    def test_order_preserving_reassociation(self):
        t, c = self.matrix_plan()
        r = self.assert_result("accepted", t, c)
        self.assertFalse(r["audit"]["same_bracketing"])
        self.assertTrue(r["audit"]["order_preserved"])
        self.assertEqual(r["audit"]["candidate_value"], [["2", "5"], ["1", "3"]])

    def test_exact_unchanged_tree_needs_no_law(self):
        t = scalar_target(SUB)
        c = plan(t, node(SUB, node(SUB, leaf("a"), leaf("b")), leaf("c")))
        r = self.assert_result("accepted", t, c)
        self.assertEqual(r["audit"]["candidate_value"], "-5")

    def test_reassociation_needs_law_even_when_values_coincide(self):
        t = scalar_target(SUB, ["0", "0", "0"])
        c = plan(t, node(SUB, leaf("a"), node(SUB, leaf("b"), leaf("c"))))
        self.assert_result("rejected", t, c, "ASSOCIATIVITY_REQUIRED")

    def test_permutation_does_not_follow_from_associativity(self):
        t = matrix_target(permutation=True)
        c = plan(t, node(MATMUL, node(MATMUL, leaf("B"), leaf("A")), leaf("C")), "matmul-v1-assoc")
        self.assert_result("rejected", t, c, "COMMUTATIVITY_REQUIRED")

    def test_independent_target_can_forbid_even_commutative_permutation(self):
        t = scalar_target()
        c = plan(t, node(ADD, node(ADD, leaf("b"), leaf("a")), leaf("c")), "qq-add-assoc", "qq-add-comm")
        self.assert_result("rejected", t, c, "LEAF_ORDER")

    def test_commutativity_and_associativity_allow_exact_permutation(self):
        t = scalar_target(permutation=True)
        c = plan(t, node(ADD, leaf("b"), node(ADD, leaf("c"), leaf("a"))), "qq-add-assoc", "qq-add-comm")
        r = self.assert_result("accepted", t, c)
        self.assertEqual(r["audit"]["candidate_value"], "9")

    def test_commutativity_alone_does_not_admit_arbitrary_tree(self):
        t = scalar_target(permutation=True)
        c = plan(t, node(ADD, leaf("b"), node(ADD, leaf("c"), leaf("a"))), "qq-add-comm")
        self.assert_result("rejected", t, c, "ASSOCIATIVITY_REQUIRED")

    def test_equal_matrix_values_do_not_grant_commutativity(self):
        t = matrix_target(permutation=True)
        for i in t["inputs"]:
            i["value"] = [["1", "0"], ["0", "1"]]
        c = plan(t, node(MATMUL, node(MATMUL, leaf("B"), leaf("A")), leaf("C")), "matmul-v1-assoc")
        self.assert_result("rejected", t, c, "COMMUTATIVITY_REQUIRED")

    def test_missing_and_duplicate_occurrences(self):
        t, _ = self.matrix_plan()
        for tree in (node(MATMUL, leaf("A"), leaf("B")),
                     node(MATMUL, node(MATMUL, leaf("A"), leaf("B")), leaf("B")),
                     node(MATMUL, node(MATMUL, leaf("A"), leaf("A")),
                          node(MATMUL, leaf("B"), leaf("C")))):
            with self.subTest(tree=tree):
                self.assert_result("rejected", t, plan(t, tree, "matmul-v1-assoc"), "LEAF_MULTIPLICITY")

    def test_equal_payload_occurrences_cannot_be_deduplicated(self):
        t = scalar_target(values=["1", "1", "1"])
        c = plan(t, node(ADD, leaf("a"), node(ADD, leaf("b"), leaf("b"))), "qq-add-assoc")
        self.assert_result("rejected", t, c, "LEAF_MULTIPLICITY")

    def test_equal_payload_distinct_occurrences_are_preserved(self):
        t = scalar_target(values=["1", "1", "1"])
        c = plan(t, node(ADD, leaf("a"), node(ADD, leaf("b"), leaf("c"))), "qq-add-assoc")
        self.assertEqual(self.assert_result("accepted", t, c)["audit"]["candidate_value"], "3")

    def test_unknown_leaf_identity(self):
        t, c = self.matrix_plan()
        c["tree"]["left"]["leaf"] = "same-value-but-other-occurrence"
        self.assert_result("rejected", t, c, "LEAF_IDENTITY")

    def test_stale_leaf_revision(self):
        t, c = self.matrix_plan()
        c["tree"]["left"]["revision"] = "input-v0"
        self.assert_result("rejected", t, c, "LEAF_REVISION")

    def test_candidate_cannot_supply_leaf_payload(self):
        t, c = self.matrix_plan()
        c["tree"]["left"]["value"] = [["0", "0"], ["0", "0"]]
        self.assert_result("rejected", t, c, "SCHEMA")

    def test_duplicate_target_occurrence_ids_rejected(self):
        t, c = self.matrix_plan()
        t["inputs"][1]["id"] = "A"
        self.assert_result("rejected", t, c, "TARGET_OCCURRENCES")

    def test_candidate_cannot_select_or_downgrade_contract(self):
        t, c = self.matrix_plan()
        c["contract"] = {"kind": "relaxed"}
        self.assert_result("rejected", t, c, "SCHEMA")

    def test_wrong_target_id(self):
        t, c = self.matrix_plan()
        c["target_id"] = "different-request"
        self.assert_result("rejected", t, c, "TARGET_ID")

    def test_candidate_law_tags_and_checked_flags_are_not_evidence(self):
        for key, value in (("laws", ["associative", "commutative"]), ("checked", True),
                           ("proof", "Lean says true"), ("result", [[2, 5], [1, 3]])):
            t, c = self.matrix_plan()
            c[key] = value
            with self.subTest(key=key):
                self.assert_result("rejected", t, c, "SCHEMA")

    def test_unknown_candidate_certificate(self):
        t, c = self.matrix_plan()
        c["evidence"][0]["certificate"] = "self-issued-associativity"
        self.assert_result("rejected", t, c, "UNKNOWN_EVIDENCE")

    def test_candidate_cannot_upgrade_law_tag(self):
        t, c = self.matrix_plan()
        c["evidence"][0]["law"] = "commutative"
        self.assert_result("rejected", t, c, "EVIDENCE_RECORD")

    def test_other_operation_evidence(self):
        t, c = self.matrix_plan()
        c["evidence"] = [law_reference("qq-add-assoc")]
        self.assert_result("rejected", t, c, "EVIDENCE_SUBJECT")

    def test_stale_revision_evidence_with_unchanged_semantics(self):
        t = matrix_target(binding=MATMUL_V2)
        c = plan(t, node(MATMUL_V2, leaf("A"), node(MATMUL_V2, leaf("B"), leaf("C"))), "matmul-v1-assoc")
        self.assert_result("rejected", t, c, "EVIDENCE_SUBJECT")
        c["evidence"] = [law_reference("matmul-v2-assoc")]
        self.assert_result("accepted", t, c)

    def test_evidence_record_mutations(self):
        mutations = (("operation", "other::mul"), ("revision", "v0"),
                     ("carrier", "Mat3(QQ)"), ("coefficients", "ZZ-canonical-v1"))
        for key, value in mutations:
            t, c = self.matrix_plan()
            c["evidence"][0]["subject"][key] = value
            with self.subTest(key=key):
                self.assert_result("rejected", t, c, "EVIDENCE_RECORD")
        for key in asdict(EXACT):
            t, c = self.matrix_plan()
            c["evidence"][0]["subject"]["profile"][key] = "other"
            with self.subTest(profile=key):
                self.assert_result("rejected", t, c, "EVIDENCE_RECORD")

    def test_profile_reuse_between_exact_and_float_addition(self):
        t = float_target()
        c = plan(t, t["contract"]["tree"], "qq-add-assoc")
        self.assert_result("rejected", t, c, "EVIDENCE_SUBJECT")

    def test_all_evidence_is_audited_even_if_unused(self):
        t = matrix_target()
        c = plan(t, node(MATMUL, node(MATMUL, leaf("A"), leaf("B")), leaf("C")), "qq-add-comm")
        self.assert_result("rejected", t, c, "EVIDENCE_SUBJECT")

    def test_duplicate_evidence_rejected(self):
        t, c = self.matrix_plan()
        c["evidence"].append(deepcopy(c["evidence"][0]))
        self.assert_result("rejected", t, c, "DUPLICATE_EVIDENCE")

    def test_plan_binding_each_field_compared_to_target(self):
        for key in ("operation", "revision", "carrier", "coefficients"):
            t, c = self.matrix_plan()
            c["binding"][key] = "different"
            with self.subTest(key=key):
                self.assert_result("rejected", t, c, "PLAN_BINDING")
        for key in asdict(BINARY64):
            t = float_target()
            c = plan(t, t["contract"]["tree"])
            c["binding"]["profile"][key] = "different"
            with self.subTest(profile=key):
                self.assert_result("rejected", t, c, "PLAN_BINDING")

    def test_inner_node_selected_operation_is_checked(self):
        t, c = self.matrix_plan()
        c["tree"]["right"]["binding"] = asdict(ADD)
        self.assert_result("rejected", t, c, "NODE_BINDING")

    def test_inner_node_revision_coefficient_and_profile_checked(self):
        for key in ("revision", "coefficients"):
            t, c = self.matrix_plan()
            c["tree"]["right"]["binding"][key] = "different"
            with self.subTest(key=key):
                self.assert_result("rejected", t, c, "NODE_BINDING")
        t = float_target()
        c = plan(t, t["contract"]["tree"])
        c["tree"]["right"]["binding"]["profile"]["rounding"] = "toward_zero"
        self.assert_result("rejected", t, c, "NODE_BINDING")

    def test_unknown_selected_binding_is_unsupported(self):
        t, c = self.matrix_plan()
        t["binding"]["revision"] = "future-v3"
        c["binding"]["revision"] = "future-v3"
        self.assert_result("unsupported", t, c, "UNSUPPORTED_BINDING")

    def test_exact_rational_scalar_multiplication(self):
        t = scalar_target(MUL, ["2/3", "3/5", "5/7"], permutation=True)
        c = plan(t, node(MUL, leaf("c"), node(MUL, leaf("a"), leaf("b"))), "qq-mul-assoc", "qq-mul-comm")
        self.assertEqual(self.assert_result("accepted", t, c)["audit"]["candidate_value"], "2/7")

    def test_binding_diagnostics_identify_individual_dimensions(self):
        t, c = self.matrix_plan()
        c["binding"]["coefficients"] = "other-coefficients"
        c["binding"]["profile"]["rounding"] = "toward_zero"
        r = self.assert_result("rejected", t, c, "PLAN_BINDING")
        self.assertIn("coefficients", r["message"])
        self.assertIn("profile.rounding", r["message"])

    def test_fixed_tree_float_acceptance_does_not_imply_left_fold_equality(self):
        t = float_target()
        c = plan(t, t["contract"]["tree"])
        r = self.assert_result("accepted", t, c)
        self.assertEqual(r["audit"]["candidate_value"]["bits"], "0000000000000000")
        self.assertEqual(r["audit"]["left_fold_observation"]["value"]["bits"], "3ff0000000000000")
        self.assertFalse(r["audit"]["left_fold_observation"]["equal_for_this_input"])
        self.assertEqual(check(t, c), r)

    def test_float_left_fold_equivalence_rejects_user_counterexample(self):
        t = float_target("left_fold_equivalent")
        tree = node(FLOAT_ADD, leaf("x"), node(FLOAT_ADD, leaf("y"), leaf("z")))
        self.assert_result("rejected", t, plan(t, tree), "VALUE_MISMATCH")

    def test_float_left_fold_equivalence_accepts_only_finite_observation(self):
        t = float_target("left_fold_equivalent")
        for i, value in zip(t["inputs"], [1.0, 2.0, 3.0]):
            i["value"] = f"{float_bits(value):016x}"
        tree = node(FLOAT_ADD, leaf("x"), node(FLOAT_ADD, leaf("y"), leaf("z")))
        r = self.assert_result("accepted", t, plan(t, tree))
        self.assertEqual(r["guarantee"], "bit_or_exact_value_equality_for_these_inputs_only")

    def test_fixed_tree_cannot_be_changed_even_when_results_match(self):
        t = float_target()
        for i in t["inputs"]:
            i["value"] = "0000000000000000"
        c = plan(t, node(FLOAT_ADD, node(FLOAT_ADD, leaf("x"), leaf("y")), leaf("z")))
        self.assert_result("rejected", t, c, "PINNED_TREE")

    def test_float_left_tree_can_be_independently_pinned(self):
        t = float_target()
        t["contract"]["tree"] = node(FLOAT_ADD, node(FLOAT_ADD, leaf("x"), leaf("y")), leaf("z"))
        r = self.assert_result("accepted", t, plan(t, t["contract"]["tree"]))
        self.assertEqual(r["audit"]["candidate_value"]["bits"], "3ff0000000000000")

    def test_float_exact_mode_rejected(self):
        t = float_target()
        tree = deepcopy(t["contract"]["tree"])
        t["contract"] = {"kind": "exact", "allow_permutation": False}
        self.assert_result("rejected", t, plan(t, tree), "EXACT_REPRESENTATION")

    def test_relaxed_errors_never_succeed(self):
        t = float_target("relaxed")
        tree = node(FLOAT_ADD, leaf("x"), node(FLOAT_ADD, leaf("y"), leaf("z")))
        self.assert_result("unsupported", t, plan(t, tree), "RELAXED_UNSUPPORTED")
        # Even a plan whose result equals left-fold cannot turn unsupported into success.
        tree = node(FLOAT_ADD, node(FLOAT_ADD, leaf("x"), leaf("y")), leaf("z"))
        self.assert_result("unsupported", t, plan(t, tree), "RELAXED_UNSUPPORTED")

    def test_relaxed_missing_leaf_is_rejected_before_error_proof(self):
        t = float_target("relaxed")
        self.assert_result("rejected", t, plan(t, node(FLOAT_ADD, leaf("x"), leaf("y"))), "LEAF_MULTIPLICITY")

    def test_forged_relaxed_certificate_not_accepted(self):
        t = float_target("relaxed")
        tree = node(FLOAT_ADD, leaf("x"), node(FLOAT_ADD, leaf("y"), leaf("z")))
        c = plan(t, tree)
        c["evidence"] = [{"certificate": "epsilon-proved", "law": "error-bound", "subject": asdict(FLOAT_ADD)}]
        self.assert_result("rejected", t, c, "UNKNOWN_EVIDENCE")

    def test_invalid_independently_pinned_tree(self):
        t = float_target()
        t["contract"]["tree"]["left"]["leaf"] = "y"
        self.assert_result("rejected", t, plan(t, t["contract"]["tree"]), "TARGET_TREE")

    def test_empty_domain_not_given_implicit_identity(self):
        t, c = self.matrix_plan()
        t["inputs"] = []
        self.assert_result("rejected", t, c, "INPUT_DOMAIN")

    def test_singleton_is_not_given_hidden_operation(self):
        t = target(ADD, ["7/3"], ("only",), {"kind": "exact", "allow_permutation": False})
        r = self.assert_result("accepted", t, plan(t, leaf("only")))
        self.assertEqual(r["audit"]["candidate_value"], "7/3")

    def test_nonfinite_inputs_rejected(self):
        for bits in ("7ff0000000000000", "fff0000000000000", "7ff8000000000001"):
            t = float_target()
            t["inputs"][0]["value"] = bits
            with self.subTest(bits=bits):
                self.assert_result("rejected", t, plan(t, t["contract"]["tree"]), "NONFINITE_INPUT")

    def test_overflow_in_candidate_is_rejected(self):
        t = float_target()
        for i in t["inputs"]:
            i["value"] = "7fefffffffffffff"
        self.assert_result("rejected", t, plan(t, t["contract"]["tree"]), "NONFINITE_RESULT")

    def test_fixed_tree_success_survives_unavailable_left_fold(self):
        t = float_target()
        for i, value in zip(t["inputs"], ["7fefffffffffffff", "7fefffffffffffff", "ffefffffffffffff"]):
            i["value"] = value
        r = self.assert_result("accepted", t, plan(t, t["contract"]["tree"]))
        self.assertEqual(r["audit"]["left_fold_observation"]["status"], "outside_profile")
        self.assertIsNone(r["audit"]["left_fold_observation"]["equal_for_this_input"])

    def test_float_signed_zero_is_preserved_in_result(self):
        t = float_target()
        for i in t["inputs"]:
            i["value"] = "8000000000000000"
        r = self.assert_result("accepted", t, plan(t, t["contract"]["tree"]))
        self.assertEqual(r["audit"]["candidate_value"]["bits"], "8000000000000000")

    def test_input_payload_is_recomputed_and_receipt_changes(self):
        t, c = self.matrix_plan()
        before = self.assert_result("accepted", t, c)
        t["inputs"][0]["value"][0][0] = "9"
        after = self.assert_result("accepted", t, c)
        self.assertNotEqual(before["target_sha256"], after["target_sha256"])
        self.assertNotEqual(before["audit"]["candidate_value"], after["audit"]["candidate_value"])

    def test_rational_input_rejects_float_coercion_and_bool(self):
        for value in (1.0, True, "1/0", "NaN", "1e9", "0.5"):
            t = scalar_target()
            t["inputs"][0]["value"] = value
            with self.subTest(value=value):
                self.assert_result("rejected", t, plan(t, node(ADD, leaf("a"), node(ADD, leaf("b"), leaf("c"))), "qq-add-assoc"), "VALUE")

    def test_tree_schema_limits_and_extra_fields(self):
        t, c = self.matrix_plan()
        for tree in (None, {"leaf": "A"}, {"leaf": "A", "revision": "input-v1", "left": {}},
                     {"binding": asdict(MATMUL), "left": leaf("A"), "right": leaf("B"), "checked": True}):
            c["tree"] = tree
            self.assert_result("rejected", t, c, "SCHEMA")
        tree = leaf("A")
        for _ in range(129):
            tree = node(MATMUL, tree, leaf("A"))
        c["tree"] = tree
        self.assert_result("rejected", t, c, "TREE_LIMIT")

    def test_exact_arithmetic_budget_cannot_crash_or_report_success(self):
        ids = tuple(f"q{i}" for i in range(40))
        t = target(MUL, ["9" * 100] * len(ids), ids,
                   {"kind": "exact", "allow_permutation": False})
        tree = leaf(ids[0])
        for ident in ids[1:]:
            tree = node(MUL, tree, leaf(ident))
        self.assert_result("unsupported", t, plan(t, tree), "ARITHMETIC_LIMIT")

    def test_all_catalan_shapes_and_permutations_for_four_exact_inputs(self):
        # Five shapes times 24 permutations. The ordered matrix model admits only
        # the five order-preserving cases; QQ addition admits all 120 with both laws.
        ids = ("a", "b", "c", "d")
        matrices = [[["1", "1"], ["0", "1"]], [["1", "0"], ["1", "1"]],
                    [["1", "2"], ["0", "1"]], [["2", "0"], ["0", "3"]]]
        mt = target(MATMUL, matrices, ids, {"kind": "exact", "allow_permutation": False})
        qt = target(ADD, ["1/2", "2/3", "3/4", "4/5"], ids, {"kind": "exact", "allow_permutation": True})
        ordered, total = 0, 0
        for perm in itertools.permutations(ids):
            for tree in trees(perm, MATMUL):
                r = check(mt, plan(mt, tree, "matmul-v1-assoc"))
                self.assertEqual(r["status"] == "accepted", perm == ids)
                ordered += r["status"] == "accepted"
            for tree in trees(perm, ADD):
                r = self.assert_result("accepted", qt, plan(qt, tree, "qq-add-assoc", "qq-add-comm"))
                self.assertEqual(r["audit"]["candidate_value"], "163/60")
                total += 1
        self.assertEqual((ordered, total), (5, 120))

    def test_finite_binary_matrix_associativity_samples(self):
        matrices = [((a, b), (c, d)) for a, b, c, d in itertools.product(range(2), repeat=4)]
        for a, b, c in itertools.product(matrices, repeat=3):
            self.assertEqual(matmul(matmul(a, b), c), matmul(a, matmul(b, c)))


class Binary64Tests(unittest.TestCase):
    def test_user_python_float_observation(self):
        x, y, z = float(2**54), -float(2**54), 1.0
        self.assertEqual(((x + y) + z, x + (y + z)), (1.0, 0.0))

    def test_ties_to_even_rounding_both_parities(self):
        one = Bits64(0x3FF0000000000000)
        half_ulp = Bits64(0x3CA0000000000000)
        self.assertEqual(add_binary64(one, half_ulp).bits, one.bits)
        self.assertEqual(add_binary64(Bits64(one.bits + 1), half_ulp).bits, one.bits + 2)

    def test_zero_cancellation_and_subnormal_boundary(self):
        cases = [
            (0x8000000000000000, 0x8000000000000000, 0x8000000000000000),
            (0x8000000000000000, 0, 0),
            (0x3FF0000000000000, 0xBFF0000000000000, 0),
            (1, 1, 2), (0x000FFFFFFFFFFFFF, 1, 0x0010000000000000),
            (0x0010000000000000, 0x8000000000000001, 0x000FFFFFFFFFFFFF),
        ]
        for a, b, expected in cases:
            self.assertEqual(add_binary64(Bits64(a), Bits64(b)).bits, expected)

    def test_rounding_underflow_and_overflow_boundaries(self):
        self.assertEqual(_round_binary64(Fraction(1, 1 << 1075)).bits, 0)
        self.assertEqual(_round_binary64(Fraction(3, 1 << 1075)).bits, 2)
        self.assertEqual(_round_binary64(-Fraction(1, 1 << 1075)).bits, 1 << 63)
        with self.assertRaises(Failure):
            add_binary64(Bits64(0x7FEFFFFFFFFFFFFF), Bits64(0x7FEFFFFFFFFFFFFF))

    def test_software_model_against_5000_host_additions(self):
        # Independent host oracle; seeded finite sample, not portable proof.
        self.assertEqual((sys.float_info.radix, sys.float_info.mant_dig, sys.float_info.rounds), (2, 53, 1))
        rng = random.Random(303)
        for _ in range(5000):
            a = rng.getrandbits(64)
            b = rng.getrandbits(64)
            if (a >> 52) & 0x7FF == 0x7FF:
                a ^= 1 << 52
            if (b >> 52) & 0x7FF == 0x7FF:
                b ^= 1 << 52
            expected = bits_float(a) + bits_float(b)
            if math.isfinite(expected):
                self.assertEqual(add_binary64(Bits64(a), Bits64(b)).bits, float_bits(expected))
            else:
                with self.assertRaises(Failure):
                    add_binary64(Bits64(a), Bits64(b))


class CLITests(unittest.TestCase):
    def test_cli_separate_files_status_and_exit_codes(self):
        script = Path(__file__).with_name("reduction_reference.py")
        with tempfile.TemporaryDirectory() as root:
            tp, cp = Path(root) / "target.json", Path(root) / "candidate.json"
            for kind, status, exitcode in (("fixed_tree", "accepted", 0),
                                           ("left_fold_equivalent", "rejected", 1),
                                           ("relaxed", "unsupported", 2)):
                t = float_target(kind)
                tree = node(FLOAT_ADD, leaf("x"), node(FLOAT_ADD, leaf("y"), leaf("z")))
                tp.write_text(json.dumps(t))
                cp.write_text(json.dumps(plan(t, tree)))
                run = subprocess.run([sys.executable, str(script), str(tp), str(cp)], text=True, capture_output=True)
                self.assertEqual(run.returncode, exitcode, run.stderr)
                self.assertEqual(json.loads(run.stdout)["status"], status)
            cp.write_text('{"schema":1,"schema":2}')
            run = subprocess.run([sys.executable, str(script), str(tp), str(cp)], text=True, capture_output=True)
            self.assertEqual(run.returncode, 3)

    def test_json_duplicate_keys_and_nan_rejected(self):
        with tempfile.TemporaryDirectory() as root:
            p = Path(root) / "bad.json"
            for raw in ('{"binding":{"revision":"v1","revision":"v2"}}', '{"x":NaN}'):
                p.write_text(raw)
                with self.assertRaises(ValueError):
                    load_json(str(p))


if __name__ == "__main__":
    unittest.main()
