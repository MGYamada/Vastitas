"""Behavioral, exhaustive finite, and mutation regressions; no third-party deps."""

import itertools
import unittest
from dataclasses import fields, replace
from fractions import Fraction
from unittest.mock import patch

import graph_reference as br

P = br.Direction.POSITIVE
N = br.Direction.NEGATIVE
DEGREES = range(-2, 3)


def boundary(degrees, *, brand="presentation:A", shape=None, same_object=False):
    strands = tuple(
        br.Strand(f"occurrence:{i}", "object:shared" if same_object else f"object:{i}", a)
        for i, a in enumerate(degrees)
    )
    return br.Boundary(
        brand, br.right_bracketing(len(strands)) if shape is None else shape, strands
    )


def word(degrees, ops, profile="braided_two", **kwargs):
    return br.make_word(br.FIXTURES[profile].key, boundary(degrees, **kwargs), tuple(ops))


def rewrite(before, rule, offset=0):
    evidence = br.evidence_for(before.profile, rule)
    claim = br.propose_rewrite(before, offset, rule, evidence)
    return br.check_rewrite(before, claim)


def observation_signature(w):
    """Test observation only; not used by rewrite acceptance."""
    o = br.evaluate(w)
    return o.profile, o.source, o.target, o.scalar


class CrossingSemanticsTests(unittest.TestCase):
    def test_empty_words_all_capabilities_and_small_arities(self):
        for name in br.FIXTURES:
            for arity in range(4):
                with self.subTest(profile=name, arity=arity):
                    w = word((1,) * arity, (), name)
                    o = br.evaluate(w)
                    self.assertEqual(o.source, o.target)
                    self.assertEqual(o.scalar, Fraction(1))
                    self.assertEqual(o.crossing_factors, ())

    def test_monoidal_rejects_both_crossing_directions(self):
        for d in (P, N):
            with self.subTest(direction=d), self.assertRaises(br.Rejected):
                word((1, 1), ((0, d),), "monoidal")

    def test_monoidal_rejects_forged_crossing_word(self):
        braided = word((1, 1), ((0, P),))
        key = br.FIXTURES["monoidal"].key
        forged = replace(braided, profile=key,
                         crossings=tuple(replace(c, profile=key) for c in braided.crossings))
        with self.assertRaises(br.Rejected):
            br.audit_word(forged)

    def test_non_symmetric_double_braiding_is_retained(self):
        for d, scalar in ((P, Fraction(4)), (N, Fraction(1, 4))):
            with self.subTest(direction=d):
                w = word((1, 1), ((0, d), (0, d)), same_object=True)
                self.assertEqual(w.source, w.target)
                self.assertEqual(br.evaluate(w).scalar, scalar)
                self.assertEqual(len(w.crossings), 2)
                self.assertNotEqual(w, word((1, 1), (), same_object=True))
                with self.assertRaises(br.Rejected):
                    rewrite(w, br.Rule.INVERSE)
                with self.assertRaises(br.Rejected):
                    rewrite(w, br.Rule.SYMMETRIC)

    def test_inverse_cancellation_both_orders_all_25_degree_pairs(self):
        for a, b in itertools.product(DEGREES, repeat=2):
            for d, inverse in ((P, N), (N, P)):
                with self.subTest(a=a, b=b, direction=d):
                    w = word((a, b), ((0, d), (0, inverse)))
                    result = rewrite(w, br.Rule.INVERSE)
                    self.assertEqual(result, word((a, b), ()))
                    self.assertEqual(br.evaluate(w).scalar, Fraction(1))

    def test_positive_and_negative_have_distinct_coefficients_and_same_ports(self):
        plus = word((1, 1), ((0, P),))
        minus = word((1, 1), ((0, N),))
        self.assertEqual(plus.target, minus.target)
        self.assertNotEqual(plus, minus)
        self.assertEqual(br.evaluate(plus).scalar, Fraction(2))
        self.assertEqual(br.evaluate(minus).scalar, Fraction(1, 2))

    def test_negative_degrees_stay_exact_fractions(self):
        w = word((-2, 3), ((0, P),))
        self.assertEqual(br.evaluate(w).scalar, Fraction(1, 64))
        self.assertEqual(br.evaluate(word((-2, 3), ((0, N),))).scalar, Fraction(64))
        self.assertIs(type(br.evaluate(w).scalar), Fraction)

    def test_braid_relation_both_signs_all_125_degree_triples(self):
        for a, b, c in itertools.product(DEGREES, repeat=3):
            for sign in (P, N):
                with self.subTest(degrees=(a, b, c), direction=sign):
                    lhs = word((a, b, c), ((0, sign), (1, sign), (0, sign)))
                    rhs = word((a, b, c), ((1, sign), (0, sign), (1, sign)))
                    self.assertEqual(rewrite(lhs, br.Rule.BRAID), rhs)
                    self.assertEqual(rewrite(rhs, br.Rule.BRAID), lhs)
                    self.assertEqual(observation_signature(lhs), observation_signature(rhs))
                    expected = Fraction(2) ** (sign.value * (a*b + a*c + b*c))
                    self.assertEqual(br.evaluate(lhs).scalar, expected)
                    self.assertEqual(lhs.target.strands, tuple(reversed(lhs.source.strands)))

    def test_degree_123_braid_witness_is_2048(self):
        lhs = word((1, 2, 3), ((0, P), (1, P), (0, P)))
        rhs = rewrite(lhs, br.Rule.BRAID)
        self.assertEqual(br.evaluate(lhs).scalar, Fraction(2048))
        self.assertEqual(br.evaluate(rhs).scalar, Fraction(2048))
        self.assertEqual(br.evaluate(lhs).crossing_factors, (Fraction(4), Fraction(8), Fraction(64)))
        self.assertEqual(br.evaluate(rhs).crossing_factors, (Fraction(64), Fraction(8), Fraction(4)))

    def test_two_bicharacter_multiplicativities_all_125_triples(self):
        for q in (Fraction(2), Fraction(-1), Fraction(1)):
            for a, b, c in itertools.product(DEGREES, repeat=3):
                with self.subTest(q=q, degrees=(a, b, c)):
                    chi = lambda x, y: br.bicharacter(q, x, y)
                    self.assertEqual(chi(a, b+c), chi(a, b) * chi(a, c))
                    self.assertEqual(chi(a+b, c), chi(a, c) * chi(b, c))
                    self.assertEqual(chi(0, a), Fraction(1))
                    self.assertEqual(chi(a, 0), Fraction(1))

    def test_far_commutation_all_625_degree_quadruples_and_four_sign_pairs(self):
        for degrees in itertools.product(DEGREES, repeat=4):
            for a, b in itertools.product((P, N), repeat=2):
                with self.subTest(degrees=degrees, directions=(a, b)):
                    lhs = word(degrees, ((0, a), (2, b)))
                    rhs = word(degrees, ((2, b), (0, a)))
                    self.assertEqual(rewrite(lhs, br.Rule.FAR), rhs)
                    self.assertEqual(rewrite(rhs, br.Rule.FAR), lhs)
                    self.assertEqual(observation_signature(lhs), observation_signature(rhs))

    def test_symmetric_double_cancellation_both_signs_all_25_pairs(self):
        for name in ("symmetric_sign", "symmetric_one"):
            for a, b in itertools.product(DEGREES, repeat=2):
                for d in (P, N):
                    with self.subTest(profile=name, degrees=(a, b), direction=d):
                        w = word((a, b), ((0, d), (0, d)), name)
                        self.assertEqual(br.evaluate(w).scalar, Fraction(1))
                        self.assertEqual(rewrite(w, br.Rule.SYMMETRIC), word((a, b), (), name))

    def test_symmetric_sign_single_crossing_is_minus_one(self):
        self.assertEqual(br.evaluate(word((1, 1), ((0, P),), "symmetric_sign")).scalar,
                         Fraction(-1))

    def test_capability_hierarchy_reuses_braided_rules(self):
        for name in ("braided_two", "symmetric_sign", "symmetric_one"):
            for rule, ops in (
                (br.Rule.INVERSE, ((0, P), (0, N))),
                (br.Rule.BRAID, ((0, P), (1, P), (0, P))),
                (br.Rule.FAR, ((0, P), (2, N))),
            ):
                with self.subTest(profile=name, rule=rule):
                    before = word((1, 2, 3, 4), ops, name)
                    self.assertEqual(observation_signature(before),
                                     observation_signature(rewrite(before, rule)))


class IdentityAndEvidenceTests(unittest.TestCase):
    def test_occurrence_ids_are_distinct_from_degrees_and_object_ids(self):
        w = word((1, 1), ((0, P), (0, N)), same_object=True)
        first, second = w.crossings
        self.assertEqual(first.left.degree, first.right.degree)
        self.assertEqual(first.left.object_id, first.right.object_id)
        self.assertNotEqual(first.left.occurrence_id, first.right.occurrence_id)
        self.assertEqual((second.left, second.right), (first.right, first.left))
        self.assertEqual(rewrite(w, br.Rule.INVERSE).source, w.source)

    def test_duplicate_occurrence_rejected_even_with_different_degree(self):
        b = boundary((1, 2))
        b = replace(b, strands=(b.strands[0], replace(b.strands[1], occurrence_id="occurrence:0")))
        with self.assertRaises(br.Rejected):
            br.make_word(br.FIXTURES["braided_two"].key, b, ())

    def test_crossing_port_mutations_rejected(self):
        w = word((1, 1), ((0, P),))
        for field, value in (("occurrence_id", "fake"), ("object_id", "other"),
                             ("degree", 2), ("degree", True), ("degree", 1.0)):
            with self.subTest(field=field, value=value):
                c = replace(w.crossings[0], left=replace(w.crossings[0].left, **{field: value}))
                with self.assertRaises(br.Rejected):
                    br.audit_word(replace(w, crossings=(c,)))

    def test_stale_same_degree_port_order_rejected(self):
        w = word((1, 1), ((0, P), (0, P)), same_object=True)
        with self.assertRaises(br.Rejected):
            br.audit_word(replace(w, crossings=(w.crossings[0], w.crossings[0])))

    def test_crossing_from_another_profile_rejected(self):
        w = word((1, 1), ((0, P),))
        c = replace(w.crossings[0], profile=br.FIXTURES["braided_two_other"].key)
        with self.assertRaises(br.Rejected):
            br.audit_word(replace(w, crossings=(c,)))

    def test_same_q_other_profile_evidence_is_not_reusable(self):
        w = word((1, 2), ((0, P), (0, N)))
        other = br.FIXTURES["braided_two_other"]
        self.assertEqual(other.q, br.FIXTURES["braided_two"].q)
        e = br.evidence_for(other.key, br.Rule.INVERSE)
        with self.assertRaises(br.Rejected):
            br.propose_rewrite(w, 0, br.Rule.INVERSE, e)

    def test_symmetry_evidence_cannot_be_borrowed_even_for_same_q(self):
        for profile in ("braided_two", "braided_sign"):
            w = word((1, 1), ((0, P), (0, P)), profile)
            e = br.evidence_for(br.FIXTURES["symmetric_sign"].key, br.Rule.SYMMETRIC)
            with self.subTest(profile=profile), self.assertRaises(br.Rejected):
                br.propose_rewrite(w, 0, br.Rule.SYMMETRIC, e)

    def test_each_profile_identity_component_is_bound(self):
        w = word((1, 2), ((0, P), (0, N)))
        e = br.evidence_for(w.profile, br.Rule.INVERSE)
        for field in fields(br.ProfileKey):
            with self.subTest(component=field.name):
                changed_key = replace(w.profile, **{field.name: "unrelated-or-stale"})
                changed_evidence = replace(e, profile=replace(e.profile, key=changed_key))
                with self.assertRaises(br.Rejected):
                    br.propose_rewrite(w, 0, br.Rule.INVERSE, changed_evidence)
                with self.assertRaises(br.Rejected):
                    br.audit_word(replace(w, profile=changed_key))

    def test_forged_capability_q_token_and_rule_rejected(self):
        w = word((1, 2), ((0, P), (0, N)))
        e = br.evidence_for(w.profile, br.Rule.INVERSE)
        for bad in (
            replace(e, token="frontend-assertion"),
            replace(e, rule=br.Rule.BRAID),
            replace(e, profile=replace(e.profile, capability=br.Capability.SYMMETRIC)),
            replace(e, profile=replace(e.profile, capability=2)),
            replace(e, profile=replace(e.profile, q=Fraction(3))),
            replace(e, profile=replace(e.profile, q=2.0)),
        ):
            with self.subTest(evidence=bad), self.assertRaises(br.Rejected):
                br.propose_rewrite(w, 0, br.Rule.INVERSE, bad)

    def test_spelling_is_not_canonical_tensor_identity(self):
        key = replace(br.FIXTURES["braided_two"].key, canonical_tensor_id="user::⊗")
        with self.assertRaises(br.Rejected):
            br.make_word(key, boundary((1, 1)), ())

    def test_orientation_must_be_explicit(self):
        w = word((1, 1), ((0, P),))
        for erased in (None, 1, -1, True, "+", "-"):
            with self.subTest(direction=erased):
                with self.assertRaises(br.Rejected):
                    word((1, 1), ((0, erased),))
                c = replace(w.crossings[0], direction=erased)
                with self.assertRaises(br.Rejected):
                    br.audit_word(replace(w, crossings=(c,)))

    def test_invalid_positions_and_nonintegral_degrees_rejected(self):
        for position in (-1, 1, 5, True, 0.0):
            with self.subTest(position=position), self.assertRaises(br.Rejected):
                word((1, 1), ((position, P),))
        for degree in (True, 1.0, Fraction(1), "1"):
            with self.subTest(degree=degree), self.assertRaises(br.Rejected):
                word((degree, 1), ())

    def test_invalid_q_and_degree_cannot_enter_exact_arithmetic(self):
        for q in (2, 2.0, Fraction(0), True):
            with self.subTest(q=q), self.assertRaises(br.Rejected):
                br.bicharacter(q, 1, 1)
        with self.assertRaises(br.Rejected):
            br.bicharacter(Fraction(2), True, 1)

    def test_bad_bracket_syntax_and_empty_factors_rejected(self):
        for shape in ((1, 0), (0, 0), (0, (None, 1)), (False, 1), [0, 1]):
            with self.subTest(shape=shape), self.assertRaises(br.Rejected):
                word((1, 1), (), shape=shape)


class RewriteBoundaryTests(unittest.TestCase):
    def test_inverse_rule_preserves_prefix_and_suffix(self):
        w = word((1, -2, 3), ((1, N), (0, P), (0, N), (1, P)))
        after = rewrite(w, br.Rule.INVERSE, 1)
        expected = word((1, -2, 3), ((1, N), (1, P)))
        self.assertEqual(after, expected)
        self.assertEqual(observation_signature(w), observation_signature(after))

    def test_braid_rule_preserves_context_and_rebinds_occurrences(self):
        ops = ((2, N), (0, P), (1, P), (0, P), (2, P))
        w = word((1, 2, -1, -2), ops)
        after = rewrite(w, br.Rule.BRAID, 1)
        expected = word((1, 2, -1, -2), ((2, N), (1, P), (0, P), (1, P), (2, P)))
        self.assertEqual(after, expected)
        self.assertEqual(after.target, w.target)
        self.assertEqual(observation_signature(after), observation_signature(w))

    def test_far_rule_rejects_adjacent_positions_even_with_zero_degrees(self):
        with self.assertRaises(br.Rejected):
            rewrite(word((0, 0, 0), ((0, P), (1, P))), br.Rule.FAR)

    def test_braid_rule_rejects_unsupported_mixed_sign_pattern(self):
        with self.assertRaises(br.Rejected):
            rewrite(word((1, 2, 3), ((0, P), (1, N), (0, P))), br.Rule.BRAID)

    def test_cancellation_rejects_different_positions(self):
        with self.assertRaises(br.Rejected):
            rewrite(word((0, 0, 0), ((0, P), (1, N))), br.Rule.INVERSE)

    def test_invalid_offsets_are_rejected(self):
        w = word((1, 1), ((0, P), (0, N)))
        for offset in (-1, 1, 100, True, 0.0):
            with self.subTest(offset=offset), self.assertRaises(br.Rejected):
                rewrite(w, br.Rule.INVERSE, offset)

    def test_no_rewrite_rule_for_permutation_scalar_or_reassociation(self):
        w = word((0, 0), ((0, P), (0, P)))
        evidence = br.evidence_for(w.profile, br.Rule.INVERSE)
        for rule in ("same final permutation", "same evaluated scalar", "reassociate"):
            claim = br.RewriteClaim(0, rule, evidence, word((0, 0), ()))
            with self.subTest(rule=rule), self.assertRaises(br.Rejected):
                br.check_rewrite(w, claim)

    def test_equal_observation_does_not_supply_symmetry(self):
        for profile, degrees in (("braided_two", (0, 1)), ("braided_sign", (1, 1))):
            w = word(degrees, ((0, P), (0, P)), profile)
            empty = word(degrees, (), profile)
            self.assertEqual(observation_signature(w), observation_signature(empty))
            for rule in (br.Rule.INVERSE, br.Rule.SYMMETRIC):
                with self.subTest(profile=profile, rule=rule), self.assertRaises(br.Rejected):
                    rewrite(w, rule)

    def test_direction_erasure_in_returned_context_is_rejected(self):
        w = word((1, 1, 1), ((0, P), (1, P), (0, P), (1, P)))
        claim = br.propose_rewrite(w, 0, br.Rule.BRAID, br.evidence_for(w.profile, br.Rule.BRAID))
        changed = word((1, 1, 1), ((1, P), (0, P), (1, P), (1, N)))
        self.assertEqual(changed.target, claim.after.target)
        self.assertNotEqual(br.evaluate(changed).scalar, br.evaluate(claim.after).scalar)
        with self.assertRaises(br.Rejected):
            br.check_rewrite(w, replace(claim, after=changed))

    def test_same_permutation_returned_word_is_not_enough(self):
        w = word((1, 1), ((0, P), (0, N)))
        claim = br.propose_rewrite(w, 0, br.Rule.INVERSE, br.evidence_for(w.profile, br.Rule.INVERSE))
        same_permutation = word((1, 1), ((0, P), (0, P)))
        self.assertEqual(same_permutation.target, claim.after.target)
        with self.assertRaises(br.Rejected):
            br.check_rewrite(w, replace(claim, after=same_permutation))

    def test_even_equal_scalar_returned_word_is_not_enough(self):
        w = word((0, 1), ((0, P), (0, N)))
        claim = br.propose_rewrite(w, 0, br.Rule.INVERSE, br.evidence_for(w.profile, br.Rule.INVERSE))
        same_observation = word((0, 1), ((0, P), (0, P)))
        self.assertEqual(observation_signature(same_observation), observation_signature(claim.after))
        with self.assertRaises(br.Rejected):
            br.check_rewrite(w, replace(claim, after=same_observation))

    def test_nominal_brand_cannot_be_changed_by_coordinate_agreement(self):
        w = word((1, 1), ((0, P), (0, N)))
        claim = br.propose_rewrite(w, 0, br.Rule.INVERSE, br.evidence_for(w.profile, br.Rule.INVERSE))
        other = word((1, 1), (), brand="different-nominal-presentation")
        self.assertEqual(br.evaluate(other).scalar, br.evaluate(claim.after).scalar)
        with self.assertRaises(br.Rejected):
            br.check_rewrite(w, replace(claim, after=other))

    def test_bracketed_endpoints_cannot_be_silently_identified(self):
        w = word((1, 2, 3), ((0, P), (0, N)), shape=((0, 1), 2))
        claim = br.propose_rewrite(w, 0, br.Rule.INVERSE, br.evidence_for(w.profile, br.Rule.INVERSE))
        other = word((1, 2, 3), (), shape=(0, (1, 2)))
        self.assertEqual(other.source.strands, w.source.strands)
        self.assertEqual(br.evaluate(other).scalar, br.evaluate(claim.after).scalar)
        with self.assertRaises(br.Rejected):
            br.check_rewrite(w, replace(claim, after=other))
        with self.assertRaises(br.Rejected):
            br.audit_word(replace(w, target=replace(w.target, bracketing=(0, (1, 2)))))

    def test_evaluator_is_not_called_by_rewrite_acceptance(self):
        w = word((1, 2, 3), ((0, P), (1, P), (0, P)))
        with patch.object(br, "evaluate", side_effect=AssertionError("unsafe oracle call")), \
             patch.object(br, "bicharacter", side_effect=AssertionError("unsafe scalar comparison")):
            after = rewrite(w, br.Rule.BRAID)
        self.assertEqual(after, word((1, 2, 3), ((1, P), (0, P), (1, P))))

    def test_trace_binds_actual_returned_word_and_replays_claims(self):
        initial = word((1, 2), ((0, P), (0, N), (0, N), (0, P)))
        e = br.evidence_for(initial.profile, br.Rule.INVERSE)
        first = br.propose_rewrite(initial, 0, br.Rule.INVERSE, e)
        second = br.propose_rewrite(first.after, 0, br.Rule.INVERSE, e)
        record = br.check_trace(initial, (first, second), second.after)
        self.assertEqual(record.returned, word((1, 2), ()))
        with self.assertRaises(br.Rejected):
            br.check_trace(initial, (first, second), first.after)
        with self.assertRaises(br.Rejected):
            br.check_trace(initial, (second, first), second.after)
        with self.assertRaises(br.Rejected):
            br.check_trace(initial, (), second.after)

    def test_arbitrary_user_morphism_node_is_not_accepted(self):
        w = word((1, 1), ())
        with self.assertRaises(br.Rejected):
            br.audit_word(replace(w, crossings=("user::f",)))

    def test_representation_is_nonfaithful_on_a_nontrivial_pure_braid(self):
        # [sigma_1^2, sigma_2^2]. Each pure block returns the same strand order,
        # and its scalar cancels with the inverse block for EVERY degree triple.
        ops = ((0, P), (0, P), (1, P), (1, P), (0, N), (0, N), (1, N), (1, N))
        for degrees in itertools.product(DEGREES, repeat=3):
            with self.subTest(degrees=degrees):
                w = word(degrees, ops)
                self.assertEqual(observation_signature(w), observation_signature(word(degrees, ())))
                with self.assertRaises(br.Rejected):
                    br.check_trace(w, (), word(degrees, ()))

        # Independent B3 -> SL(2,Z) witness that this word is not the identity.
        # These matrices satisfy A*B*A = B*A*B. This is NOT a general solver.
        def multiply(a, b):
            return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2))
                               for j in range(2)) for i in range(2))

        identity = ((1, 0), (0, 1))
        A, B = ((1, 1), (0, 1)), ((1, 0), (-1, 1))
        invA, invB = ((1, -1), (0, 1)), ((1, 0), (1, 1))
        self.assertEqual(multiply(multiply(A, B), A), multiply(multiply(B, A), B))
        self.assertEqual(multiply(A, invA), identity)
        self.assertEqual(multiply(B, invB), identity)
        image = identity
        for position, sign in ops:
            generator = (A, B)[position] if sign is P else (invA, invB)[position]
            image = multiply(image, generator)
        self.assertEqual(image, ((13, 8), (8, 5)))
        self.assertNotEqual(image, identity)


if __name__ == "__main__":
    unittest.main(verbosity=2)
