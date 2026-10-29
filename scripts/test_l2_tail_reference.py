"""Rule, provenance, and finite-observation regressions; no infinite proof claims."""

import unittest
from dataclasses import replace
from fractions import Fraction as Q
from unittest.mock import patch

import l2_tail_reference as ref


ENV = ref.Environment(dependencies=(("fixture:analysis", "revision:1"),))
X = ref.ReferenceCore("fixture:x", "1", ref.Geometric(Q(1), Q(1, 2)))
R = ref.ReferenceCore("fixture:reciprocal", "1", ref.Reciprocal(Q(1)))
INTERVALS = tuple((n, m) for n in range(33) for m in range(n, 65))


def certificate(core=X, env=ENV):
    return ref.propose_certificate(core, env)


class TailRuleTests(unittest.TestCase):
    def assert_outcome(self, expected, cert, core=X, env=ENV):
        result = ref.check_certificate(core, env, cert)
        self.assertEqual(result.outcome, expected, result.reason)
        if expected is ref.Outcome.ACCEPTED_REFERENCE:
            self.assertIs(result.accepted.binding.core, core)
            self.assertIs(result.accepted.binding.environment, env)
            self.assertEqual(ref.audit_acceptance(core, env, result.accepted), result)
        else:
            self.assertIsNone(result.accepted)
        return result

    def test_geometric_signed_rational_parameters_and_zero(self):
        for a in (Q(-3, 2), Q(0), Q(1), Q(5, 7)):
            for r in (Q(-999, 1000), Q(-1, 2), Q(0), Q(1, 2), Q(999, 1000)):
                core = replace(X, body=ref.Geometric(a, r))
                with self.subTest(a=a, r=r):
                    self.assert_outcome(ref.Outcome.ACCEPTED_REFERENCE, certificate(core), core)

    def test_scaled_reciprocals(self):
        for a in (Q(-7, 3), Q(0), Q(1), Q(5, 7)):
            core = replace(R, body=ref.Reciprocal(a))
            self.assert_outcome(ref.Outcome.ACCEPTED_REFERENCE, certificate(core), core)

    def test_loose_bounds_are_accepted_not_only_canonical_coefficients(self):
        for core in (X, R):
            cert = certificate(core)
            loose = replace(cert, bound=replace(cert.bound, coefficient=Q(3)))
            self.assert_outcome(ref.Outcome.ACCEPTED_REFERENCE, loose, core)
            for n, m in INTERVALS:
                self.assertLessEqual(ref.finite_tail_square_sum(core, n, m),
                                     ref.tail_value(loose.bound, n) - ref.tail_value(loose.bound, m))

    def test_missing_geometric_factor_rejected(self):
        bad = replace(certificate(), bound=ref.GeometricBound(Q(1), Q(1, 4)))
        self.assert_outcome(ref.Outcome.INVALID_BOUND, bad)
        self.assertEqual(ref.finite_tail_square_sum(X, 0, 2), Q(5, 4))
        self.assertGreater(ref.finite_tail_square_sum(X, 0, 2), ref.tail_value(bad.bound, 0))

    def test_subtly_small_bound_passes_all_sampled_intervals_but_is_rejected(self):
        bad = replace(certificate(), bound=ref.GeometricBound(Q(4, 3) - Q(1, 10**100), Q(1, 4)))
        for n, m in INTERVALS:
            self.assertLessEqual(ref.finite_tail_square_sum(X, n, m), ref.tail_value(bad.bound, n))
        self.assert_outcome(ref.Outcome.INVALID_BOUND, bad)

    def test_reciprocal_small_bound_rejected_with_finite_counterexample(self):
        bad = replace(certificate(R), bound=ref.ReciprocalBound(Q(1, 2)))
        self.assert_outcome(ref.Outcome.INVALID_BOUND, bad, R)
        self.assertGreater(ref.finite_tail_square_sum(R, 0, 2), ref.tail_value(bad.bound, 0))

    def test_negative_and_zero_bounds_do_not_certify_nonzero_sequences(self):
        for core in (X, R):
            for c in (Q(-1), Q(0)):
                cert = certificate(core)
                self.assert_outcome(ref.Outcome.INVALID_BOUND,
                                    replace(cert, bound=replace(cert.bound, coefficient=c)), core)

    def test_no_observation_or_candidate_producer_is_used_for_acceptance(self):
        certs = ((X, certificate()), (R, certificate(R)))
        with patch.object(ref, "term", side_effect=AssertionError("sampled")), \
             patch.object(ref, "finite_tail_square_sum", side_effect=AssertionError("sampled")), \
             patch.object(ref, "tail_value", side_effect=AssertionError("sampled")), \
             patch.object(ref, "propose_certificate", side_effect=AssertionError("trusted producer")):
            for core, cert in certs:
                self.assert_outcome(ref.Outcome.ACCEPTED_REFERENCE, cert, core)
            bad = replace(certs[0][1], bound=ref.GeometricBound(Q(1), Q(1, 4)))
            self.assert_outcome(ref.Outcome.INVALID_BOUND, bad)

    def test_missing_evidence_does_not_even_certify_a_supported_generator(self):
        self.assert_outcome(ref.Outcome.UNSUPPORTED, None)

    def test_opaque_sequences_with_no_proof_remain_unresolved(self):
        for description in ("arbitrary generator", "1/sqrt(n+1)", "1/(n+1)^2"):
            core = replace(X, body=ref.Opaque(description))
            self.assertIsNone(certificate(core))
            self.assert_outcome(ref.Outcome.UNSUPPORTED, None, core)

    def test_unknown_rule_is_unsupported(self):
        self.assert_outcome(ref.Outcome.UNSUPPORTED,
                            replace(certificate(), rule="finite-samples-look-good"))

    def test_no_decay_rule_outside_open_unit_interval(self):
        # Includes zero sequences: outside this rule is not a nonmembership verdict.
        for a in (Q(0), Q(1)):
            for r in (Q(-2), Q(-1), Q(1), Q(2)):
                core = replace(X, body=ref.Geometric(a, r))
                cert = ref.Certificate(ref.Binding(core, ENV), ref.GEOMETRIC_RULE,
                                       ref.GeometricBound(Q(2), r*r))
                self.assert_outcome(ref.Outcome.UNSUPPORTED, cert, core)
                self.assertIsNone(certificate(core))

    def test_equal_prefix_is_not_generator_identity(self):
        y = replace(X, body=ref.PrefixThenConstant(tuple(ref.term(X, n) for n in range(8)), Q(1)))
        self.assertEqual([ref.term(X, n) for n in range(8)], [ref.term(y, n) for n in range(8)])
        self.assertEqual(ref.finite_tail_square_sum(y, 0, 8), Q(21845, 16384))
        self.assertEqual(ref.finite_tail_square_sum(X, 0, 8), Q(21845, 16384))
        self.assertEqual(ref.tail_value(certificate().bound, 8), Q(1, 49152))
        self.assertGreater(ref.finite_tail_square_sum(y, 8, 9), ref.tail_value(certificate().bound, 8))
        self.assert_outcome(ref.Outcome.EVIDENCE_MISMATCH, certificate(), y)
        self.assert_outcome(ref.Outcome.UNSUPPORTED, None, y)
        # Rewriting the certificate's binding does not make its rule fit y.
        rebound = replace(certificate(), binding=ref.Binding(y, ENV))
        self.assert_outcome(ref.Outcome.EVIDENCE_MISMATCH, rebound, y)

    def test_definition_identity_revision_and_parameters_are_bound(self):
        mutations = (replace(X, definition_id="fixture:other"),
                     replace(X, definition_revision="2"),
                     replace(X, body=ref.Geometric(Q(2), Q(1, 2))),
                     replace(X, body=ref.Geometric(Q(1), Q(-1, 2))))
        for core in mutations:
            self.assert_outcome(ref.Outcome.EVIDENCE_MISMATCH, certificate(), core)

    def test_rebound_changed_amplitude_is_rechecked(self):
        core = replace(X, body=ref.Geometric(Q(2), Q(1, 2)))
        rebound = replace(certificate(), binding=ref.Binding(core, ENV))
        self.assert_outcome(ref.Outcome.INVALID_BOUND, rebound, core)

    def test_tail_ratio_and_generator_ratio_must_match(self):
        for q in (Q(1, 16), Q(1, 2), Q(-1, 4)):
            bad = replace(certificate(), bound=ref.GeometricBound(Q(2), q))
            self.assert_outcome(ref.Outcome.EVIDENCE_MISMATCH, bad)

    def test_wrong_known_rule_or_tail_template_rejected(self):
        self.assert_outcome(ref.Outcome.EVIDENCE_MISMATCH,
                            replace(certificate(), rule=ref.RECIPROCAL_RULE))
        self.assert_outcome(ref.Outcome.EVIDENCE_MISMATCH,
                            replace(certificate(), bound=ref.ReciprocalBound(Q(2))))
        self.assert_outcome(ref.Outcome.EVIDENCE_MISMATCH,
                            replace(certificate(R), bound=certificate().bound), R)

    def test_environment_and_ruleset_changes_invalidate_evidence(self):
        for env in (ref.Environment(),
                    ref.Environment(dependencies=(("fixture:analysis", "revision:2"),)),
                    ref.Environment(dependencies=ENV.dependencies + (("fixture:extra", "1"),))):
            self.assert_outcome(ref.Outcome.EVIDENCE_MISMATCH, certificate(), env=env)
        stale = replace(certificate(), binding=replace(certificate().binding, ruleset="old-rules"))
        self.assert_outcome(ref.Outcome.EVIDENCE_MISMATCH, stale)

    def test_approximate_profile_cannot_acquire_exact_authority(self):
        env = ref.Environment("float64")
        self.assert_outcome(ref.Outcome.UNSUPPORTED, certificate(X, env), env=env)

    def test_changed_returned_core_or_environment_fails_consumer_audit(self):
        accepted = ref.check_certificate(X, ENV, certificate()).accepted
        other = replace(X, definition_id="fixture:other")
        for core, env in ((other, ENV), (X, ref.Environment())):
            self.assertEqual(ref.audit_acceptance(core, env, accepted).outcome,
                             ref.Outcome.EVIDENCE_MISMATCH)
        forged = replace(accepted, binding=ref.Binding(other, ENV))
        self.assertEqual(ref.audit_acceptance(X, ENV, forged).outcome, ref.Outcome.EVIDENCE_MISMATCH)

    def test_forged_acceptance_dataclass_is_not_proof_authority(self):
        bad = replace(certificate(), bound=ref.GeometricBound(Q(1), Q(1, 4)))
        forged = ref.ReferenceAcceptance(ref.Binding(X, ENV), bad)
        self.assertEqual(ref.audit_acceptance(X, ENV, forged).outcome, ref.Outcome.INVALID_BOUND)
        self.assertEqual(ref.audit_acceptance(X, ENV, True).outcome, ref.Outcome.MALFORMED)

    def test_non_fraction_values_are_malformed_even_if_numerically_equal(self):
        for value in (1, True, 1.0, "1", None):
            core = replace(X, body=ref.Geometric(value, Q(1, 2)))
            self.assert_outcome(ref.Outcome.MALFORMED, None, core)
            bad = replace(certificate(), bound=ref.GeometricBound(value, Q(1, 4)))
            self.assert_outcome(ref.Outcome.MALFORMED, bad)

    def test_malformed_and_mutable_records_rejected(self):
        self.assert_outcome(ref.Outcome.MALFORMED, {"accepted": True})
        self.assert_outcome(ref.Outcome.MALFORMED, replace(certificate(), binding=True))
        self.assert_outcome(ref.Outcome.MALFORMED, None, replace(X, body=object()))
        for env in (ref.Environment(dependencies=list(ENV.dependencies)),
                    ref.Environment(dependencies=ENV.dependencies * 2)):
            self.assert_outcome(ref.Outcome.MALFORMED, None, env=env)


class FiniteObservationTests(unittest.TestCase):
    def test_1617_geometric_interval_identities(self):
        self.assertEqual(len(INTERVALS), 1617)
        bound = certificate().bound
        for n, m in INTERVALS:
            self.assertEqual(ref.finite_tail_square_sum(X, n, m),
                             ref.tail_value(bound, n) - ref.tail_value(bound, m))

    def test_1617_reciprocal_interval_inequalities(self):
        bound = certificate(R).bound
        self.assertEqual(ref.tail_value(bound, 0), Q(2))
        for n, m in INTERVALS:
            self.assertLessEqual(ref.finite_tail_square_sum(R, n, m),
                                 ref.tail_value(bound, n) - ref.tail_value(bound, m))

    def test_reciprocal_comparison_identity_and_zero_index_separately(self):
        bound = certificate(R).bound
        self.assertEqual(ref.term(R, 0)**2, ref.tail_value(bound, 0) - ref.tail_value(bound, 1))
        for n in range(1, 65):
            self.assertEqual(Q(1, n) - Q(1, n+1) - Q(1, (n+1)**2),
                             Q(1, n*(n+1)**2))

    def test_zero_ratio_keeps_the_nonzero_initial_term(self):
        core = replace(X, body=ref.Geometric(Q(3, 2), Q(0)))
        bound = certificate(core).bound
        self.assertEqual(ref.term(core, 0), Q(3, 2))
        self.assertEqual(ref.tail_value(bound, 0), Q(9, 4))
        self.assertEqual(ref.tail_value(bound, 1), Q(0))
        self.assertEqual(ref.finite_tail_square_sum(core, 0, 64), Q(9, 4))

    def test_invalid_indices_do_not_get_saturating_or_float_semantics(self):
        for n in (-1, 1.0, True):
            with self.assertRaises(ValueError):
                ref.term(X, n)
            with self.assertRaises(ValueError):
                ref.tail_value(certificate().bound, n)
        with self.assertRaises(ValueError):
            ref.finite_tail_square_sum(X, 3, 2)


if __name__ == "__main__":
    unittest.main()
