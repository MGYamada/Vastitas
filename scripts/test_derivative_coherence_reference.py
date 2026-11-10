"""Run: python3 -m unittest discover -s scripts -p 'test_derivative_coherence_reference.py' -v"""
import unittest
from dataclasses import replace
from fractions import Fraction as Q
from itertools import permutations

from derivative_coherence_reference import (
    Context, Domain, Map, Piece, Reject, Rule, admit, const, evaluated, jacobian,
    normal, register_all, resolve, same_within, selected_rewrite, value, var,
)

X, U, V = var(1, 0), var(2, 0), var(2, 1)
ZERO, ONE = const(1, 0), const(1, 1)
R, SINGLE, HALF, OPEN = (Domain(k) for k in ("all", "singleton", "nonnegative", "open_unit"))
G = Map("g", 1, "X", "Y", 1, (X, X * X))
H = Map("h", 1, "Y", "Z", 2, (U * U + V,))
F = Map("f", 1, "X", "Z", 1, ((X * X).scale(2),))
ID = Map("id", 1, "X", "X", 1, (X,))
BRANCH = Map("if_zero", 1, "X", "X", 1, (Piece("zero", ZERO, X),))
ABS = Map("abs", 1, "X", "X", 1, (Piece("nonnegative", X, X.scale(-1)),))
SQUARE = Map("square", 1, "X", "X", 1, (X * X,))
# Computed branch-by-branch substitution of square(abs(x)); no derivative of abs.
ABS_SQUARED = Map("square_after_abs", 1, "X", "X", 1,
                  (Piece("nonnegative", ABS.components[0].yes * ABS.components[0].yes,
                         ABS.components[0].no * ABS.components[0].no),))


def context(f=F, p=Q(0), kind="ambient", domain=R, policy=""):
    return Context(f, (Q(p),), kind, domain, policy)


def polynomial_rule(c, name="direct"):
    return Rule(name, c, jacobian(normal(c.function, c.domain)), "polynomial")


def routes(p=Q(0)):
    c = context(p=p)
    gr = polynomial_rule(context(G, p), "g-rule")
    hc = Context(H, value(G, (Q(p),)), "ambient", Domain("all", 2))
    hr = polynomial_rule(hc, "h-rule")
    direct = polynomial_rule(c)
    chain = Rule("chain", c, ((X.scale(4),),), "chain", (gr, hr))
    return c, direct, chain


class CoherenceRegression(unittest.TestCase):
    def reject(self, code, fn, *args, **kwargs):
        with self.assertRaisesRegex(Reject, "^" + code + "$"):
            fn(*args, **kwargs)

    def test_exact_polynomial_two_routes_and_cotangent_action(self):
        for p in (Q(0), Q(1), Q(-2), Q(2, 3)):
            c, direct, chain = routes(p)
            self.assertEqual(admit(c, direct).matrix, ((X.scale(4),),))
            self.assertEqual(admit(c, chain).matrix, direct.matrix)
            self.assertEqual(evaluated(chain), ((4 * p,),))
            for eta in (Q(1), Q(-3, 5)):
                # h* eta = (2x eta, eta); g*(a,b) = a + 2x b.
                self.assertEqual(2 * p * eta + 2 * p * eta, 4 * p * eta)

    def test_bad_field_passes_zero_sample_but_not_symbolic_certificate(self):
        c, direct, _ = routes()
        bad = replace(direct, identity="bad", matrix=((X.scale(2),),))
        self.assertEqual(evaluated(bad), evaluated(direct))
        self.reject("DERIVATIVE_FORMULA_MISMATCH", admit, c, bad)
        self.assertNotEqual(bad.matrix[0][0].at((Q(1),)), direct.matrix[0][0].at((Q(1),)))

    def test_point_specific_proof_is_valid_but_cannot_be_replayed_elsewhere(self):
        c, direct, _ = routes()
        # 2x is NOT a derivative field, but its value 0 is a genuine derivative at 0.
        point_rule = Rule("point-only", c, ((X.scale(2),),), "point_from", (direct,))
        self.assertEqual(evaluated(admit(c, point_rule)), ((Q(0),),))
        self.reject("SUBJECT_MISMATCH", admit, context(p=1), point_rule)
        # Rebasing both claims forces recomputation and exposes the disagreement.
        c1, d1, _ = routes(1)
        self.reject("POINT_MAP_MISMATCH", admit, c1,
                    replace(point_rule, context=c1, children=(d1,)))

    def test_equal_at_one_point_is_not_primal_germ_equality(self):
        zero = replace(ID, identity="constant", components=(ZERO,))
        c = context(zero)
        identity_rule = polynomial_rule(context(ID), "id-rule")
        claimed = Rule("fake-chain", c, ((ONE,),), "chain", (identity_rule, identity_rule))
        self.assertEqual(value(zero, (Q(0),)), value(ID, (Q(0),)))
        self.reject("MISSING_PRIMAL_GERM_EQUALITY", admit, c, claimed)

    def test_whole_branch_is_identity(self):
        c = context(BRANCH)
        self.assertEqual(normal(BRANCH, R), (X,))
        rule = polynomial_rule(c)
        self.assertEqual(evaluated(admit(c, rule)), ((Q(1),),))
        self.reject("DERIVATIVE_FORMULA_MISMATCH", admit, c,
                    replace(rule, matrix=((ZERO,),)))

    def test_changed_branch_value_invalidates_global_equality(self):
        changed = replace(BRANCH, components=(Piece("zero", ONE, X),))
        self.reject("NO_GERM_PROOF", normal, changed, R)
        unknown = replace(BRANCH, components=(Piece("unknown", ZERO, X),))
        c = context(unknown, kind="within", domain=SINGLE)
        self.reject("UNSUPPORTED_GUARD", admit, c, Rule("bad-ast", c, ((ZERO,),), "singleton"))

    def test_any_linear_map_is_a_singleton_within_derivative(self):
        c = context(BRANCH, kind="within", domain=SINGLE)
        for slope in (0, 1, 7):
            r = Rule(str(slope), c, ((const(1, slope),),), "singleton")
            self.assertEqual(evaluated(admit(c, r)), ((Q(slope),),))

    def test_singleton_has_no_within_uniqueness(self):
        c = context(BRANCH, kind="within", domain=SINGLE)
        r0 = Rule("zero", c, ((ZERO,),), "singleton")
        r1 = replace(r0, identity="one", matrix=((ONE,),))
        self.reject("NO_WITHIN_UNIQUENESS", same_within, c, r0, r1)

    def test_singleton_cannot_be_promoted_or_retagged_as_ambient(self):
        wc, ac = context(BRANCH, kind="within", domain=SINGLE), context(BRANCH)
        r = Rule("within", wc, ((ZERO,),), "singleton")
        self.reject("SUBJECT_MISMATCH", admit, ac, r)
        self.reject("SINGLETON_NOT_AMBIENT", admit, ac, replace(r, context=ac))
        self.reject("WITHIN_NOT_NEIGHBORHOOD", admit, ac,
                    Rule("promoted", ac, r.matrix, "promote", (r,)))

    def test_half_line_unique_within_does_not_promote_at_boundary(self):
        wc, ac = context(ABS, kind="within", domain=HALF), context(ABS)
        r = polynomial_rule(wc)
        self.assertTrue(same_within(wc, r, replace(r, identity="second")))
        self.assertEqual(evaluated(r), ((Q(1),),))
        self.assertTrue(HALF.unique((Q(0),)))
        self.assertFalse(HALF.neighborhood((Q(0),)))
        self.reject("WITHIN_NOT_NEIGHBORHOOD", admit, ac,
                    Rule("promoted", ac, r.matrix, "promote", (r,)))

    def test_half_line_interior_allows_pointwise_promotion(self):
        wc, ac = context(ABS, 1, "within", HALF), context(ABS, 1)
        r = polynomial_rule(wc)
        promoted = Rule("interior", ac, r.matrix, "promote", (r,))
        self.assertEqual(evaluated(admit(ac, promoted)), ((Q(1),),))
        self.reject("SUBJECT_MISMATCH", admit, context(ABS, 0), promoted)

    def test_open_neighborhood_promotion(self):
        wc, ac = context(BRANCH, kind="within", domain=OPEN), context(BRANCH)
        r = polynomial_rule(wc)
        self.assertEqual(evaluated(admit(ac, Rule("open", ac, r.matrix, "promote", (r,)))),
                         ((Q(1),),))

    def test_selected_backward_is_separate_even_for_a_smooth_primal(self):
        sc, ac = context(BRANCH, kind="selected", policy="zero-backward-v1"), context(BRANCH)
        selected = Rule("selected", sc, ((ZERO,),), "policy")
        self.assertEqual(admit(sc, selected, ((ZERO,),)), selected)
        self.reject("SUBJECT_MISMATCH", admit, ac, selected)
        self.reject("SELECTED_IS_NOT_DERIVATIVE", admit, ac, replace(selected, context=ac))

    def test_selected_numeric_agreement_still_requires_derivative_evidence(self):
        sc, ac = context(ID, kind="selected", policy="identity-backward"), context(ID)
        selected = Rule("selected", sc, ((ONE,),), "policy")
        admit(sc, selected, ((ONE,),))
        self.reject("SELECTED_IS_NOT_DERIVATIVE", admit, ac, replace(selected, context=ac))
        self.assertEqual(evaluated(admit(ac, polynomial_rule(ac))), ((Q(1),),))

    def test_primal_equal_rewrite_rejects_different_selected_action(self):
        lc = context(BRANCH, kind="selected", policy="zero")
        rc = context(ID, kind="selected", policy="identity")
        left, right = Rule("left", lc, ((ZERO,),), "policy"), Rule("right", rc, ((ONE,),), "policy")
        self.reject("REWRITE_SELECTED_ACTION", selected_rewrite,
                    lc, left, left.matrix, rc, right, right.matrix)
        zero_policy = replace(rc, policy="explicit-zero")
        preserving = replace(right, context=zero_policy, matrix=left.matrix)
        self.assertTrue(selected_rewrite(lc, left, left.matrix, zero_policy, preserving, left.matrix))

    def test_selected_policy_is_required_and_bound(self):
        c = context(ID, kind="selected", policy="identity")
        r = Rule("selected", c, ((ONE,),), "policy")
        self.reject("MISSING_SELECTED_POLICY", admit, c, r)
        self.reject("SELECTED_POLICY_MISMATCH", admit, c, r, ((ZERO,),))

    def test_optional_rejected_proposal_does_not_poison_proved_route(self):
        c, direct, chain = routes()
        bad = replace(direct, identity="bad", matrix=((X.scale(2),),))
        for order in permutations((bad, chain, direct)):
            result, rejected = resolve(c, order)
            self.assertEqual(result.identity, "chain")
            self.assertEqual(rejected, {"bad": "DERIVATIVE_FORMULA_MISMATCH"})

    def test_required_or_active_invalid_rule_is_not_silently_dropped(self):
        c, direct, chain = routes()
        bad = replace(direct, identity="bad", matrix=((X.scale(2),),))
        self.reject("REQUIRED_RULE_REJECTED", resolve, c, (bad, chain), required="bad")
        self.reject("DERIVATIVE_FORMULA_MISMATCH", register_all, c, (direct, bad))
        self.reject("NO_PROVED_ROUTE", resolve, c, (bad,))

    def test_failed_chain_route_allows_independent_composite_proof(self):
        c = context(ABS_SQUARED)
        gr = Rule("unproved-abs", context(ABS), ((ONE,),), "missing")
        hr = polynomial_rule(context(SQUARE), "square-rule")
        chain = Rule("unavailable-chain", c, ((X.scale(2),),), "chain", (gr, hr))
        direct = polynomial_rule(c)
        result, failures = resolve(c, (chain, direct))
        self.assertEqual(result.identity, "direct")
        self.assertEqual(result.matrix, ((X.scale(2),),))
        self.assertEqual(failures, {"unavailable-chain": "MISSING_EVIDENCE"})

    def test_composite_basepoint_and_nominal_endpoint_are_checked(self):
        c, _, chain = routes(2)
        g, h = chain.children
        moved_h = replace(h, context=replace(h.context, point=(Q(0), Q(0))))
        self.reject("SUBJECT_MISMATCH", admit, c, replace(chain, children=(g, moved_h)))
        wrong = replace(h, context=replace(h.context, function=replace(H, source="other-Y")))
        self.reject("ENDPOINT_MISMATCH", admit, c, replace(chain, children=(g, wrong)))

    def test_subject_revision_environment_domain_and_basepoint_cannot_be_replayed(self):
        c, direct, _ = routes()
        for changed in (replace(c, function=replace(F, revision=2)),
                        replace(c, environment="changed"), replace(c, domain=OPEN),
                        replace(c, point=(Q(1),))):
            self.reject("SUBJECT_MISMATCH", admit, changed, direct)

    def test_rejected_out_of_domain_point_and_wrong_linear_shape(self):
        c = context(ID, 0, "within", OPEN)
        r = polynomial_rule(c)
        moved = replace(c, point=(Q(2),))
        self.reject("DOMAIN_OR_BASEPOINT", admit, moved, replace(r, context=moved))
        self.reject("LINEAR_MAP_SHAPE", admit, c, replace(r, matrix=((ONE, ONE),)))


if __name__ == "__main__":
    unittest.main(verbosity=2)
