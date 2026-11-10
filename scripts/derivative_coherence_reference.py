"""Finite exact reference for derivative-rule admission; not Vastitas or Lean.

Python 3.10+, standard library only. Coefficients are rational, functions real.
Only the proof constructors below are supported. No general analytic decision
procedure, numeric sampling certificate, or user-provided success bit exists.
"""
from dataclasses import dataclass
from fractions import Fraction as Q


class Reject(Exception):
    pass


def need(condition, code):
    if not condition:
        raise Reject(code)


@dataclass(frozen=True)
class Poly:
    n: int
    terms: tuple

    @staticmethod
    def make(n, terms):
        d = {}
        for exponent, coefficient in terms:
            need(len(exponent) == n and all(type(e) is int and e >= 0 for e in exponent),
                 "POLYNOMIAL_SHAPE")
            d[tuple(exponent)] = d.get(tuple(exponent), Q(0)) + Q(coefficient)
        return Poly(n, tuple(sorted((e, c) for e, c in d.items() if c)))

    def __add__(self, other):
        need(self.n == other.n, "POLYNOMIAL_SHAPE")
        return Poly.make(self.n, self.terms + other.terms)

    def __mul__(self, other):
        need(self.n == other.n, "POLYNOMIAL_SHAPE")
        return Poly.make(self.n, ((tuple(a + b for a, b in zip(e, f)), c * d)
                                 for e, c in self.terms for f, d in other.terms))

    def scale(self, scalar):
        return Poly.make(self.n, ((e, Q(scalar) * c) for e, c in self.terms))

    def diff(self, i):
        return Poly.make(self.n, ((tuple(a - (j == i) for j, a in enumerate(e)), c * e[i])
                                 for e, c in self.terms if e[i]))

    def at(self, point):
        need(len(point) == self.n, "BASEPOINT_DIMENSION")
        result = Q(0)
        for e, c in self.terms:
            for x, power in zip(point, e):
                c *= Q(x) ** power
            result += c
        return result

    def subst(self, args):
        need(len(args) == self.n and len({a.n for a in args}) == 1, "SUBSTITUTION_SHAPE")
        n = args[0].n
        result = const(n, 0)
        for e, c in self.terms:
            term = const(n, c)
            for arg, power in zip(args, e):
                for _ in range(power):
                    term = term * arg
            result = result + term
        return result


def const(n, c):
    return Poly.make(n, [((0,) * n, c)])


def var(n, i):
    return Poly.make(n, [(tuple(int(j == i) for j in range(n)), 1)])


@dataclass(frozen=True)
class Piece:
    guard: str  # exactly x == 0, or x >= 0, in R
    yes: Poly
    no: Poly


@dataclass(frozen=True)
class Domain:
    kind: str  # all, singleton, nonnegative, open_unit
    n: int = 1

    def contains(self, p):
        need(len(p) == self.n, "BASEPOINT_DIMENSION")
        if self.kind == "all":
            return True
        need(self.n == 1, "UNSUPPORTED_DOMAIN")
        if self.kind == "singleton":
            return p[0] == 0
        if self.kind == "nonnegative":
            return p[0] >= 0
        if self.kind == "open_unit":
            return -1 < p[0] < 1
        raise Reject("UNSUPPORTED_DOMAIN")

    def unique(self, p):
        # Closed finite domain catalogue, requiring future real-analysis proofs.
        return self.contains(p) and self.kind != "singleton"

    def neighborhood(self, p):
        return self.contains(p) and (self.kind in ("all", "open_unit") or
                                    (self.kind == "nonnegative" and p[0] > 0))


@dataclass(frozen=True)
class Map:
    identity: str
    revision: int
    source: str
    target: str
    n: int
    components: tuple


def check_map(f):
    need(type(f.n) is int and f.n > 0 and f.components, "MAP_SHAPE")
    for e in f.components:
        if isinstance(e, Piece):
            need(f.n == 1 and e.guard in ("zero", "nonnegative"), "UNSUPPORTED_GUARD")
            polys = (e.yes, e.no)
        else:
            polys = (e,)
        for a in polys:
            need(isinstance(a, Poly) and a.n == f.n, "POLYNOMIAL_SHAPE")
            need(Poly.make(a.n, a.terms) == a, "NONCANONICAL_POLYNOMIAL")


def value(f, p):
    values = []
    for e in f.components:
        if isinstance(e, Piece):
            need(f.n == 1 and e.guard in ("zero", "nonnegative"), "UNSUPPORTED_GUARD")
            choose = p[0] == 0 if e.guard == "zero" else p[0] >= 0
            e = e.yes if choose else e.no
        values.append(e.at(p))
    return tuple(values)


def normal(f, domain):
    """Exact global/on-domain polynomial equalities; never sample-based."""
    out = []
    for e in f.components:
        if isinstance(e, Piece):
            need(f.n == 1, "UNSUPPORTED_GUARD")
            if e.guard == "zero":
                need(e.yes.at((Q(0),)) == e.no.at((Q(0),)), "NO_GERM_PROOF")
                e = e.no  # the only exceptional point agrees; all other x use no
            elif e.guard == "nonnegative":
                if e.yes == e.no:
                    e = e.yes
                elif domain.kind == "nonnegative":
                    e = e.yes
                else:
                    raise Reject("NO_GERM_PROOF")
            else:
                raise Reject("UNSUPPORTED_GUARD")
        need(e.n == f.n, "POLYNOMIAL_SHAPE")
        out.append(e)
    return tuple(out)


def jacobian(components):
    return tuple(tuple(e.diff(i) for i in range(e.n)) for e in components)


def matmul(a, b):
    n = b[0][0].n
    return tuple(tuple(sum((a[i][k] * b[k][j] for k in range(len(b))), const(n, 0))
                       for j in range(len(b[0]))) for i in range(len(a)))


@dataclass(frozen=True)
class Context:
    function: Map
    point: tuple
    contract: str  # ambient, within, selected
    domain: Domain
    policy: str = ""
    environment: str = "exact-real-reference-v1"


@dataclass(frozen=True)
class Rule:
    identity: str
    context: Context
    matrix: tuple  # linearization formula; its transpose encodes the backward
    proof: str
    children: tuple = ()


def admit(expected, rule, policy_matrix=None):
    """Validate against an independently supplied request; return no trusted flag."""
    need(rule.context == expected, "SUBJECT_MISMATCH")
    f, p, d = expected.function, expected.point, expected.domain
    check_map(f)
    need(d.n == f.n and d.contains(p), "DOMAIN_OR_BASEPOINT")
    need(len(rule.matrix) == len(f.components) and
         all(len(row) == f.n for row in rule.matrix) and
         all(isinstance(a, Poly) and a.n == f.n for row in rule.matrix for a in row),
         "LINEAR_MAP_SHAPE")
    need(all(Poly.make(a.n, a.terms) == a for row in rule.matrix for a in row),
         "NONCANONICAL_POLYNOMIAL")
    if expected.contract == "selected":
        need(rule.proof == "policy" and expected.policy and policy_matrix is not None,
             "MISSING_SELECTED_POLICY")
        need(rule.matrix == policy_matrix, "SELECTED_POLICY_MISMATCH")
        return rule
    need(expected.contract in ("ambient", "within"), "UNKNOWN_CONTRACT")
    need(not expected.policy and rule.proof != "policy", "SELECTED_IS_NOT_DERIVATIVE")
    if expected.contract == "ambient":
        need(d.neighborhood(p), "DOMAIN_NOT_NEIGHBORHOOD")
    if rule.proof == "singleton":
        need(expected.contract == "within" and d.kind == "singleton", "SINGLETON_NOT_AMBIENT")
        return rule  # any continuous linear map is a within derivative here
    if rule.proof == "promote":
        need(expected.contract == "ambient" and len(rule.children) == 1, "BAD_PROMOTION")
        child = rule.children[0]
        child_expected = Context(f, p, "within", child.context.domain,
                                 environment=expected.environment)
        admit(child_expected, child)
        need(child.context.domain.neighborhood(p), "WITHIN_NOT_NEIGHBORHOOD")
        need(child.matrix == rule.matrix, "PROMOTION_MAP_CHANGED")
        return rule
    if rule.proof == "point_from":
        need(len(rule.children) == 1, "MISSING_POINT_PROOF")
        child = rule.children[0]
        admit(expected, child)
        need(evaluated(child) == evaluated(rule), "POINT_MAP_MISMATCH")
        return rule  # only at this exact basepoint, with a derivative proof
    if rule.proof == "polynomial":
        wanted = jacobian(normal(f, d))
    elif rule.proof == "chain":
        need(expected.contract == "ambient" and d.kind == "all" and len(rule.children) == 2,
             "UNSUPPORTED_CHAIN_DOMAIN")
        gr, hr = rule.children
        g, h = gr.context.function, hr.context.function
        need(g.source == f.source and g.target == h.source and h.target == f.target and
             g.n == f.n and h.n == len(g.components), "ENDPOINT_MISMATCH")
        admit(Context(g, p, "ambient", Domain("all", g.n), environment=expected.environment), gr)
        admit(Context(h, value(g, p), "ambient", Domain("all", h.n),
                      environment=expected.environment), hr)
        gp = normal(g, Domain("all", g.n))
        hp = normal(h, Domain("all", h.n))
        need(normal(f, d) == tuple(e.subst(gp) for e in hp), "MISSING_PRIMAL_GERM_EQUALITY")
        wanted = matmul(tuple(tuple(e.subst(gp) for e in row) for row in hr.matrix), gr.matrix)
    else:
        raise Reject("MISSING_EVIDENCE")
    # Equality of rational-polynomial coefficients, for every point in scope.
    need(rule.matrix == wanted, "DERIVATIVE_FORMULA_MISMATCH")
    return rule


def same_within(expected, left, right):
    need(expected.contract == "within", "NOT_WITHIN")
    admit(expected, left)
    admit(expected, right)
    need(expected.domain.unique(expected.point), "NO_WITHIN_UNIQUENESS")
    return evaluated(left) == evaluated(right)


def evaluated(rule):
    return tuple(tuple(e.at(rule.context.point) for e in row) for row in rule.matrix)


def resolve(expected, proposals, required=None):
    """Optional proposals are not admitted registrations. Required rules fail closed."""
    need(expected.contract == "ambient", "NOT_AMBIENT_REQUEST")
    ids = [r.identity for r in proposals]
    need(len(ids) == len(set(ids)), "DUPLICATE_RULE_ID")
    passed, rejected = [], {}
    for r in proposals:
        try:
            passed.append(admit(expected, r))
        except Reject as exc:
            rejected[r.identity] = str(exc)
    if required is not None:
        need(required in ids, "REQUIRED_RULE_MISSING")
        need(required not in rejected, "REQUIRED_RULE_REJECTED")
        passed = [r for r in passed if r.identity == required]
    need(passed, "NO_PROVED_ROUTE")
    need(all(evaluated(r) == evaluated(passed[0]) for r in passed), "COHERENCE_FAILURE")
    return min(passed, key=lambda r: r.identity), rejected


def register_all(expected, rules):
    # A required/active registration never gets silently discarded by fallback.
    for rule in rules:
        admit(expected, rule)
    return tuple(rules)


def selected_rewrite(left_context, left, left_policy, right_context, right, right_policy):
    need(left_context.contract == right_context.contract == "selected", "NOT_SELECTED")
    admit(left_context, left, left_policy)
    admit(right_context, right, right_policy)
    need((left_context.function.source, left_context.function.target, left_context.point,
          left_context.domain, left_context.environment) ==
         (right_context.function.source, right_context.function.target, right_context.point,
          right_context.domain, right_context.environment), "REWRITE_CONTEXT")
    need(normal(left_context.function, left_context.domain) ==
         normal(right_context.function, right_context.domain), "REWRITE_PRIMAL")
    need(left.matrix == right.matrix, "REWRITE_SELECTED_ACTION")
    return True
