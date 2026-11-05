"""Exact small fixtures, not a set/sort library. Run this file for a JSON report."""

from dataclasses import replace
import json

from order_reference import Claim, Invalid, Lattice, Map, Order, Pair, verify


def powerset_example():
    a = Order("order-reference-v1", "P({0,1})", "subset-A", "1",
              ("{}", "{0}", "{1}", "{0,1}"),
              ((True, True, True, True), (False, True, False, True),
               (False, False, True, True), (False, False, False, True)))
    b = Order(a.context, "P({x})", "subset-B", "1", ("{}", "{x}"),
              ((True, True), (False, True)))
    la = Lattice(a, ((0, 1, 2, 3), (1, 1, 3, 3), (2, 3, 2, 3), (3, 3, 3, 3)),
                 ((0, 0, 0, 0), (0, 1, 0, 1), (0, 0, 2, 2), (0, 1, 2, 3)), 0, 3)
    lb = Lattice(b, ((0, 1), (1, 1)), ((0, 0), (0, 1)), 0, 1)
    pair = Pair(Map("direct-image", "1", a, b, (0, 1, 1, 1)),
                Map("inverse-image", "1", b, a, (0, 3)))
    return la, lb, pair


def absolute_order():
    return Order("order-reference-v1", "{-1,0,1}", "absolute-value", "1",
                 ("-1", "0", "1"),
                 ((True, False, True), (True, True, True), (True, False, True)))


def demo():
    la, lb, pair = powerset_example()
    a, b, lower, upper = la.order, lb.order, pair.lower, pair.upper
    absolute = absolute_order()
    reversed_b = replace(b, name="superset-B", le=tuple(zip(*b.le)))
    reversed_pair = Pair(replace(lower, target=reversed_b),
                         replace(upper, source=reversed_b))
    cases = [
        ("two-element-chain", b, "linear_order", None),
        ("powerset-partial", a, "partial_order", None),
        ("powerset-not-total", a, "linear_order", "totality"),
        ("lattice-A", la, "bounded_lattice", None),
        ("lattice-B", lb, "bounded_lattice", None),
        ("direct-inverse-adjunction", pair, "galois", None),
        ("left-binary-joins", lower, "binary_joins", None),
        ("right-binary-meets", upper, "binary_meets", None),
        ("left-all-finite-joins", lower, "all_joins", None),
        ("right-all-finite-meets", upper, "all_meets", None),
        ("false-left-meets", lower, "binary_meets", "preservation"),
        ("false-isomorphism", pair, "order_iso", "left_inverse"),
        ("absolute-preorder", absolute, "preorder", None),
        ("false-absolute-antisymmetry", absolute, "partial_order", "antisymmetry"),
        ("relation-reversed-at-target", reversed_pair, "galois", "lower_monotonicity"),
        ("adjoints-swapped", Pair(upper, lower), "galois", "adjunction"),
    ]
    records = []
    for name, expected, law, error in cases:
        candidate = Claim(expected, law)
        records.append(run_case(name, expected, candidate, law, error))
    other = replace(a, name="another-subset-order")
    records.append(run_case("named-order-replay", other, Claim(a, "partial_order"),
                            "partial_order", "SUBJECT_MISMATCH"))
    records.append(run_case("same-name-reversed-relation", reversed_b,
                            Claim(replace(b, name=reversed_b.name), "linear_order"),
                            "linear_order", "SUBJECT_MISMATCH"))
    return {
        "scope": "finite reference only; no Lean proof or accepted-Core connection",
        "cases": records,
        "counterexamples": {
            "direct_image_of_intersection": b.elements[lower.images[la.meets[1][2]]],
            "intersection_of_direct_images": b.elements[lb.meets[lower.images[1]][lower.images[2]]],
            "upper_lower_of_singleton": a.elements[upper.images[lower.images[1]]],
            "original_singleton": a.elements[1],
        },
    }


def run_case(name, expected, candidate, law, error):
    try:
        counts = verify(expected, candidate, law=law)
        return {"name": name, "accepted": True, "counts": counts, "matched": error is None}
    except Invalid as exc:
        return {"name": name, "accepted": False, "error": exc.code,
                "counterexample": exc.witness, "matched": exc.code == error}


if __name__ == "__main__":
    report = demo()
    print(json.dumps(report, indent=2))
    raise SystemExit(0 if all(case["matched"] for case in report["cases"]) else 1)
