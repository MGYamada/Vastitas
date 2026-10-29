"""Run with Python's standard library. Outcomes are reference checks, not Lean proofs."""

from dataclasses import replace
from fractions import Fraction as Q

import l2_tail_reference as ref


def main():
    env = ref.Environment(dependencies=(("fixture:analysis", "1"),))
    x = ref.ReferenceCore("fixture:x", "1", ref.Geometric(Q(1), Q(1, 2)))
    r = ref.ReferenceCore("fixture:reciprocal", "1", ref.Reciprocal(Q(1)))
    y = replace(x, body=ref.PrefixThenConstant(tuple(ref.term(x, n) for n in range(8)), Q(1)))
    opaque = replace(x, body=ref.Opaque("arbitrary generator without evidence"))
    cert = ref.propose_certificate(x, env)
    cases = (
        ("geometric", x, cert),
        ("reciprocal", r, ref.propose_certificate(r, env)),
        ("underestimated bound", x, replace(cert, bound=ref.GeometricBound(Q(1), Q(1, 4)))),
        ("evidence reused on matching prefix", y, cert),
        ("missing evidence", opaque, None),
    )
    print("Reference rule checks only; Lean soundness and compiler integration are pending.")
    for name, core, evidence in cases:
        result = ref.check_certificate(core, env, evidence)
        print(f"{name}: {result.outcome.value} ({result.reason})")
    print(f"shared prefix squared norm = {ref.finite_tail_square_sum(y, 0, 8)}")
    print(f"borrowed B(8) = {ref.tail_value(cert.bound, 8)}; y[8]^2 = {ref.term(y, 8)**2}")


if __name__ == "__main__":
    main()
