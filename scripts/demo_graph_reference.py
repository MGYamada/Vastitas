"""Print inspectable exact examples, including ordered occurrence/profile data."""

import json
from dataclasses import asdict
from enum import Enum
from fractions import Fraction

from graph_reference import (
    Boundary, Direction, FIXTURES, Rejected, Rule, Strand, check_rewrite,
    evidence_for, evaluate, make_word, propose_rewrite, right_bracketing,
)


def example(degrees, instructions, fixture="braided_two"):
    source = Boundary(
        "demo:fixed-presentation", right_bracketing(len(degrees)),
        tuple(Strand(f"strand:{i}", f"object:{i}", a) for i, a in enumerate(degrees)),
    )
    return make_word(FIXTURES[fixture].key, source, instructions)


def exact_json(value):
    if isinstance(value, Fraction):
        return {"numerator": value.numerator, "denominator": value.denominator}
    if isinstance(value, Enum):
        return value.name
    raise TypeError(type(value).__name__)


def main():
    plus, minus = Direction.POSITIVE, Direction.NEGATIVE
    double = example((1, 1), ((0, plus), (0, plus)))
    inverse = example((1, 1), ((0, plus), (0, minus)))
    symmetric = example((1, 1), ((0, plus), (0, plus)), "symmetric_sign")
    lhs = example((1, 2, 3), ((0, plus), (1, plus), (0, plus)))
    rhs = example((1, 2, 3), ((1, plus), (0, plus), (1, plus)))
    output = {
        "status": "Python exact reference only; no Lean proof or Vastitas execution",
        "examples": {},
        "checked_rewrites": {},
        "rejections": {},
    }
    for name, w in (("braided_double", double), ("braided_inverse", inverse),
                    ("symmetric_double", symmetric), ("braid_123_left", lhs),
                    ("braid_123_right", rhs)):
        output["examples"][name] = {"word": asdict(w), "observation": asdict(evaluate(w))}
    for name, w, rule in (("inverse", inverse, Rule.INVERSE),
                          ("symmetric", symmetric, Rule.SYMMETRIC),
                          ("braid", lhs, Rule.BRAID)):
        claim = propose_rewrite(w, 0, rule, evidence_for(w.profile, rule))
        after = check_rewrite(w, claim)
        output["checked_rewrites"][name] = {
            "rule": rule, "remaining_crossings": len(after.crossings),
            "scalar": evaluate(after).scalar,
        }
    attempts = {
        "monoidal_crossing": lambda: example((1, 1), ((0, plus),), "monoidal"),
        "braided_same_direction_as_inverse": lambda: propose_rewrite(
            double, 0, Rule.INVERSE, evidence_for(double.profile, Rule.INVERSE)),
        "symmetry_evidence_from_another_profile": lambda: propose_rewrite(
            double, 0, Rule.SYMMETRIC, evidence_for(symmetric.profile, Rule.SYMMETRIC)),
    }
    for name, attempt in attempts.items():
        try:
            attempt()
        except Rejected as error:
            output["rejections"][name] = str(error)
        else:
            raise AssertionError(f"expected rejection: {name}")
    print(json.dumps(output, indent=2, default=exact_json, ensure_ascii=False))


if __name__ == "__main__":
    main()
