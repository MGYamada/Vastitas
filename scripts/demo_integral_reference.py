"""Hand-supplied finite integral candidates for #293; no adaptive search."""

import argparse
import json
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path

import integral_reference as ir


def interval(a, b):
    if any(type(x) not in (int, Q) for x in (a, b)):
        raise ir.Invalid("INVALID_SCHEMA", "demo endpoints must be exact")
    return ir.Interval(Q(a), Q(b))


def cell(a, b, polynomial, delta, proof_form=ir.LOCAL_PROOF):
    domain = interval(a, b)
    if type(delta) not in (int, Q):
        raise ir.Invalid("INVALID_SCHEMA", "demo delta must be exact")
    return ir.Cell(domain, polynomial, Q(delta), domain, proof_form)


def examples():
    x = ir.Poly.variable(0, 1)
    target = ir.Target("reference:environment:1", "reference:real-line", "x",
                       ir.PolynomialFunction("square", "1", x ** 2), interval(0, 1))
    request = ir.Request(target, Q(1, 16))
    coarse = ir.Certificate(target, (cell(0, 1, x, Q(1, 4)),),
                            ir.Totals((Q(1, 2),), Q(1, 2), Q(1, 4), interval(Q(1, 4), Q(3, 4))))
    refined = ir.Certificate(
        target, (cell(0, Q(1, 2), Q(1, 2) * x, Q(1, 16)),
                 cell(Q(1, 2), 1, Q(3, 2) * x - Q(1, 2), Q(1, 16))),
        ir.Totals((Q(1, 16), Q(5, 16)), Q(3, 8), Q(1, 16), interval(Q(5, 16), Q(7, 16))))
    exact = ir.Certificate(target, (cell(0, 1, x ** 2, 0),),
                           ir.Totals((Q(1, 3),), Q(1, 3), Q(0), interval(Q(1, 3), Q(1, 3))))
    false_bound = replace(coarse, cells=(replace(coarse.cells[0], delta=Q(1, 8)),),
                          claimed=ir.Totals((Q(1, 2),), Q(1, 2), Q(1, 8),
                                            interval(Q(3, 8), Q(5, 8))))
    bump_target = replace(target, function=ir.PolynomialFunction("bump", "1", 16 * x ** 2 * (x - 1) ** 2))
    zero_totals = ir.Totals((), Q(0), Q(0), interval(0, 0))
    endpoint_only = ir.Certificate(
        bump_target, (cell(0, 1, ir.Poly.constant(0, 1), 0, "endpoint-samples/v1"),),
        replace(zero_totals, local_integrals=(Q(0),)))
    zero_target = replace(target, interval=interval(Q(3, 7), Q(3, 7)))
    return {
        "coarse_goal_unmet": (request, coarse),
        "refined_goal_met": (request, refined),
        "exact_singleton": (request, exact),
        "false_delta": (request, false_bound),
        "endpoint_only": (ir.Request(bump_target, Q(1, 16)), endpoint_only),
        "zero_length": (ir.Request(zero_target, Q(1, 16)),
                        ir.Certificate(zero_target, (), zero_totals)),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-dir", type=Path, help="write separate request/certificate JSON pairs")
    args = parser.parse_args()
    output = {"scope": "Python reference only; no Lean/Core/native guarantee", "cases": {}}
    for name, (request, certificate) in examples().items():
        report = ir.verify(request, certificate)
        output["cases"][name] = {
            "accepted_reference": report.accepted, "goal_status": report.goal_status,
            "totals": None if report.artifact is None else ir.totals_data(report.artifact.totals),
            "failures": [check.code for check in report.checks if check.status != "pass"],
        }
        if args.write_dir:
            args.write_dir.mkdir(parents=True, exist_ok=True)
            for kind, data in (("request", ir.request_data(request)),
                               ("certificate", ir.certificate_data(certificate))):
                (args.write_dir / f"{name}.{kind}.json").write_text(
                    json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
