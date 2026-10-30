"""Run the fixed #253 reference and deliberately incorrect mutation fixtures."""

import argparse
from dataclasses import asdict
import json

import elliptic_reference as e


def example(kind="F5"):
    field = e.Field(kind, f"reference::{kind}")
    curve = e.Curve(field, f"reference::E_{kind}")
    return e.Model(curve, f"reference::E_{kind}::short")


def slope_only_mutant(model, left, right):
    """NEGATIVE fixture: affine formulas with inv0, ignoring their hypotheses.

    Keep identity handling so the defect is specifically in the affine branches.
    Return a raw claim: some outputs are off-curve, while (0,0)+(0,0) is not.
    """
    e.check_point(model, left)
    e.check_point(model, right)
    if left.coordinates is None:
        return right
    if right.coordinates is None:
        return left
    field = model.field
    x1, y1 = left.coordinates
    x2, y2 = right.coordinates
    if left == right:
        numerator, denominator = 3 * x1 * x1 - 1, 2 * y1
    else:
        numerator, denominator = y2 - y1, x2 - x1
    slope = field.scalar(numerator * field.inv0(denominator))
    x3 = field.scalar(slope * slope - x1 - x2)
    y3 = field.scalar(slope * (x1 - x3) - y1)
    return e.Point(model, (x3, y3))


def isolated_zero_torsion_mutant(model, left, right):
    """Replace ONLY the P=(0,0) doubling branch by the same wrong slope formula.

    This stronger negative control passes all 64 membership/closure checks but
    fails inverses and associativity. It is not an alternative group operation.
    """
    e.check_point(model, left)
    e.check_point(model, right)
    if left == right and left.coordinates == (0, 0):
        return slope_only_mutant(model, left, right)
    return e.add(model, left, right)


def report():
    model = example()
    audit = e.check_f5_group(model)
    mutant = e.audit_f5_group(model, isolated_zero_torsion_mutant)
    try:
        e.check_f5_group(model, isolated_zero_torsion_mutant)
    except e.Invalid as error:
        mutation_rejection = error.code
    else:
        raise RuntimeError("negative control unexpectedly passed")

    qmodel = example("QQ")
    p = e.point(qmodel, 0, 0)
    wrong = slope_only_mutant(qmodel, p, p)
    e.certify_membership(qmodel, wrong)
    return {
        "status": "Python reference only; Lean, named Group and accepted Core bridges pending",
        "equation": "y^2 = x^3 - x",
        "field": model.field.kind,
        "discriminant": e.certify_model(model).discriminant,
        "point_order": [e.label(p) for p in audit.points],
        "addition_table": [[e.label(p) for p in row] for row in audit.table],
        "checks": {name: asdict(check) for name, check in audit.checks.items()},
        "mutation": {
            "scope": "only (0,0)+(0,0) replaced by the slope-only formula",
            "wrong_double": e.label(slope_only_mutant(model, audit.points[1], audit.points[1])),
            "membership_passes": True,
            "checks": {name: asdict(check) for name, check in mutant.checks.items()},
            "rejection": mutation_rejection,
        },
        "QQ_boundary": {
            "discriminant": str(e.certify_model(qmodel).discriminant),
            "point": e.label(p),
            "double": e.label(e.add(qmodel, p, p)),
            "inverse_sum": e.label(e.add(qmodel, p, e.neg(qmodel, p))),
            "slope_only_double": e.label(wrong),
            "wrong_result_membership_passes": True,
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit the reproducible exact report")
    args = parser.parse_args()
    result = report()
    if args.json:
        print(json.dumps(result, indent=2))
        return
    print(result["status"])
    print(f"E/F5: {result['equation']}; discriminant={result['discriminant']}")
    print("| + | " + " | ".join(result["point_order"]) + " |")
    print("|" + " --- |" * 9)
    for name, row in zip(result["point_order"], result["addition_table"]):
        print("| " + " | ".join([name] + row) + " |")
    for label, checks in (("correct", result["checks"]), ("mutant", result["mutation"]["checks"])):
        for law, check in checks.items():
            print(f"{label}: {law}: checked={check['checked']}, "
                  f"failures={check['failures']}, first_witness={check['witness']}")
    print("mutation rejection:", result["mutation"]["rejection"])
    print("QQ boundary:", result["QQ_boundary"])


if __name__ == "__main__":
    main()
