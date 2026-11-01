"""Runnable #375 exact examples; finite Python results, not proof certificates."""

import json
from dataclasses import replace
from fractions import Fraction as Q

import hodge_reference as h


def diagonal(entries):
    return tuple(tuple(x if i == j else 0 for j in range(len(entries))) for i, x in enumerate(entries))


def example(dimension):
    """Select all fixture data explicitly; production operations infer none of it."""
    names = {3: ("x", "y", "z"), 4: ("t", "x", "y", "z")}[dimension]
    frame = h.Frame("reference:environment", f"R{dimension}", "real-base", "origin-fiber",
                    "finite-real-space", "1", "named:QQ", h.SCALAR_PROFILE,
                    "ordered-coordinate-basis", "corresponding-dual-basis", dimension, names)
    entries = (1, 1, 1) if dimension == 3 else (-1, 1, 1, 1)
    metric = h.Metric(frame, "euclidean" if dimension == 3 else "minkowski-minus-plus", "1", diagonal(entries))
    evidence = h.HodgeEvidence(
        h.NondegenerateEvidence(metric, diagonal(entries)),
        h.SignatureEvidence(metric, diagonal((1,) * dimension), entries, int(dimension == 4)),
        h.VolumeEvidence(metric, Q(1)),
    )
    return metric, evidence, h.Orientation(frame, 1)


def run():
    g, e, o = example(3)
    m, me, mo = example(4)
    xy = h.basis_form(g.frame, (0, 1))
    ex, ey = h.PolarVector(g.frame, (1, 0, 0)), h.PolarVector(g.frame, (0, 1, 0))
    axial = h.cross_twisted(g, ex, ey, e)
    reflected = h.FrameAutomorphism(g.frame, diagonal((-1, 1, 1)), diagonal((-1, 1, 1)))
    h.check_isometry(g, reflected)
    checks = {}

    def check(name, action, code="OK"):
        try:
            result = action()
            actual = "OK" if result is not False else "VALUE_MISMATCH"
        except h.Invalid as error:
            actual = error.code
        checks[name] = {"expected": code, "actual": actual, "passed": code == actual}

    check("euclidean_star_xy", lambda: h.star(g, xy, e, o).components == (0, 0, 1))
    check("cross_direction", lambda: h.display_twisted(axial, o) == (0, 0, 1))
    check("orientation_reversal", lambda: h.display_twisted(axial, replace(o, sign=-1)) == (0, 0, -1))
    check("twisted_reflection", lambda: h.cross_twisted(g, reflected.act(ex), reflected.act(ey), e) == reflected.act(axial))
    for degree in range(4):
        for blade in h.indices(g.frame, degree):
            a = h.basis_form(g.frame, blade)
            check(f"euclidean_square_{blade}", lambda a=a: h.star(g, h.star(g, a, e, o), e, o) == a)
    lorentz_table = {}
    for blade in h.indices(m.frame, 2):
        a = h.basis_form(m.frame, blade)
        result = h.star(m, a, me, mo)
        lorentz_table[str(blade)] = result.components
        check(f"lorentz_definition_{blade}", lambda a=a, result=result: h.verify_star(m, a, me, result, orientation=mo))
        check(f"lorentz_square_{blade}", lambda a=a: h.star(m, h.star(m, a, me, mo), me, mo) == h.scale(a, -1))
    tx = h.basis_form(m.frame, (0, 1))
    check("reject_euclidean_sign", lambda: h.verify_star(m, tx, me, h.basis_form(m.frame, (2, 3)), orientation=mo),
          "HODGE_IDENTITY_FAILED")
    check("reject_missing_orientation", lambda: h.star(g, xy, e, None), "MISSING_ORIENTATION")
    check("reject_missing_inverse", lambda: h.star(g, xy, replace(e, nondegenerate=None), o), "MISSING_NONDEGENERACY")
    scaled = replace(g, metric_id="nonorthonormal", gram=diagonal((4, 1, 1)))
    se = h.HodgeEvidence(h.NondegenerateEvidence(scaled, diagonal((Q(1, 4), 1, 1))),
                         h.SignatureEvidence(scaled, diagonal((1, 1, 1)), (4, 1, 1), 0),
                         h.VolumeEvidence(scaled, Q(2)))
    check("nonorthonormal_rational", lambda: h.star(scaled, xy, se, o).components == (0, 0, Q(1, 2)))
    irrational = replace(g, metric_id="requires-sqrt2", gram=diagonal((2, 1, 1)))
    ie = h.HodgeEvidence(h.NondegenerateEvidence(irrational, diagonal((Q(1, 2), 1, 1))),
                         h.SignatureEvidence(irrational, diagonal((1, 1, 1)), (2, 1, 1), 0),
                         h.VolumeEvidence(irrational, Q(1)))
    check("reject_falsely_rational_star", lambda: h.star(irrational, xy, ie, o), "COEFFICIENT_EXTENSION_REQUIRED")
    return {
        "scope": "Finite exact Python reference only; no Lean proof, accepted Core, native refinement or physical guarantee",
        "convention": "alpha wedge star(beta) = <alpha,beta>_g vol; negative-square count q; star^2=(-1)^(k(n-k)+q)",
        "minkowski_gram": m.gram,
        "minkowski_orientation": "dt wedge dx wedge dy wedge dz",
        "two_form_order": h.indices(m.frame, 2),
        "lorentz_star_table": lorentz_table,
        "checks": checks,
    }


if __name__ == "__main__":
    report = run()
    print(json.dumps(report, indent=2, default=str))
    raise SystemExit(0 if all(c["passed"] for c in report["checks"].values()) else 1)
