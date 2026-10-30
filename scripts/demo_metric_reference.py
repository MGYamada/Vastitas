"""Run the exact two-dimensional #264 example (Python reference only)."""

import json
from dataclasses import replace
from fractions import Fraction as Q

import metric_free_reference as mf
import metric_reference as mr


def example():
    xy = mf.Frame("reference:environment:1", "reference:R2", "reference:real-base",
                  "chart:xy", "frame:xy", "dual:xy", "model:real-plane", "1", ("x", "y"))
    uv = replace(xy, chart_id="chart:uv", tangent_frame_id="frame:uv",
                 cotangent_frame_id="dual:uv", coordinates=("u", "v"))
    change = mf.CoordinateChange(uv, xy, ((1, 1), (0, 1)))
    point = mf.Point(xy, (1, 2))
    source = mf.Point(uv, (-1, 2))
    function = mf.ScalarPolynomial(xy, mf.X ** 2 + mf.X * mf.Y + 3 * mf.Y ** 2)
    g = mr.Metric(xy, "metric:g", "1", ((2, 0), (0, 3)))
    h = mr.Metric(xy, "metric:h", "1", ((2, 1), (1, 2)))
    return function, point, source, change, g, h


def run():
    function, point, source, change, g, h = example()
    alpha = mf.differential(function, point)
    g_fiber, h_fiber = mr.FiberMetric(g, point), mr.FiberMetric(h, point)
    g_evidence, h_evidence = (mr.certify_nondegenerate(s) for s in (g_fiber, h_fiber))
    grad_g = mr.gradient(function, point, using=g, evidence=g_evidence)
    grad_h = mr.gradient(function, point, using=h, evidence=h_evidence)
    alpha_u = mf.differential(change.reexpress(function), source)
    g_u = mr.reexpress_metric(change, g)
    grad_u = mr.sharp(mr.FiberMetric(g_u, source), alpha_u,
                      mr.certify_nondegenerate(mr.FiberMetric(g_u, source)))
    wrong_df = mf.Cotangent(source, mf.matvec(mf.inverse(change.forward), alpha.components))
    singular = mr.FiberMetric(replace(g, metric_id="metric:singular", gram=((1, 0), (0, 0))), point)
    indefinite = mr.FiberMetric(replace(g, metric_id="metric:indefinite", gram=((1, 0), (0, -1))), point)
    checks = {}

    def check(name, action, expected="OK"):
        try:
            action()
            actual = "OK"
        except mf.Invalid as error:
            actual = error.code
        checks[name] = {"expected": expected, "actual": actual, "passed": actual == expected}

    check("cotangent_transport", lambda: mf.check_cotangent_transport(change, source, alpha, alpha_u))
    check("metric_transport", lambda: mr.check_metric_transport(change, g, g_u))
    check("gradient_transport", lambda: mr.check_gradient_transport(change, source, g, alpha, grad_g, grad_u))
    check("df_as_vector", lambda: mf.check_cotangent_transport(change, source, alpha, wrong_df),
          "COTANGENT_TRANSPORT_MISMATCH")
    check("singular_nondegeneracy", lambda: mr.certify_nondegenerate(singular), "SINGULAR")
    check("indefinite_nondegeneracy", lambda: mr.certify_nondegenerate(indefinite))
    check("indefinite_positivity", lambda: mr.certify_riemannian(indefinite), "NOT_POSITIVE_DEFINITE")
    twin = mr.FiberMetric(replace(g, metric_id="metric:equal-matrix-twin"), point)
    check("equal_matrix_evidence_replay", lambda: mr.sharp(twin, alpha, g_evidence),
          "EVIDENCE_SUBJECT_MISMATCH")
    before = mf.cotangent_pullback(change.as_map(), source, alpha)
    for metric in (g, h):
        mr.gradient(function, point, using=metric,
                    evidence=mr.certify_nondegenerate(mr.FiberMetric(metric, point)))
    unchanged = (alpha == mf.differential(function, point)
                 and before == mf.cotangent_pullback(change.as_map(), source, alpha))
    checks["metric_free_invariance"] = {"passed": unchanged}
    known = (alpha.components == (4, 13) and grad_g.value.components == (2, Q(13, 3))
             and grad_h.value.components == (Q(-5, 3), Q(22, 3))
             and alpha_u.components == (4, 17) and g_u.gram == ((2, 2), (2, 5))
             and grad_u.value.components == (Q(-7, 3), Q(13, 3))
             and wrong_df.components == (-9, 13))
    checks["known_exact_values"] = {"passed": known}
    return {
        "scope": "Exact Python reference over R^2; finite tests, no Lean proof or accepted Core",
        "df": alpha.components,
        "gradient_g": grad_g.value.components,
        "gradient_h": grad_h.value.components,
        "df_in_uv": alpha_u.components,
        "metric_g_in_uv": g_u.gram,
        "gradient_g_in_uv": grad_u.value.components,
        "pushed_gradient": change.push_tangent(grad_u.value).components,
        "wrong_vector_transform_of_df": wrong_df.components,
        "checks": checks,
    }


if __name__ == "__main__":
    report = run()
    print(json.dumps(report, indent=2, default=str))
    raise SystemExit(0 if all(check["passed"] for check in report["checks"].values()) else 1)
