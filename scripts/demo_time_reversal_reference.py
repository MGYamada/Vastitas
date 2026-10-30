"""Inspectable exact JSON for #301; no compiler, Lean or empirical certification."""

import json
from dataclasses import asdict, replace

import time_reversal_reference as tr
from demo_graph_reference import exact_json


def encode(value):
    if type(value) is tr.Qi:
        return asdict(value)
    return exact_json(value)


def main():
    output = {
        "status": "Python exact finite matrix observations over Q(i)",
        "lean_proof": False,
        "accepted_core_connection": False,
        "physical_identification_verified": False,
        "models": {},
        "expected_rejections": {},
    }
    reports = {}
    for model in (tr.SPIN_HALF, tr.SPINLESS):
        c = tr.reference_coordinates(model)
        target = tr.Selection(c, model.profile)
        t = tr.Semilinear(c, "T", model.reference_matrix, tr.ScalarAction.CONJUGATE)
        report = tr.check_time_reversal(target, t)
        reports[model.model_id] = report
        output["models"][model.model_id] = asdict(report)
    report = reports[tr.SPIN_HALF.model_id]
    target, t = report.expected, report.candidate
    dropped = replace(t, scalar_action=tr.ScalarAction.IDENTITY)
    dropped_report = tr.observe_time_reversal(target, dropped)
    output["dropped_K"] = {
        "matrix_checks_still_hold": all(r.holds for r in dropped_report.matrix_relations),
        "antilinearity_holds": all(r.holds for r in dropped_report.vector_relations),
        "observation": asdict(dropped_report),
    }
    phased_target, phased = replace(target, phase=tr.I), tr.rephase(t, tr.I)
    phased_report = tr.check_time_reversal(phased_target, phased)
    ordinary_square = tr.mul(phased.entries, phased.entries)
    output["phase_i"] = {
        "observation": asdict(phased_report),
        "incorrect_ordinary_square": ordinary_square,
    }
    b = tr.matrix([[1, 0], [0, tr.I]])
    changed = replace(target.coordinates, basis=tr.Basis(
        "fixture:complex-basis", tr.SPIN_HALF.model_id, ("up", "i down"), b))
    changed_target, transported = replace(target, coordinates=changed), tr.transport(t, changed)
    output["basis_transport"] = asdict(tr.check_time_reversal(changed_target, transported))
    h = tr.Subject(target.coordinates, "H", tr.SubjectKind.HAMILTONIAN, tr.ID2)
    p = tr.Subject(target.coordinates, "P-up", tr.SubjectKind.PURE_STATE_PROJECTOR,
                   tr.matrix([[1, 0], [0, 0]]))
    h_report = tr.check_invariance(target, t, h)
    p_report = tr.observe_invariance(target, t, p)
    output["Hamiltonian"] = asdict(h_report)
    output["state"] = asdict(p_report)
    output["state_transformed"] = p_report.transformed
    attempts = {
        "dropped_K_despite_correct_original_square": lambda: tr.check_time_reversal(target, dropped),
        "ordinary_square_after_phase_i": lambda: tr.check_time_reversal(
            phased_target, phased,
            replace(phased_report, square=replace(phased_report.square, entries=ordinary_square))),
        "spinless_evidence_for_spin_half": lambda: tr.check_time_reversal(
            target, t, reports[tr.SPINLESS.model_id]),
        "symmetric_H_implies_invariant_state": lambda: tr.check_invariance(target, t, p, h_report),
        "ordinary_linear_basis_transport": lambda: tr.check_time_reversal(
            changed_target, replace(transported, entries=tr.mul(
                tr.mul(tr.conjugate_transpose(b), t.entries), b))),
    }
    for name, attempt in attempts.items():
        try:
            attempt()
        except tr.Rejected as error:
            output["expected_rejections"][name] = str(error)
        else:
            raise AssertionError(f"expected rejection: {name}")
    print(json.dumps(output, indent=2, default=encode, ensure_ascii=False))


if __name__ == "__main__":
    main()
