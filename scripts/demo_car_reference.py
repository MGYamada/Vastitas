"""Run #246's exact finite examples and print inspectable JSON, no dependencies."""

import json
from dataclasses import asdict, replace

import car_reference as cr
import graph_reference as graph
from demo_graph_reference import exact_json


def main():
    output = {
        "status": "Python exact matrix observations; no Vastitas execution or Lean proof",
        "production_graph_authority": False,
        "car": {},
        "expected_negatives": {},
    }
    for n in (1, 2):
        ops = cr.annihilators(n)
        report = cr.observe_car(ops, ops[0].model.adjoint_profile)
        if not report.all_hold:
            raise AssertionError(f"{n}-mode CAR failed")
        output["car"][str(n)] = {"relations_checked": len(report.relations),
                                  "all_hold": report.all_hold, "observation": asdict(report)}
    a, b = cr.spin_x()
    spins = cr.observe_spins((a, b))
    if not spins.all_hold:
        raise AssertionError("ordinary spin tensor failed")
    output["spins"] = {"all_hold": spins.all_hold, "observation": asdict(spins)}
    pauli = cr.observe_pauli()
    if not all(r.holds for r in pauli.relations):
        raise AssertionError("Pauli relations failed")
    output["pauli"] = {"observation": asdict(pauli),
                       "cl2_image_rank": cr.require_independent_images(pauli.cl2_images),
                       "cl3_image_rank": cr.span_rank(pauli.cl3_images)}
    c1, c2 = cr.annihilators(2)
    dropped = cr.observe_car((c1, replace(c2, entries=cr.kron(cr.ID2, cr.R))),
                             c1.model.adjoint_profile)
    wrong_spin = cr.observe_spins((a, replace(b, entries=cr.kron(cr.Z, cr.X))))
    for name, report in (("dropped_Z", dropped), ("fermionic_sign_on_spin_site", wrong_spin)):
        if report.all_hold:
            raise AssertionError(f"expected failure: {name}")
        output["expected_negatives"][name] = {
            "failed_relations": [asdict(r) for r in report.relations if not r.holds],
        }
    word = cr.exchange_word(c1.model, 1, 1, double=True)
    attempts = {
        "cross_profile_evidence": lambda: graph.propose_rewrite(
            word, 0, graph.Rule.SYMMETRIC,
            graph.evidence_for(a.model.tensor_profile, graph.Rule.SYMMETRIC)),
        "Cl3_is_Mat2": lambda: cr.require_independent_images(pauli.cl3_images),
    }
    for name, attempt in attempts.items():
        try:
            attempt()
        except cr.Rejected as error:
            output["expected_negatives"][name] = str(error)
        else:
            raise AssertionError(f"expected rejection: {name}")
    print(json.dumps(output, indent=2, default=exact_json, ensure_ascii=False))


if __name__ == "__main__":
    main()
