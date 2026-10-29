"""Ten synthetic receipt cases; no Vastitas or Lean execution is performed."""

import argparse
import copy
import hashlib
import json
from pathlib import Path

import doctest_result_reference as ref


FIXTURE = Path(__file__).resolve().parents[1] / "tests/fixtures/doctest/mismatched-failure-v3.json"


def example():
    """Explicit fixture bindings; these hashes are NOT observed toolchain pins."""
    binding = {"invocation_id": "fixture:run-1", "case_id": "fixture:docs#reject-1",
               "package_revision": "fixture:package@revision-1", "policy": ref.POLICY}
    for key in ("input", "dependencies", "toolchain", "profile"):
        binding[key + "_sha256"] = hashlib.sha256(("fixture:" + key).encode()).hexdigest()
    expectation = {"schema": ref.EXPECTATION_SCHEMA, "binding": binding,
                   "match": "exact_code_multiset", "codes": ["E_NAME"]}
    diagnostic = {"code": "E_NAME", "message": "unknown variable missing",
                  "span": {"start": 19, "end": 26, "line": 1, "column": 20}, "notes": []}
    result = {"schema": ref.RESULT_SCHEMA, "binding": copy.deepcopy(binding),
              "path": "ordinary_vast_check", "outcome": "kernel_rejected",
              "integrity": "complete", "driver_exit_code": 1,
              "backend": {"state": "completed", "request_version": 2, "exit_code": 1,
                          "response": {"version": 2, "ok": False, "diagnostics": [diagnostic]}},
              "diagnostics": [copy.deepcopy(diagnostic)]}
    return expectation, result


def cases():
    expectation, kernel = example()
    frontend = copy.deepcopy(kernel)
    frontend.update(outcome="frontend_rejected", backend={
        "state": "not_reached", "request_version": None, "exit_code": None, "response": None})
    yield "frontend_rejection", expectation, frontend
    yield "kernel_rejection", expectation, kernel
    mismatch = copy.deepcopy(kernel)
    mismatch["backend"]["response"] = ref.load_json(FIXTURE.read_text(encoding="utf-8"))
    mismatch["diagnostics"] = copy.deepcopy(mismatch["backend"]["response"]["diagnostics"])
    sentinel = copy.deepcopy(expectation)
    sentinel["codes"] = ["E_SENTINEL"]
    yield "version_2_request_version_3_failure", sentinel, mismatch
    unknown = copy.deepcopy(kernel)
    unknown["integrity"] = "unknown"
    yield "unknown_integrity", expectation, unknown
    for outcome in ("infrastructure_failure", "interrupted"):
        result = copy.deepcopy(kernel)
        result.update(outcome=outcome, driver_exit_code=None)
        result["backend"].update(state="failed", exit_code=None)
        yield outcome, expectation, result
    for name, codes in (("wrong_diagnostic", ["E_TYPE"]),
                        ("extra_diagnostic", ["E_NAME", "E_TYPE"])):
        result = copy.deepcopy(kernel)
        result["diagnostics"] = [{"code": code, "message": "fixture diagnostic"} for code in codes]
        result["backend"]["response"]["diagnostics"] = copy.deepcopy(result["diagnostics"])
        yield name, expectation, result
    accepted = copy.deepcopy(kernel)
    accepted.update(outcome="accepted", driver_exit_code=0, diagnostics=[])
    accepted["backend"].update(exit_code=0, response={"version": 2, "ok": True})
    yield "accepted", expectation, accepted
    not_run = copy.deepcopy(frontend)
    not_run.update(outcome="not_run", integrity="unknown", driver_exit_code=None, diagnostics=[])
    yield "not_run", expectation, not_run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    reports = [{"case": name, **ref.judge(expected, result)} for name, expected, result in cases()]
    if args.json:
        print(json.dumps(reports, sort_keys=True, indent=2))
    else:
        print("Reference observations only; registry_eligible=false in every case.")
        for report in reports:
            print(f"{report['case']}: {report['status']} ({report['reason']})")


if __name__ == "__main__":
    main()
