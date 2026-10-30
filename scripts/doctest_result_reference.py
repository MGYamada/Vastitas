"""Reference result judgment for #236; no source checking or driver receipt minting.

Consumes the existing Diagnostic payload (code/message/span/notes). The surrounding
execution observations must eventually come from the ordinary driver, before it
renders errors. Supplied JSON is not authenticated evidence. Every output here is
reference_only and is ineligible for registry admission, even when status=passed.
"""

import argparse
from collections import Counter
import copy
import json
from pathlib import Path
import re


EXPECTATION_SCHEMA = "vastitas.doctest-expectation-reference/1"
RESULT_SCHEMA = "vastitas.doctest-result-reference/1"
REPORT_SCHEMA = "vastitas.doctest-report-reference/1"
POLICY = "expected-rejection/1"
_CODE = re.compile(r"E_[A-Z0-9_]+\Z")
_DIGEST = re.compile(r"[0-9a-f]{64}\Z")
_OUTCOMES = {"frontend_rejected", "kernel_rejected", "accepted",
             "infrastructure_failure", "interrupted", "not_run", "unsupported", "unknown"}
_NON_LANGUAGE_CODES = {
    "E_PROTOCOL", "E_BACKEND", "E_BUILD", "E_INPUT", "E_OUTPUT", "E_USAGE",
    "E_ARGUMENT", "E_INTERRUPTED", "E_CODEGEN", "E_LIMIT", "E_DISPATCH_LIMIT",
    "E_UNSUPPORTED",
}


class Invalid(ValueError):
    """Malformed/unsupported result data, never a Vastitas language judgment."""


def _require(condition, message):
    if not condition:
        raise Invalid(message)


def _fields(value, required, optional=""):
    required, optional = set(required.split()), set(optional.split())
    _require(type(value) is dict and required <= set(value) <= required | optional,
             f"expected fields: {sorted(required)}; optional: {sorted(optional)}")


def _text(value):
    _require(type(value) is str and bool(value.strip()), "expected nonempty text")


def _codes(values):
    _require(type(values) is list and bool(values), "expected a nonempty diagnostic list")
    for value in values:
        _require(type(value) is str and _CODE.fullmatch(value) is not None,
                 "expected an exact top-level diagnostic code")


def _binding(value):
    _fields(value, "invocation_id case_id package_revision input_sha256 "
                   "dependencies_sha256 toolchain_sha256 profile_sha256 policy")
    for key, part in value.items():
        _text(part)
        if key.endswith("_sha256"):
            _require(_DIGEST.fullmatch(part) is not None, "expected a lowercase SHA-256 digest")
    _require(value["policy"] == POLICY, "unsupported result policy")


def _span(value):
    _fields(value, "start end line column")
    _require(all(type(v) is int and v >= 0 for v in value.values()), "invalid span")
    _require(value["start"] <= value["end"], "reversed span")


def _diagnostic(value):
    # The original driver regression deliberately omits span. Do not manufacture
    # one, rewrite prose, flatten notes, or mint #238's occurrence/semantic IDs.
    _fields(value, "code message", "span notes")
    _codes([value["code"]])
    _require(type(value["message"]) is str, "invalid diagnostic message")
    if "span" in value:
        _span(value["span"])
    _require(type(value.get("notes", [])) is list, "invalid diagnostic notes")
    for note in value.get("notes", []):
        _fields(note, "message", "span")
        _require(type(note["message"]) is str, "invalid note message")
        if "span" in note:
            _span(note["span"])


def _validate(expectation, result):
    _fields(expectation, "schema binding match codes")
    _require(expectation["schema"] == EXPECTATION_SCHEMA, "unsupported expectation schema")
    _binding(expectation["binding"])
    _require(expectation["match"] == "exact_code_multiset", "unsupported diagnostic match rule")
    _codes(expectation["codes"])
    _fields(result, "schema binding path outcome integrity driver_exit_code backend diagnostics")
    _require(result["schema"] == RESULT_SCHEMA, "unsupported result schema")
    _binding(result["binding"])
    _text(result["path"])
    _require(type(result["outcome"]) is str and result["outcome"] in _OUTCOMES,
             "unsupported result outcome")
    _require(result["integrity"] in ("complete", "unknown"), "unsupported integrity state")
    _require(result["driver_exit_code"] is None or type(result["driver_exit_code"]) is int,
             "invalid driver exit code")
    backend = result["backend"]
    _fields(backend, "state request_version exit_code response")
    _require(backend["state"] in ("not_reached", "completed", "failed", "unknown"),
             "unsupported backend state")
    for key in ("request_version", "exit_code"):
        _require(backend[key] is None or type(backend[key]) is int, f"invalid backend {key}")
    _require(backend["response"] is None or type(backend["response"]) is dict,
             "invalid decoded backend response")
    _require(type(result["diagnostics"]) is list, "invalid diagnostics array")
    for diagnostic in result["diagnostics"]:
        _diagnostic(diagnostic)


def _decision(expectation, result):
    if expectation["binding"] != result["binding"]:
        return "failed", "binding_mismatch"
    if result["outcome"] == "not_run":
        return "skipped", "not_run"
    if result["outcome"] == "unsupported":
        return "unsupported", "unsupported"
    if result["path"] != "ordinary_vast_check":
        return "failed", "not_ordinary_driver_path"
    if result["integrity"] != "complete":
        return "failed", "integrity_unknown"
    outcome = result["outcome"]
    if outcome not in ("frontend_rejected", "kernel_rejected"):
        return "failed", outcome
    if result["driver_exit_code"] != 1:
        return "failed", "driver_termination_mismatch"
    backend = result["backend"]
    if outcome == "frontend_rejected":
        if backend != {"state": "not_reached", "request_version": None,
                       "exit_code": None, "response": None}:
            return "failed", "frontend_backend_inconsistent"
    else:
        if backend["state"] != "completed" or backend["exit_code"] != 1:
            return "failed", "backend_termination_mismatch"
        version = backend["request_version"]
        if version not in range(2, 9):
            return "failed", "unsupported_protocol"
        response = backend["response"]
        _fields(response, "version ok diagnostics")
        _require(type(response["version"]) is int and type(response["ok"]) is bool,
                 "invalid response version/ok types")
        if response["version"] != version:
            return "failed", "protocol_mismatch"
        if response["ok"] is not False:
            return "failed", "backend_not_rejected"
        _require(type(response["diagnostics"]) is list, "invalid response diagnostics")
        for diagnostic in response["diagnostics"]:
            _diagnostic(diagnostic)
        if response["diagnostics"] != result["diagnostics"]:
            return "failed", "diagnostic_payload_mismatch"
    if not result["diagnostics"]:
        return "failed", "missing_diagnostics"
    codes = [d["code"] for d in result["diagnostics"]]
    # These are defensive contradictions, not a code-to-outcome classifier.
    # The future emitter classifies control-flow causes before formatting.
    if any(code in _NON_LANGUAGE_CODES or code.startswith("E_INTERNAL") for code in codes):
        return "failed", "non_language_diagnostic"
    if Counter(codes) != Counter(expectation["codes"]):
        return "failed", "diagnostic_mismatch"
    return "passed", "expected_rejection"


def judge(expectation, result):
    """Judge only result observations; never compile or recheck a .vast program."""
    report = {"schema": REPORT_SCHEMA, "scope": "reference_only", "check": "doctest",
              "registry_eligible": False, "expectation": copy.deepcopy(expectation),
              "result": copy.deepcopy(result)}
    try:
        _validate(expectation, result)
        report["status"], report["reason"] = _decision(expectation, result)
        actual = Counter(d["code"] for d in result["diagnostics"])
        expected = Counter(expectation["codes"])
        report["missing_codes"] = sorted((expected - actual).elements())
        report["unexpected_codes"] = sorted((actual - expected).elements())
    except Invalid as error:
        report.update(status="failed", reason="invalid_contract", detail=str(error))
    return report


def load_json(text):
    """A receipt cannot silently use last-wins duplicate keys or NaN values."""
    def object_pairs(pairs):
        result = {}
        for key, value in pairs:
            _require(key not in result, f"duplicate JSON field: {key}")
            result[key] = value
        return result

    def nonfinite(value):
        raise Invalid(f"non-finite JSON value: {value}")

    def noninteger(value):
        raise Invalid(f"non-integer JSON number: {value}")

    return json.loads(text, object_pairs_hook=object_pairs, parse_constant=nonfinite,
                      parse_float=noninteger)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("expectation", type=Path)
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    try:
        report = judge(load_json(args.expectation.read_text(encoding="utf-8")),
                       load_json(args.result.read_text(encoding="utf-8")))
    except (OSError, UnicodeError, ValueError, RecursionError) as error:
        report = {"schema": REPORT_SCHEMA, "scope": "reference_only", "check": "doctest",
                  "registry_eligible": False, "status": "failed", "reason": "invalid_input",
                  "detail": str(error)}
    print(json.dumps(report, ensure_ascii=True, sort_keys=True, indent=2, allow_nan=False))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
