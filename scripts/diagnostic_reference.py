"""Presentation/identity reference for #230/#231/#233, never compiler acceptance.

Only synthetic, explicitly scoped reference occurrences have complete identities.
The current kernel-response adapter preserves rejection and leaves semantic roles
unresolved. There is deliberately no input flag that can certify a provenance
ledger; #229's independent reconstruction is still required.
"""

import copy
import hashlib
import json
import re


SCHEMA = "vastitas.diagnostic-reference/1"
PROFILE = "finite-scalar-join-reference/1"
SCALARS = ("Nat", "Int", "Bool", "Unit")
_ATOM = re.compile(r"[A-Za-z0-9_:.+@-]+\Z")


class Invalid(ValueError):
    """Unsupported or malformed reference data, not a language judgment."""


def _require(condition, message):
    if not condition:
        raise Invalid(message)


def _fields(value, names):
    _require(type(value) is dict and set(value) == set(names.split()),
             f"expected fields: {names}")


def _atom(value):
    _require(type(value) is str and _ATOM.fullmatch(value) is not None,
             "semantic IDs must be nonempty ASCII atoms, never display paths")


def _array(value):
    _require(type(value) is list, "expected a JSON array")


def _pin(value):
    _fields(value, "package revision")
    for part in value.values():
        _atom(part)


def _ref(value):
    _fields(value, "package revision declaration")
    for part in value.values():
        _atom(part)


def _span(value):
    _fields(value, "start end line column")
    _require(all(type(v) is int and v >= 0 for v in value.values()), "invalid span")
    _require(value["end"] >= value["start"], "reversed span")


def _diagnostic(value):
    _require(type(value) is dict, "expected a diagnostic")
    _require(set(value) in ({"code", "message", "span"},
                           {"code", "message", "span", "notes"}),
             "unsupported diagnostic fields; no asserted ledger is trusted")
    _atom(value["code"])
    _require(type(value["message"]) is str, "invalid message")
    _span(value["span"])
    _array(value.get("notes", []))
    for note in value.get("notes", []):
        _fields(note, "message span")
        _require(type(note["message"]) is str, "invalid note")
        _span(note["span"])


def _role(value, expected, reference):
    _fields(value, "role status basis subject")
    _require(type(value["role"]) is str and value["role"] in expected, "unsupported semantic role")
    # No producer of verified semantic roles exists in this reference. In
    # particular a JSON status/evidence string cannot supply the missing ledger.
    _require(value["status"] == "unresolved", "semantic role is not checker-verified")
    _require(value["basis"] == ("reference_fixture" if reference else "not_established"),
             "unsupported provenance basis")
    if reference:
        _ref(value["subject"])
    else:
        _require(value["subject"] is None, "legacy diagnostic establishes no subject")


def validate(record):
    _fields(record, "schema origin semantic presentation external_candidates")
    _require(record["schema"] == SCHEMA, "unsupported schema")
    reference = record["origin"] == "reference_fixture"
    _require(reference or record["origin"] == "kernel_response_only", "unsupported origin")
    s = record["semantic"]
    _fields(s, "code outcome phase obligation function assembly participants holder "
               "conflict_set witness_keys history environment")
    _atom(s["code"])
    _require(s["outcome"] == "rejected", "a diagnostic must preserve rejection")
    _fields(s["obligation"], "kind id status")
    _require(s["obligation"]["status"] == "unresolved", "obligation remains unresolved")
    for name in ("participants", "conflict_set", "witness_keys", "history"):
        _array(s[name])
    _role(s["holder"], {"current_obligation_holder"}, reference)
    for participant in s["participants"]:
        _role(participant, {"method_contributor", "function_authority"}, reference)

    if reference:
        _require(s["code"] == "E_DISPATCH_AMBIGUOUS" and s["phase"] == "assembly_completion"
                 and s["obligation"]["kind"] == "dispatch_unique", "unsupported reference profile")
        _atom(s["obligation"]["id"])
        _ref(s["function"])
        _ref(s["assembly"])
        env = s["environment"]
        _fields(env, "profile input_revision environment_revision compiler_revision "
                     "toolchain_revision dependencies dependency_edges")
        _require(env["profile"] == PROFILE, "unsupported identity profile")
        for name in ("input_revision", "environment_revision", "compiler_revision", "toolchain_revision"):
            _atom(env[name])
        _array(env["dependencies"])
        _array(env["dependency_edges"])
        for pin in env["dependencies"]:
            _pin(pin)
        pins = {(p["package"], p["revision"]) for p in env["dependencies"]}
        for edge in env["dependency_edges"]:
            _fields(edge, "from to")
            for pin in edge.values():
                _pin(pin)
                _require((pin["package"], pin["revision"]) in pins, "unpinned dependency edge")
        refs = [s["function"], s["assembly"], s["holder"]["subject"]]
        refs += [p["subject"] for p in s["participants"]]
        for ref in s["conflict_set"]:
            _ref(ref)
        refs += s["conflict_set"]
        contributors = {canonical_json(p["subject"]) for p in s["participants"]
                        if p["role"] == "method_contributor"}
        conflicts = {canonical_json(r) for r in s["conflict_set"]}
        _require(len(conflicts) >= 2 and conflicts <= contributors,
                 "every conflicting contribution must be represented")
        _require(bool(s["witness_keys"]), "reference ambiguity requires witness keys")
        for key in s["witness_keys"]:
            _array(key)
            _require(len(key) == 2 and all(type(k) is str and k in SCALARS for k in key),
                     "unsupported ordered scalar key")
        for event in s["history"]:
            _fields(event, "op subject loan")
            _require(type(event["op"]) is str and event["op"] in {
                "borrow", "apply", "return", "seal", "reborrow", "transfer"},
                     "unsupported history event")
            _ref(event["subject"])
            refs.append(event["subject"])
            if event["loan"] is not None:
                _atom(event["loan"])
        for ref in refs:
            _require((ref["package"], ref["revision"]) in pins, "semantic reference is not pinned")
    else:
        _require(s["phase"] == "unresolved" and s["obligation"] == {
            "kind": "unresolved", "id": None, "status": "unresolved"},
            "cannot reconstruct an obligation from diagnostic prose")
        _require(all(s[k] is None for k in ("function", "assembly", "environment"))
                 and all(s[k] == [] for k in ("participants", "conflict_set", "witness_keys", "history")),
                 "legacy diagnostics do not establish a semantic ledger")

    p = record["presentation"]
    _fields(p, "diagnostic source_path next_action")
    _diagnostic(p["diagnostic"])
    _require(p["diagnostic"]["code"] == s["code"], "conflicting diagnostic codes")
    _require(all(type(p[k]) is str for k in ("source_path", "next_action")), "invalid display text")
    _array(record["external_candidates"])
    for hint in record["external_candidates"]:
        _fields(hint, "role status basis hint")
        _require(hint["status"] == "candidate" and hint["basis"] == "external_heuristic",
                 "external hints must remain candidate")
        _require(type(hint["role"]) is str and type(hint["hint"]) is str, "invalid external hint")


def canonical_json(value):
    """Encoding v1: ASCII JSON, sorted object keys, compact separators.

    Array order is NEVER changed here. Set normalization is field-specific below.
    The validated semantic profile has ASCII atoms and no floating-point fields;
    display Unicode is excluded from identity.
    """
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"),
                      allow_nan=False).encode("ascii")


def _set(values):
    unique = {canonical_json(value): value for value in values}
    return [unique[key] for key in sorted(unique)]


def canonical_occurrence(record):
    """Complete synthetic identity bytes, or None when the ledger is unavailable."""
    validate(record)
    if record["origin"] != "reference_fixture":
        return None
    s = copy.deepcopy(record["semantic"])
    for name in ("participants", "conflict_set", "witness_keys"):
        s[name] = _set(s[name])
    for name in ("dependencies", "dependency_edges"):
        s["environment"][name] = _set(s["environment"][name])
    # Keep history order AND multiplicity, as well as argument positions in keys.
    return canonical_json({"schema": SCHEMA, "origin": record["origin"], "semantic": s})


def _fingerprint(prefix, encoded):
    return prefix + hashlib.sha256(encoded).hexdigest()


def identities(record):
    encoded = canonical_occurrence(record)
    if encoded is None:
        return {"coverage": "unresolved: checker ledger unavailable",
                "diagnostic_occurrence_id": None, "reference_occurrence_id": None,
                "semantic_issue_key": None, "grouping_is_advisory": True}
    s = record["semantic"]

    def nominal(ref):
        return {"package": ref["package"], "declaration": ref["declaration"]}

    group = {"grouping_schema": "vastitas.reference-issue/1", "profile": PROFILE,
             "code": s["code"], "obligation_kind": s["obligation"]["kind"],
             "function": nominal(s["function"]),
             "conflict_set": _set([nominal(ref) for ref in s["conflict_set"]])}
    return {"coverage": "reference_fixture_only", "diagnostic_occurrence_id": None,
            "reference_occurrence_id": _fingerprint("vastitas-reference-occurrence-v1:", encoded),
            "semantic_issue_key": _fingerprint("vastitas-reference-issue-v1:", canonical_json(group)),
            "grouping_is_advisory": True}


def machine_report(record):
    """The same record feeds both projections. No report is a certificate."""
    return {"record": copy.deepcopy(record), "identity": identities(record)}


def _location(ref):
    if ref is None:
        return "unresolved"
    return f"{ref['package']}@{ref['revision']}::{ref['declaration']}"


def render(record):
    report = machine_report(record)
    s, p, ids = record["semantic"], record["presentation"], report["identity"]
    lines = [f"{s['code']}: unresolved mathematical obligation",
             f"Outcome: {s['outcome']}; phase: {s['phase']}",
             f"Obligation: {s['obligation']['kind']} ({s['obligation']['id'] or 'unresolved'})",
             f"Identity coverage: {ids['coverage']}"]
    if record["origin"] == "reference_fixture":
        lines.append("All locations below are reference identities; checker provenance is unresolved.")
    lines.append("Involved semantic contributions and authority:")
    for item in _set(s["participants"]):
        lines.append(f"  {item['role']}: {_location(item['subject'])} [{item['status']}]")
    if not s["participants"]:
        lines.append("  unresolved")
    lines.append(f"Current obligation location: {_location(s['holder']['subject'])} [unresolved]")
    if s["conflict_set"]:
        lines.append("Conflicting contributions: " + ", ".join(
            _location(ref) for ref in _set(s["conflict_set"])))
        lines.append("Overlap keys: " + ", ".join("(" + ", ".join(key) + ")"
                                                  for key in _set(s["witness_keys"])))
    if s["history"]:
        lines.append("Recorded history (order retained; reference only):")
        for event in s["history"]:
            lines.append(f"  {event['op']} {_location(event['subject'])} loan={event['loan']}")
    lines.append("Diagnostic: " + p["diagnostic"]["message"])
    span = p["diagnostic"]["span"]
    lines.append(f"Location: {p['source_path'] or '(not supplied)'}:{span['line']}:{span['column']}")
    for note in p["diagnostic"].get("notes", []):
        lines.append(f"Note ({note['span']['line']}:{note['span']['column']}): {note['message']}")
    lines.append("Next verification action: " + p["next_action"])
    if record["external_candidates"]:
        lines.append(f"External context: {len(record['external_candidates'])} candidate hint(s); "
                     "unverified details remain in JSON and do not establish semantic roles.")
    lines.append("Reference exact occurrence: " + (ids["reference_occurrence_id"] or "unresolved"))
    lines.append("Advisory grouping key: " + (ids["semantic_issue_key"] or "unresolved"))
    lines.append("Equal grouping keys do not establish the same bug or a unique cause.")
    return "\n".join(lines)


def from_kernel_response(response, expected_version):
    """Import the existing failure envelope, not a ledger or an attestation.

    A saved response may itself be untrusted. This adapter makes no verified
    semantic-role claims and never derives identities from prose, spans or paths.
    All diagnostics/notes survive; successful responses cannot become failures.
    """
    _fields(response, "version ok diagnostics")
    _require(type(expected_version) is int and expected_version in range(2, 8),
             "unsupported expected wire version")
    _require(type(response["version"]) is int and response["version"] == expected_version,
             "wire version mismatch")
    _require(response["ok"] is False, "expected the actual rejected outcome")
    _array(response["diagnostics"])
    _require(bool(response["diagnostics"]), "failure must contain diagnostics")
    records = []
    for diagnostic in response["diagnostics"]:
        _diagnostic(diagnostic)
        record = {"schema": SCHEMA, "origin": "kernel_response_only", "semantic": {
            "code": diagnostic["code"], "outcome": "rejected", "phase": "unresolved",
            "obligation": {"kind": "unresolved", "id": None, "status": "unresolved"},
            "function": None, "assembly": None, "participants": [],
            "holder": {"role": "current_obligation_holder", "status": "unresolved",
                       "basis": "not_established", "subject": None},
            "conflict_set": [], "witness_keys": [], "history": [], "environment": None},
            "presentation": {"diagnostic": copy.deepcopy(diagnostic), "source_path": "",
                             "next_action": "Inspect the original diagnostic; #229's checked "
                                            "failure ledger is required to locate the obligation."},
            "external_candidates": []}
        validate(record)
        records.append(record)
    return records


def load_json(text):
    """Reject ambiguous duplicate object keys instead of accepting last-wins JSON."""
    def object_pairs(pairs):
        result = {}
        for key, value in pairs:
            _require(key not in result, f"duplicate JSON field: {key}")
            result[key] = value
        return result

    def nonfinite(value):
        raise Invalid(f"non-finite JSON value: {value}")

    return json.loads(text, object_pairs_hook=object_pairs, parse_constant=nonfinite)
