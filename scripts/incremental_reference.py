"""Finite dependency-invalidation reference for #339, outside the compiler.

Cache entries are untrusted JSON-shaped candidates. Every hit undergoes a full
finite semantic recheck from current inputs; hashes/receipts never grant
acceptance. This models candidate reuse, NOT saved checker work or Lean proofs.
See docs/incremental-reference.md for the deliberately small source language.
"""

from copy import deepcopy
from dataclasses import asdict, dataclass
from hashlib import sha256
import json


SCHEMA = "vastitas.incremental-reference/1"


def canonical(value):
    """Typed JSON equality: in particular, True must not compare equal to 1."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def digest(value):
    return sha256(canonical(value).encode()).hexdigest()


def wire(value):
    return json.loads(canonical(asdict(value)))


@dataclass(frozen=True, order=True)
class ModuleId:
    package: str  # Nominal source identity, NOT a package display name/version.
    path: str

    def token(self):
        return canonical([self.package, self.path])


@dataclass(frozen=True, order=True)
class DeclId:
    module: ModuleId
    name: str

    def token(self):
        return canonical([self.module.package, self.module.path, self.name])


@dataclass(frozen=True, order=True)
class Key:
    nominal: str
    capabilities: tuple = ()


KEYS = tuple(Key(n, c) for n in ("Linear", "Scalar")
             for c in ((), ("HasMetric",)))


@dataclass(frozen=True)
class Package:
    identity: str
    name: str
    version: str = "1"
    dependencies: tuple = ()
    manifest_revision: str = "1"


@dataclass(frozen=True)
class Family:
    name: str
    domain: tuple = KEYS


@dataclass(frozen=True)
class Method:
    name: str
    family: DeclId
    selector: str = "Any"
    requires: tuple = ()
    result: str = "Int"
    body: object = 0  # Only Int/Bool literal bodies belong to this tiny profile.


@dataclass(frozen=True)
class Use:
    target: ModuleId
    expected: str = "Int"


@dataclass(frozen=True)
class Call:
    family: DeclId
    key: Key
    expected: str = "Int"


@dataclass(frozen=True)
class Module:
    identity: ModuleId
    imports: tuple = ()  # Transitive visibility in this reference only.
    interface: str = "Int"
    body: object = 0
    uses: tuple = ()
    families: tuple = ()
    methods: tuple = ()
    calls: tuple = ()


@dataclass(frozen=True)
class Grant:
    family: DeclId
    issuer: ModuleId
    grantee: ModuleId
    region: tuple = KEYS


@dataclass(frozen=True)
class Assembly:
    revision: str = "1"
    applied: tuple = ()  # External method identities; owner methods are active.
    grants: tuple = ()


@dataclass(frozen=True)
class Program:
    roots: tuple  # Package identities. Audit ALL modules in their dependency closure.
    packages: tuple
    modules: tuple
    assembly: Assembly = Assembly()
    compiler: str = "reference-compiler/1"


@dataclass
class Run:
    observation: dict
    cache: dict
    trace: dict


def literal_type(value):
    return {int: "Int", bool: "Bool"}.get(type(value), "Invalid")


def applicable(method, key):
    return (method.selector in ("Any", key.nominal)
            and set(method.requires) <= set(key.capabilities))


def more_specific(left, right):
    nominal = left.selector == right.selector or right.selector == "Any"
    caps = set(left.requires) >= set(right.requires)
    strict = (left.selector != right.selector
              or set(left.requires) != set(right.requires))
    return nominal and caps and strict


def _order(graph):
    """Dependencies first, deterministic, with explicit cycle rejection."""
    pending, done, ordered = set(graph), set(), []
    while pending:
        ready = sorted(n for n in pending if set(graph[n]) <= done)
        if not ready:
            return None
        ordered.extend(ready)
        done.update(ready)
        pending.difference_update(ready)
    return ordered


def _prepare(program):
    errors = []
    packages = {p.identity: p for p in program.packages}
    if len(packages) != len(program.packages):
        errors.append("E_DUPLICATE_PACKAGE")
    selected, pending = set(), set(program.roots)
    while pending:
        identity = min(pending)
        pending.remove(identity)
        if identity in selected:
            continue
        selected.add(identity)
        if identity not in packages:
            errors.append("E_MISSING_PACKAGE:" + identity)
        else:
            pending.update(set(packages[identity].dependencies) - selected)
    if errors:
        return {}, {}, [], errors
    packages = {i: packages[i] for i in sorted(selected)}
    if _order({i: p.dependencies for i, p in packages.items()}) is None:
        errors.append("E_PACKAGE_CYCLE")
    source = [m for m in program.modules if m.identity.package in selected]
    modules = {m.identity.token(): m for m in source}
    if len(modules) != len(source):
        errors.append("E_DUPLICATE_MODULE")
    for token, module in modules.items():
        for dep in module.imports:
            if dep.token() not in modules:
                errors.append("E_MISSING_IMPORT:" + token + ":" + dep.token())
            if (dep.package != module.identity.package and dep.package not in
                    packages[module.identity.package].dependencies):
                errors.append("E_PACKAGE_IMPORT:" + token + ":" + dep.token())
        names = [f.name for f in module.families] + [m.name for m in module.methods]
        if len(set(names)) != len(names):
            errors.append("E_DUPLICATE_DECL:" + token)
        for family in module.families:
            if any(k not in KEYS for k in family.domain):
                errors.append("E_UNSUPPORTED_DOMAIN:" + token)
        for method in module.methods:
            if (method.selector not in ("Any", "Linear", "Scalar")
                    or method.requires not in ((), ("HasMetric",))):
                errors.append("E_UNSUPPORTED_SIGNATURE:" + token)
        if any(c.key not in KEYS for c in module.calls):
            errors.append("E_UNSUPPORTED_KEY:" + token)
    graph = {t: [d.token() for d in m.imports] for t, m in modules.items()}
    order = _order(graph) if not errors else None
    if not errors and order is None:
        errors.append("E_MODULE_CYCLE")
    return packages, modules, order or [], sorted(set(errors))


def _environment(program, modules):
    """Reconstruct the complete finite family environment from CURRENT sources."""
    families = {DeclId(m.identity, f.name): f for m in modules.values()
                for f in m.families}
    methods = {DeclId(m.identity, f.name): f for m in modules.values()
               for f in m.methods}
    applied = set(program.assembly.applied)
    global_errors = []
    for identity in sorted(applied - methods.keys()):
        global_errors.append("E_MISSING_CONTRIBUTION:" + identity.token())
    grants = program.assembly.grants
    for grant in grants:
        if (grant.family not in families or grant.issuer != grant.family.module
                or grant.grantee.token() not in modules
                or any(key not in KEYS for key in grant.region)):
            global_errors.append("E_GRANT:" + grant.family.token())
    views = {}
    for identity, family in sorted(families.items()):
        candidates = [(i, m) for i, m in sorted(methods.items())
                      if m.family == identity and (i.module == identity.module or i in applied)]
        errors, rows = [], []
        signatures = [(m.selector, m.requires) for _, m in candidates]
        if len(set(signatures)) != len(signatures):
            errors.append("E_DUPLICATE_SIGNATURE:" + identity.token())
        for mid, _ in candidates:
            if mid.module != identity.module and not any(
                    g.family == identity and g.issuer == identity.module
                    and g.grantee == mid.module for g in grants):
                errors.append("E_NO_GRANT:" + mid.token())
        for key in KEYS:  # Whole key space, including keys outside declared domain.
            matches = [(i, m) for i, m in candidates if applicable(m, key)]
            best = [(i, m) for i, m in matches
                    if not any(more_specific(other, m) for _, other in matches)]
            witness = canonical(wire(key))
            if len(best) > 1:
                errors.append("E_AMBIGUOUS:" + witness)
            if not best and key in family.domain:
                errors.append("E_COVERAGE:" + witness)
            for mid, _ in best:
                if mid.module != identity.module and not any(
                        g.family == identity and g.issuer == identity.module
                        and g.grantee == mid.module and key in g.region for g in grants):
                    errors.append("E_IMPACT:" + mid.token() + ":" + witness)
            winner = best[0] if len(best) == 1 else None
            rows.append({"key": wire(key), "best": [i.token() for i, _ in best],
                         "winner": winner[0].token() if winner else None,
                         "result": winner[1].result if winner else None,
                         "body": winner[1].body if winner else None})
        views[identity] = {"identity": identity.token(), "dispatch": rows,
                           "diagnostics": sorted(set(errors))}
    return views, sorted(set(global_errors))


def _visible(token, modules):
    found, pending = set(), {token}
    while pending:
        item = pending.pop()
        if item not in found:
            found.add(item)
            pending.update(d.token() for d in modules[item].imports)
    return found


def _check_unit(module, modules, views, dependencies):
    """Finite semantic rederivation. No cache data can enter this function."""
    errors, bindings, uses = [], [], []
    visible = _visible(module.identity.token(), modules)
    if module.interface not in ("Int", "Bool") or literal_type(module.body) != module.interface:
        errors.append("E_BODY")
    if any(not result["accepted"] for result in dependencies.values()):
        errors.append("E_DEPENDENCY")
    for use in module.uses:
        actual = modules[use.target.token()].interface if use.target.token() in visible else None
        uses.append({"target": use.target.token(), "expected": use.expected, "actual": actual})
        if actual != use.expected:
            errors.append("E_INTERFACE:" + use.target.token())
    # All methods, including losers, out-of-domain and unapplied contributions.
    for method in module.methods:
        mid = DeclId(module.identity, method.name).token()
        if method.result not in ("Int", "Bool") or literal_type(method.body) != method.result:
            errors.append("E_METHOD_BODY:" + mid)
        if method.family not in views or method.family.module.token() not in visible:
            errors.append("E_METHOD_FAMILY:" + mid)
    for call in module.calls:
        view = views.get(call.family)
        if view is None or call.family.module.token() not in visible:
            errors.append("E_CALL_SCOPE:" + call.family.token())
            bindings.append({"family": call.family.token(), "key": wire(call.key), "selection": None})
            continue
        row = next(row for row in view["dispatch"] if row["key"] == wire(call.key))
        bindings.append({"family": call.family.token(), "key": wire(call.key), "selection": row})
        if view["diagnostics"]:
            errors.append("E_FAMILY:" + call.family.token())
        if row["winner"] is None or row["result"] != call.expected:
            errors.append("E_CALL:" + call.family.token())
    owned = [view for identity, view in sorted(views.items()) if identity.module == module.identity]
    for view in owned:
        errors.extend(view["diagnostics"])
    return {"module": module.identity.token(), "accepted": not errors,
            "diagnostics": sorted(set(errors)), "interface": module.interface,
            "body": {"type": literal_type(module.body), "literal": module.body},
            "imports": sorted(d.token() for d in module.imports), "uses": uses,
            "methods": [wire(m) for m in module.methods], "families": owned, "calls": bindings}


def _snapshot(program, packages, modules):
    return {"compiler": program.compiler, "packages": [wire(p) for p in packages.values()],
            "assembly": wire(program.assembly),
            "environment": [{"module": t, "families": [wire(f) for f in m.families],
                             "methods": [wire(f) for f in m.methods]}
                            for t, m in sorted(modules.items())],
            "modules": {t: {"source": wire(m), "imports": sorted(d.token() for d in m.imports)}
                        for t, m in sorted(modules.items())}}


def _valid_snapshot(value):
    if type(value) is not dict or set(value) != {
            "compiler", "packages", "assembly", "environment", "modules"}:
        return False
    if type(value["modules"]) is not dict:
        return False
    for token, row in value["modules"].items():
        if (type(token) is not str or type(row) is not dict
                or set(row) != {"source", "imports"} or type(row["source"]) is not dict
                or type(row["imports"]) is not list
                or any(type(d) is not str for d in row["imports"])):
            return False
    return True


def invalidation(current, previous):
    """An optimization plan, never trusted evidence. Use old AND new edges."""
    all_units = set(current["modules"])
    if not _valid_snapshot(previous):
        return all_units, "missing-or-malformed-snapshot"
    if any(canonical(current[field]) != canonical(previous[field]) for field in
           ("compiler", "packages", "assembly", "environment")):
        return all_units, "package-compiler-or-assembly-closure"
    old, new = previous["modules"], current["modules"]
    if old.keys() != new.keys():
        return all_units, "module-set-closure"
    dirty = {t for t in new if canonical(old[t]) != canonical(new[t])}
    while True:
        expanded = dirty | {t for t in new if
                            (set(old[t]["imports"]) | set(new[t]["imports"])) & dirty}
        if expanded == dirty:
            return dirty, "reverse-import-closure" if dirty else "unchanged"
        dirty = expanded


def _receipt(context, candidate):
    # Corruption detection only. Even a fully rehashed forgery must be rechecked.
    return {"kind": "finite-recheck-required", "context_sha256": digest(context),
            "candidate_sha256": digest(candidate)}


def _entry(context, candidate):
    return deepcopy({"context": context, "candidate": candidate,
                     "evidence": _receipt(context, candidate)})


def _recheck(entry, context, expected):
    if type(entry) is not dict or set(entry) != {"context", "candidate", "evidence"}:
        return False
    return (canonical(entry["context"]) == canonical(context)
            and canonical(entry["evidence"]) == canonical(_receipt(context, entry["candidate"]))
            and canonical(entry["candidate"]) == canonical(expected))


def _cache_or_empty(cache):
    try:
        # Copy through JSON: no Python object/pickle execution or mutable aliasing.
        cache = json.loads(canonical(cache))
        if (type(cache) is dict and set(cache) == {"schema", "snapshot", "entries"}
                and cache["schema"] == SCHEMA and type(cache["entries"]) is dict):
            return cache
    except (TypeError, ValueError, RecursionError):
        pass
    return {"schema": SCHEMA, "snapshot": None, "entries": {}}


def _run(program, cache, *, clean):
    packages, modules, order, errors = _prepare(program)
    empty = {"schema": SCHEMA, "snapshot": None, "entries": {}}
    trace = {"invalidated": [], "reused": [], "recomputed": [], "fallback": [], "checked": []}
    if errors:
        trace["reason"] = "invalid-input-graph"
        return Run({"accepted": False, "diagnostics": errors, "units": []}, empty, trace)
    snapshot = _snapshot(program, packages, modules)
    prior = _cache_or_empty(None if clean else cache)
    dirty, reason = invalidation(snapshot, prior["snapshot"])
    trace.update(invalidated=sorted(dirty), reason="clean" if clean else reason)
    views, errors = _environment(program, modules)
    results, entries = {}, {}
    for token in order:
        module = modules[token]
        deps = {d.token(): results[d.token()] for d in module.imports}
        context = {k: v for k, v in snapshot.items() if k != "modules"}
        context.update(source=wire(module), dependencies=deps)
        # Always reconstruct acceptance, diagnostics and selected structure from
        # CURRENT inputs. Candidate reuse never skips this finite model check.
        expected = _check_unit(module, modules, views, deps)
        trace["checked"].append(token)
        entry = prior["entries"].get(token)
        if token not in dirty and _recheck(entry, context, expected):
            results[token] = deepcopy(entry["candidate"])
            trace["reused"].append(token)
        else:
            results[token] = expected
            trace["recomputed"].append(token)
            if token not in dirty and entry is not None:
                trace["fallback"].append(token)
        entries[token] = _entry(context, results[token])
    units = [results[t] for t in sorted(results)]
    diagnostics = sorted(set(errors + [u["module"] + ":" + e for u in units for e in u["diagnostics"]]))
    observation = {"accepted": not diagnostics, "diagnostics": diagnostics, "units": units}
    return Run(observation, {"schema": SCHEMA, "snapshot": snapshot, "entries": entries}, trace)


def clean_build(program):
    return _run(program, None, clean=True)


def incremental_build(program, cache=None):
    return _run(program, cache, clean=False)
