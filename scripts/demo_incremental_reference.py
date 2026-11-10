#!/usr/bin/env python3
"""Run a finite #339 edit history; no compiler, persistent cache or timing claim."""

from dataclasses import replace
import json

import incremental_reference as r


def main():
    owner = r.ModuleId("library-origin-A", "ops")
    user = r.ModuleId("application-origin", "main")
    quiet = r.ModuleId("application-origin", "unused")
    family = r.DeclId(owner, "f")
    metric_key = r.Key("Linear", ("HasMetric",))
    base = r.Method("base", family)
    linear = r.Method("linear", family, "Linear", body=11)
    metric = r.Method("metric", family, requires=("HasMetric",), body=22)
    repair = r.Method("repair", family, "Linear", ("HasMetric",), body=33)
    initial = r.Program((user.package,), (
        r.Package(owner.package, "library"),
        r.Package(user.package, "application", dependencies=(owner.package,)),
    ), (
        r.Module(owner, families=(r.Family("f"),), methods=(base,)),
        r.Module(user, imports=(owner,), calls=(r.Call(family, metric_key),)),
        r.Module(quiet),
    ))

    def with_methods(methods):
        return replace(initial, modules=(replace(initial.modules[0], methods=methods),)
                       + initial.modules[1:])

    refined = with_methods((base, linear))
    ambiguous = with_methods((base, linear, metric))
    repaired = with_methods((base, linear, metric, repair))
    local_edit = replace(repaired, modules=repaired.modules[:-1] +
                         (replace(repaired.modules[-1], body=7),))
    cache = None
    rows = []
    for label, program in (("cold", initial), ("warm", initial),
                           ("new winner", refined), ("ambiguity", ambiguous),
                           ("repair", repaired), ("unrelated body edit", local_edit)):
        run = r.incremental_build(program, cache)
        clean = r.clean_build(program)
        if r.canonical(run.observation) != r.canonical(clean.observation):
            raise AssertionError("cache transparency regression: " + label)
        unit = next(u for u in run.observation["units"] if u["module"] == user.token())
        rows.append({"step": label, "accepted": run.observation["accepted"],
                     "winner": unit["calls"][0]["selection"]["winner"],
                     "reused_candidates": len(run.trace["reused"]),
                     "invalidated_units": len(run.trace["invalidated"]),
                     "rechecked_units": len(run.trace["checked"]), "clean_equal": True})
        cache = run.cache
    print(json.dumps({"scope": "finite reference; every hit rechecked; no speedup claim",
                      "steps": rows}, indent=2))


if __name__ == "__main__":
    main()
