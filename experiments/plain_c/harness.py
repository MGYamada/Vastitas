"""Three-arm measurements with a standalone, uninstrumented plain-C comparator.

Existing arena counters remain in the generated and arena-C paths. Plain-C cost
counters are compiled only into a separate diagnostic executable, never the
executable admitted to timing. Historical two-arm records are not rewritten.
"""
from __future__ import annotations

import csv
import hashlib
import itertools
import json
from pathlib import Path
import random
import re
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "scripts"))
from native_sanitizers import FLAGS as SANITIZERS

PROFILES = {"public_gemm": (0, 3, 3), "tensor_packing": (1, 4, 4),
            "contraction_trees": (2, 6, 6)}
IMPLEMENTATIONS = ("generated", "arena_c", "plain_c")
ORDERS = tuple(itertools.permutations(IMPLEMENTATIONS))
PAYLOAD = {"repetitions", "checksum", "observed"}
TIMING_FIELDS = PAYLOAD | {"elapsed_ns", "process_maxrss_kib", "cost_instrumentation"}
COST_FIELDS = {"data_allocations", "data_frees", "live_bytes_after", "peak_data_bytes",
               "written_bytes", "copied_bytes", "metadata_allocations", "peak_metadata_bytes",
               "timed_data_allocations", "timed_data_frees", "timed_written_bytes",
               "timed_copied_bytes", "timed_metadata_allocations"}
METADATA_COSTS = {"metadata_allocations", "peak_metadata_bytes", "timed_metadata_allocations"}
ROW_FIELDS = {"case", "scope", "phase", "pair", "order", "implementation"}
CALL_FIELDS = {"blas_calls_timed", "pack_calls_timed", "selected_pack_calls_timed"}


def compare_payload(reference, plain):
    for key in PAYLOAD:
        if key not in reference or key not in plain or reference[key] != plain[key]:
            raise ValueError(f"plain-C output contract differs: {key}")


def check_plain_record(record, diagnostic):
    expected = TIMING_FIELDS | (COST_FIELDS if diagnostic else set())
    if set(record) != expected or record.get("cost_instrumentation") is not diagnostic:
        raise ValueError("unexpected plain-C schema or timing/accounting mode")
    for key in expected - {"checksum", "observed", "cost_instrumentation"}:
        if type(record[key]) is not int or record[key] < 0:
            raise ValueError(f"invalid plain-C integer field: {key}")
    if not 1 <= record["repetitions"] <= 1_000_000:
        raise ValueError("invalid plain-C repetition count")
    for key in ("checksum", "observed"):
        if not isinstance(record[key], str) or not re.fullmatch(r"[0-9a-f]{16}", record[key]):
            raise ValueError(f"invalid plain-C bit checksum: {key}")


def compare_diagnostic(reference, plain):
    check_plain_record(plain, True)
    compare_payload(reference, plain)
    for key in COST_FIELDS:
        want = 0 if key in METADATA_COSTS else reference[key]
        if plain[key] != want:
            raise ValueError(f"plain-C diagnostic cost differs: {key}")


def native_test(runner, case, header, profile, work, prefix, cc, arena_rows,
                *, sanitize=False, no_lsan=False):
    """Build independent timing/diagnostic binaries and verify their actual work."""
    number, buffers, scopes = PROFILES[profile]
    work.mkdir(parents=True, exist_ok=False)
    (work / "case.h").write_text(header(case, "PlainLayout"))
    flags = ["-std=c11", "-O3", "-fno-lto", "-Wall", "-Wextra", "-Werror"]
    if sanitize:
        flags[1:2] = ["-O1", "-g", *SANITIZERS]
        if sys.platform.startswith("linux"):
            flags += ["-fno-pie", "-no-pie"]
    env = dict(runner.env)
    if no_lsan:
        env["ASAN_OPTIONS"] = env.get("ASAN_OPTIONS", "") + ":detect_leaks=0"
    results = {}
    for diagnostic in (False, True):
        executable = work / ("diagnostic" if diagnostic else "timing")
        definitions = [f"-DBENCH_PROFILE={number}"] + (["-DBENCH_COSTS"] if diagnostic else [])
        command = [*cc, *flags, *definitions, "-I", work, "-I", ROOT / "experiments" / profile,
                   "-I", prefix / "include", HERE / "probe.c", prefix / "lib/libopenblas.a",
                   "-lm", "-lpthread", "-o", executable]
        runner.run(command, phase="plain_c_native_compile")
        symbols = work / ("diagnostic-symbols.txt" if diagnostic else "timing-symbols.txt")
        runner.run(["nm", executable], stdout_path=symbols, phase="plain_c_link_audit")
        if re.search(r"\b_?(?:vstorage_|vgemm_|lean_)[A-Za-z0-9_]*", symbols.read_text()):
            raise ValueError("standalone C comparator contains Vastitas/Lean symbols")
        result = runner.run([executable, "self-test"], env=env,
                            phase="plain_c_sanitizer" if sanitize else "plain_c_correctness")
        if "runtime error:" in result["stderr"] or "ERROR: AddressSanitizer" in result["stderr"]:
            raise ValueError("sanitizer reported an error despite successful exit")
        rows = [json.loads(line) for line in result["stdout"].splitlines()]
        if len(rows) != scopes or len(arena_rows) != 2 * scopes:
            raise ValueError("missing standalone C/arena validation rows")
        for scope, row in enumerate(rows):
            check_plain_record(row, diagnostic)
            compare_payload(arena_rows[2 * scope], row)
            if diagnostic:
                compare_diagnostic(arena_rows[2 * scope], row)
            else:
                # Neither stats storage nor failure-injection branches belong
                # in the timing build. The compiled record confirms the mode.
                if COST_FIELDS.intersection(row):
                    raise ValueError("accounting leaked into the timing executable")
        results["diagnostic" if diagnostic else "timing"] = {
            "rows": rows, "sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
            "executable": str(executable), "flags": flags + definitions,
        }
    failures = []
    if case["case"].startswith("tiny-") and case["pad"]:
        for allocation in range(1, buffers + 1):
            result = runner.run([work / "diagnostic", "0", "1", "1", str(allocation)],
                                env=env, required=False, phase="plain_c_failure_cleanup")
            expected = {"failure": "allocation", "allocated": allocation - 1,
                        "freed": allocation - 1, "live_bytes": 0}
            if result["returncode"] != 3 or json.loads(result["stdout"]) != expected:
                raise ValueError("plain-C partial-allocation cleanup failed")
            if "ERROR:" in result["stderr"] or "runtime error:" in result["stderr"]:
                raise ValueError("sanitizer failure during allocation cleanup")
            failures.append(expected)
    return {"case": case["case"], "implementation": "plain_c", "profile": profile,
            "status": "passed", "sanitizer": sanitize, "variants": results,
            "allocation_failure_checks": failures, "runtime_symbols": "absent"}


def order_for(index, phase, group):
    offset = {"verification": 0, "warmup": 2, "calibration": 4, "measurement": 0}[phase]
    return ORDERS[(index + offset + group) % len(ORDERS)]


def measure(runner, case, generated, plain, samples, target_ms, rows, raw, index,
            scopes, compare_arena):
    def group(scope, phase, group_id, reps, verify=False):
        found = {}
        order = order_for(index, phase, group_id)
        for implementation in order:
            command = ([plain, scope, reps, int(verify)] if implementation == "plain_c" else
                       [generated, "c" if implementation == "arena_c" else "generated",
                        scope, reps, int(verify)])
            result = runner.run(command, phase="runtime_validation" if verify else phase)
            found[implementation] = json.loads(result["stdout"])
        compare_arena(found["generated"], found["arena_c"])
        check_plain_record(found["plain_c"], False)
        compare_payload(found["generated"], found["plain_c"])
        if not verify:
            fields = list(found["generated"]) + ["cost_instrumentation"]
            for position, implementation in enumerate(order):
                record = {key: found[implementation].get(key) for key in fields}
                record["cost_instrumentation"] = implementation != "plain_c"
                row = dict(case=case["case"], scope=scopes[scope], phase=phase,
                           pair=group_id, order=position, implementation=implementation, **record)
                rows.append(row)
                writer = csv.DictWriter(raw, fieldnames=list(row))
                if raw.tell() == 0:
                    writer.writeheader()
                writer.writerow(row)
            raw.flush()
        return min(record["elapsed_ns"] for record in found.values())

    for scope in range(len(scopes)):
        group(scope, "verification", 0, 1, True)
        for i in range(6):
            group(scope, "warmup", i, 3)
        reps = 1
        for attempt in range(16):
            elapsed = group(scope, "calibration", attempt, reps)
            if elapsed >= target_ms * 1e6 or reps >= 1_000_000:
                break
            reps = min(1_000_000, max(reps + 1, min(reps * 8,
                int(reps * target_ms * 1e6 / max(elapsed, 1) * 1.2))))
        for i in range(samples):
            group(scope, "measurement", i, reps)
        group(scope, "verification", 1, 1, True)


def validate_groups(rows):
    groups = {}
    for row in rows:
        required = ROW_FIELDS | TIMING_FIELDS | COST_FIELDS
        if not required <= row.keys() or row.keys() - required - CALL_FIELDS:
            raise ValueError("unexpected measurement row schema")
        if any(not isinstance(row[field], str) or not row[field] for field in ("case", "scope")):
            raise ValueError("missing case/scope identity")
        if row["phase"] not in {"warmup", "calibration", "measurement"}:
            raise ValueError("unexpected measurement phase")
        if type(row["pair"]) is not int or row["pair"] < 0 or type(row["order"]) is not int or not 0 <= row["order"] <= 2:
            raise ValueError("invalid measurement group/order")
        timing = {field: row[field] for field in TIMING_FIELDS}
        implementation = row["implementation"]
        if implementation == "plain_c":
            check_plain_record(timing, False)
            if any(row[field] is not None for field in (COST_FIELDS | CALL_FIELDS) & row.keys()):
                raise ValueError("plain-C timing record invents cost observations")
        else:
            check_plain_record({**timing, **{field: row[field] for field in COST_FIELDS}}, True)
            if any(type(row[field]) is not int or row[field] < 0 for field in CALL_FIELDS & row.keys()):
                raise ValueError("invalid arena operation counter")
        key = tuple(row[field] for field in ("case", "scope", "phase", "pair"))
        group = groups.setdefault(key, {})
        if implementation not in IMPLEMENTATIONS or implementation in group:
            raise ValueError("unknown or duplicate implementation in measurement group")
        group[implementation] = row
    for group in groups.values():
        if set(group) != set(IMPLEMENTATIONS) or {r["order"] for r in group.values()} != {0, 1, 2}:
            raise ValueError("incomplete or incorrectly ordered measurement group")
        generated, arena, plain = (group[name] for name in IMPLEMENTATIONS)
        if generated.keys() != arena.keys() or generated.keys() != plain.keys():
            raise ValueError("mismatched measurement row schema")
        for reference in (arena, plain):
            compare_payload(generated, reference)
        for key in generated.keys() - ROW_FIELDS - {"elapsed_ns", "process_maxrss_kib"}:
            if generated[key] != arena.get(key):
                raise ValueError(f"generated/arena-C contract differs: {key}")
    return groups


def summarize(rows, out, statistics_module, title):
    validate_groups(rows)
    groups = {}
    for row in rows:
        if row["phase"] == "measurement":
            groups.setdefault((row["case"], row["scope"]), {}).setdefault(row["pair"], {})[row["implementation"]] = row
    if not groups:
        raise ValueError("no complete measurement groups")
    summaries = []
    comparisons = (("generated", "plain_c"), ("generated", "arena_c"), ("arena_c", "plain_c"))
    for (case, scope), samples in groups.items():
        implementations = {}
        for name in IMPLEMENTATIONS:
            records = [sample[name] for sample in samples.values()]
            implementations[name] = {
                "ns_per_operation": statistics_module.distribution([r["elapsed_ns"] / r["repetitions"] for r in records]),
                "sample_count": len(records), "repetitions": sorted({r["repetitions"] for r in records}),
                "minimum_batch_ns": min(r["elapsed_ns"] for r in records),
                "process_maxrss_kib": statistics_module.distribution([r["process_maxrss_kib"] for r in records]),
                "cost_observation": "separate native diagnostic replay" if name == "plain_c" else "arena counters in the measured process",
            }
        paired = {}
        for numerator, denominator in comparisons:
            ratios, differences = [], []
            for sample in samples.values():
                a, b = (sample[name]["elapsed_ns"] / sample[name]["repetitions"] for name in (numerator, denominator))
                if a <= 0 or b <= 0:
                    raise ValueError("nonpositive measurement interval")
                ratios.append(a / b); differences.append(a - b)
            rng = random.Random(20261030)
            bootstrap = [statistics.median(rng.choices(ratios, k=len(ratios))) for _ in range(5000)]
            paired[f"{numerator}/{denominator}"] = {
                "ratio": statistics_module.distribution(ratios), "delta_ns": statistics_module.distribution(differences),
                "ratio_bootstrap_95_interval": [statistics_module.percentile(bootstrap, .025),
                                                statistics_module.percentile(bootstrap, .975)],
            }
        summaries.append(dict(case=case, scope=scope, implementations=implementations, comparisons=paired))
    result = dict(schema=2, acceptance_comparator="plain_c", records=summaries,
                  bootstrap_note="Paired within-run percentile bootstrap; not host/process uncertainty or an acceptance test.",
                  performance_acceptance="not established; controlled host and predeclared budgets remain required")
    (out / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
    lines = [f"# {title}", "", "Times are ns/operation. All three implementations use the same repetition count within each rotating-order group.",
             "Plain C uses aligned allocation and direct packing/CBLAS; it contains no arena, Lean, or diagnostic cost counters.",
             "Generated/arena-C isolates codegen overhead relative to the shared runtime. Generated/plain-C is the performance comparator.",
             "Plain-C costs are validated in a separate instrumented replay; blank timing cost fields mean unobserved, not zero.",
             "No controlled-host acceptance follows from this report.", "",
             "| Case | Scope | Generated median | Arena-C median | Plain-C median | Generated/plain-C ratio [95%] | Generated/arena-C ratio |",
             "| --- | --- | ---: | ---: | ---: | ---: | ---: |"]
    for entry in summaries:
        medians = [entry["implementations"][name]["ns_per_operation"]["median"] for name in IMPLEMENTATIONS]
        plain = entry["comparisons"]["generated/plain_c"]
        low, high = plain["ratio_bootstrap_95_interval"]
        arena = entry["comparisons"]["generated/arena_c"]["ratio"]["median"]
        lines.append(f'| {entry["case"]} | {entry["scope"]} | {medians[0]:.1f} | {medians[1]:.1f} | {medians[2]:.1f} | '
                     f'{plain["ratio"]["median"]:.3f} [{low:.3f}, {high:.3f}] | {arena:.3f} |')
    (out / "summary.md").write_text("\n".join(lines) + "\n")
