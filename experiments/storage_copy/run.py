#!/usr/bin/env python3
"""Optional C-adapter experiment; no Lean, runtime API changes, or CI gate."""
import argparse
import csv
import datetime as dt
import hashlib
import io
import itertools
import json
import os
from pathlib import Path
import platform
import random
import shlex
import shutil
import statistics
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
ORIGINAL = "63d944ed67d96bfb8ad8183ddb5d7b1303c6c9ab"
SOURCES = ["lean-kernel/native/" + x for x in ("storage.c", "storage.h", "test_storage.c")]
SOURCES += ["experiments/storage_copy/" + x for x in ("bench.h", "probe.c", "driver.c", "run.py")]
FLAGS = ["-std=c11", "-O3", "-Wall", "-Wextra", "-Werror", "-Wpedantic", "-fno-lto"]


def capture(args, cwd=ROOT):
    p = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
    return {"command": [str(x) for x in args], "returncode": p.returncode,
            "stdout": p.stdout, "stderr": p.stderr}


def percentile(values, fraction):
    values = sorted(values)
    at = (len(values) - 1) * fraction
    low = int(at)
    return values[low] + (values[min(low + 1, len(values) - 1)] - values[low]) * (at - low)


def distribution(values):
    median = statistics.median(values)
    return {"median": median, "q25": percentile(values, .25), "q75": percentile(values, .75),
            "min": min(values), "max": max(values),
            "mad": statistics.median(abs(v - median) for v in values)}


def check_pairs(rows):
    pairs = {}
    for row in rows:
        key = (row["phase"], row["scope"], row["pair"])
        pair = pairs.setdefault(key, {})
        if row["implementation"] in pair:
            raise ValueError(f"duplicate implementation in pair {key}")
        pair[row["implementation"]] = row
    for key, pair in pairs.items():
        if set(pair) != {"adapter", "c"}:
            raise ValueError(f"incomplete pair {key}")
        a, c = pair["adapter"], pair["c"]
        if {a["order"], c["order"]} != {"0", "1"}:
            raise ValueError(f"invalid order in pair {key}")
        for field in a:
            if field not in {"implementation", "order", "elapsed_ns"} and a[field] != c[field]:
                raise ValueError(f"unequal output/cost contract: {key}, {field}: {a[field]} != {c[field]}")


def summarize(rows, out):
    groups = {}
    for row in rows:
        if row["phase"] == "measurement":
            groups.setdefault((row["case"], row["scope"]), []).append(row)
    summaries = []
    for (case, scope), records in groups.items():
        implementations = {}
        for impl in ("adapter", "c"):
            chosen = [r for r in records if r["implementation"] == impl]
            implementations[impl] = {
                "ns_per_operation": distribution([int(r["elapsed_ns"]) / int(r["repetitions"]) for r in chosen]),
                "sample_count": len(chosen), "repetitions": int(chosen[0]["repetitions"]),
                "minimum_batch_ns": min(int(r["elapsed_ns"]) for r in chosen),
            }
        pairs = {}
        for row in records:
            pairs.setdefault(int(row["pair"]), {})[row["implementation"]] = int(row["elapsed_ns"]) / int(row["repetitions"])
        ratios = [p["adapter"] / p["c"] for p in pairs.values()]
        differences = [p["adapter"] - p["c"] for p in pairs.values()]
        rng = random.Random(20261030)
        boot = [statistics.median(rng.choices(ratios, k=len(ratios))) for _ in range(5000)]
        entry = {"case": case, "scope": scope, "implementations": implementations,
                 "paired_ratio": distribution(ratios), "paired_delta_ns": distribution(differences),
                 "paired_ratio_bootstrap_95_interval": [percentile(boot, .025), percentile(boot, .975)],
                 "bootstrap_note": "Paired within-run percentile bootstrap; not host/process uncertainty or an acceptance test."}
        summaries.append(entry)
    (out / "summary.json").write_text(json.dumps(summaries, indent=2) + "\n")
    lines = ["# C storage-copy measurements", "", "Times are ns/operation; IQR is Q25–Q75. Ratio is median of paired adapter/C ratios.",
             "All scopes are C only. Lifecycle is primary; the other scopes exclude common work.", "",
             "| Case | Scope | Adapter median [IQR] | C median [IQR] | Paired ratio [bootstrap 95%] |",
             "|---|---|---:|---:|---:|"]
    for s in summaries:
        a, c = (s["implementations"][i]["ns_per_operation"] for i in ("adapter", "c"))
        lo, hi = s["paired_ratio_bootstrap_95_interval"]
        lines.append(f'| {s["case"]} | {s["scope"]} | {a["median"]:.1f} [{a["q25"]:.1f}, {a["q75"]:.1f}] | '
                     f'{c["median"]:.1f} [{c["q25"]:.1f}, {c["q75"]:.1f}] | {s["paired_ratio"]["median"]:.3f} [{lo:.3f}, {hi:.3f}] |')
    (out / "summary.md").write_text("\n".join(lines) + "\n")


def cases(smoke):
    sizes = [("empty", 0, 7), ("tiny", 2, 3), ("small", 16, 17), ("cache", 128, 129), ("bulk", 2048, 2051)]
    if smoke:
        sizes = sizes[:2] + [("smoke", 31, 37)]
    result = []
    for (size, m, n), scalar, sp, dp, st, tt in itertools.product(sizes, range(2), range(2), range(2), range(2), range(2)):
        result.append({"case": f'{size}-{"complex" if scalar else "real"}-p{sp}{dp}-t{st}{tt}',
                       "size": size, "rows": m, "columns": n, "scalar": scalar,
                       "source_pad": sp, "target_pad": dp, "source_transpose": st,
                       "target_transpose": tt, "self": 0})
    for (size, m, n), scalar, pad, trans in itertools.product(sizes, range(2), range(2), range(2)):
        result.append({"case": f'{size}-{"complex" if scalar else "real"}-self-p{pad}-t{trans}',
                       "size": size, "rows": m, "columns": n, "scalar": scalar,
                       "source_pad": pad, "target_pad": pad, "source_transpose": trans,
                       "target_transpose": trans, "self": 1})
    random.Random(20261030).shuffle(result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cc", default=os.environ.get("CC", "cc"))
    parser.add_argument("--samples", type=int, default=11)
    parser.add_argument("--target-ms", type=float, default=5)
    parser.add_argument("--cpu", type=int, help="Pin to one allowed Linux CPU; default first allowed CPU")
    parser.add_argument("--smoke", action="store_true", help="Small sizes, still all layouts; not performance evidence")
    parser.add_argument("--skip-sanitizers", action="store_true", help="Record omission explicitly")
    parser.add_argument("--no-leak-sanitizer", action="store_true", help="Keep ASan/UBSan, disable LSan on restricted hosts")
    args = parser.parse_args()
    if not 3 <= args.samples <= 1000 or not 0 < args.target_ms <= 1000:
        parser.error("samples must be 3..1000 and target-ms must be (0,1000]")
    if args.no_leak_sanitizer:
        os.environ["ASAN_OPTIONS"] = os.environ.get("ASAN_OPTIONS", "") + ":detect_leaks=0"
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    cc = shlex.split(args.cc)
    allowed = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None
    cpu = args.cpu if args.cpu is not None else (allowed[0] if allowed else None)
    if cpu is not None:
        os.sched_setaffinity(0, {cpu})
    build = out / "build"
    build.mkdir()
    stage = out / "source"
    hashes = {}
    for rel in SOURCES:
        dest = stage / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / rel, dest)
        hashes[rel] = hashlib.sha256(dest.read_bytes()).hexdigest()
    provenance = {
        "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "argv": sys.argv, "python": sys.version, "platform": platform.platform(),
        "cpu_affinity_before": allowed, "cpu_affinity": cpu, "threads": 1,
        "flags": FLAGS, "cc": cc, "source_sha256": hashes,
        "scope": "Synchronous C adapter only; no Lean FFI, compiler/protocol-8, GEMM, GPU or native refinement claim.",
        "sanitizers": "skipped explicitly" if args.skip_sanitizers else "required separate untimed executables",
        "environment": {k: os.environ.get(k) for k in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MALLOC_ARENA_MAX", "LD_PRELOAD", "ASAN_OPTIONS", "UBSAN_OPTIONS")},
        "host": {},
    }
    for name, command in {
        "compiler": cc + ["--version"], "compiler_target": cc + ["-dumpmachine"],
        "git_head": ["git", "rev-parse", "HEAD"], "git_status": ["git", "status", "--short"],
        "followup_commits": ["git", "log", "--format=%H %s", f"{ORIGINAL}..HEAD"],
        "adapter_diff_since_267": ["git", "diff", ORIGINAL, "HEAD", "--", "lean-kernel/native"],
        "lscpu": ["lscpu"], "uname": ["uname", "-a"], "libc": ["ldd", "--version"],
    }.items():
        try:
            provenance["host"][name] = capture(command)
        except FileNotFoundError as exc:
            provenance["host"][name] = {"unavailable": str(exc)}
    for path in ("/sys/fs/cgroup/cpu.max", "/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/cpu.stat", "/proc/loadavg"):
        if Path(path).is_file():
            provenance["host"][path] = Path(path).read_text()
    (out / "environment.json").write_text(json.dumps(provenance, indent=2) + "\n")
    commands = []

    def run(command, **kwargs):
        record = capture([str(x) for x in command], **kwargs)
        commands.append(record)
        (out / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if record["returncode"]:
            raise RuntimeError(f'{shlex.join(record["command"])}\n{record["stderr"]}\n{record["stdout"]}')
        return record

    source_dir = stage / "experiments/storage_copy"
    objects = []
    for unit in ("probe", "driver"):
        obj = build / f"{unit}.o"
        run(cc + FLAGS + ["-c", source_dir / f"{unit}.c", "-o", obj])
        run(cc + FLAGS + ["-S", source_dir / f"{unit}.c", "-o", out / f"{unit}.s"])
        objects.append(obj)
    exe = build / "bench"
    run(cc + FLAGS + objects + ["-o", exe])
    for name, command in {"symbols.txt": ["nm", "-S", exe],
                          "disassembly.txt": ["objdump", "-d", exe], "linked-libraries.txt": ["ldd", exe]}.items():
        if shutil.which(command[0]):
            result = capture([str(x) for x in command])
            (out / name).write_text(result["stdout"] + result["stderr"])
    run([exe, "--contracts"])
    if not args.skip_sanitizers:
        sanflags = ["-std=c11", "-O1", "-g", "-Wall", "-Wextra", "-Werror", "-fno-lto",
                    "-fsanitize=address,undefined", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer"]
        # Non-PIE avoids Linux ASan shadow-address collisions in some containers.
        if sys.platform.startswith("linux"):
            sanflags += ["-fno-pie", "-no-pie"]
        san = build / "bench-sanitized"
        run(cc + sanflags + [source_dir / "probe.c", source_dir / "driver.c", "-o", san])
        run([san, "--contracts"])
        for c in cases(True):
            values = [c[k] for k in ("rows", "columns", "scalar", "source_pad", "target_pad", "source_transpose", "target_transpose", "self")]
            record = capture([str(x) for x in [san, *values, 0, 0, 0]])
            if record["returncode"]:
                commands.append(record)
                (out / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
                raise RuntimeError(f'Sanitizer failure: {c}\n{record["stderr"]}')
        original_test = build / "native-sanitized"
        run(cc + sanflags + [stage / "lean-kernel/native/storage.c", stage / "lean-kernel/native/test_storage.c", "-o", original_test])
        run([original_test])
        (out / "sanitizers.json").write_text(json.dumps({"status": "passed", "matrix": cases(True),
            "flags": sanflags, "cases": len(cases(True)), "production_c_test": "passed", "contract_tests": "passed",
            "leak_detection_disabled": args.no_leak_sanitizer}, indent=2) + "\n")
    all_cases = cases(args.smoke)
    (out / "cases.json").write_text(json.dumps(all_cases, indent=2) + "\n")
    all_rows = []
    with (out / "raw.csv").open("w", newline="") as raw, (out / "verification.log").open("w") as verified:
        writer = None
        for index, c in enumerate(all_cases):
            values = [c[k] for k in ("rows", "columns", "scalar", "source_pad", "target_pad", "source_transpose", "target_transpose", "self")]
            command = [str(x) for x in [exe, *values, args.samples, int(args.target_ms * 1e6), index % 2]]
            result = capture(command)
            verified.write(c["case"] + ": " + result["stderr"])
            verified.flush()
            if result["returncode"]:
                raise RuntimeError(f'{c}: {result["stderr"]}')
            batch = [{**c, **r} for r in csv.DictReader(io.StringIO(result["stdout"]))]
            check_pairs(batch)
            if writer is None:
                writer = csv.DictWriter(raw, fieldnames=list(batch[0]))
                writer.writeheader()
            writer.writerows(batch); raw.flush(); all_rows.extend(batch)
            print(f'[{index + 1}/{len(all_cases)}] {c["case"]} verified', flush=True)
    summarize(all_rows, out)
    provenance["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
    provenance["case_count"] = len(all_cases)
    provenance["raw_row_count"] = len(all_rows)
    provenance["host"]["loadavg_after"] = Path("/proc/loadavg").read_text() if Path("/proc/loadavg").exists() else None
    provenance["host"]["cpu_stat_after"] = Path("/sys/fs/cgroup/cpu.stat").read_text() if Path("/sys/fs/cgroup/cpu.stat").exists() else None
    (out / "environment.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(f"Saved {out}")


if __name__ == "__main__":
    main()
