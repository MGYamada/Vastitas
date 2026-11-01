"""Audit the preserved post-regroup/full Linux run; never rebuild or modify project files.

Uses Python's standard library and Git. The measured commit must be available
in this repository. Consistency checks are not native refinement or a controlled
performance acceptance test.
"""
from collections import Counter, defaultdict
import csv
import hashlib
import io
import json
from pathlib import Path
import random
import re
import statistics
import subprocess
import zipfile

if not __debug__:
    raise RuntimeError("Run this audit without Python -O: assertions are required")

SAVED = Path(__file__).resolve().parent
REPOSITORY = SAVED.parents[3]
HEAD = "7486d2ca7f8f9bb9cd2bc4d77335b47e79ebf28c"
ARCHIVE_SHA = "c7005be138e3e096ed9564fcd526d5ba7ceeebc3c7f0765941e674f66e7b476d"
SCOPES = ["lifecycle", "reused_buffers", "pack3_adapter", "regroup3_adapter", "first_blas", "second_blas"]
PLAIN = ["cases.json", "compile-times.json", "environment.json", "native-validation.json",
         "openblas-build.json", "raw.csv", "status.json", "summary.json", "summary.md"]


def digest(data):
    return hashlib.sha256(data).hexdigest()


archive = (SAVED / "evidence.zip").read_bytes()
assert digest(archive) == ARCHIVE_SHA
manifest = json.loads((SAVED / "artifact-manifest.json").read_text())
assert manifest["measured_head"] == HEAD and manifest["archive_sha256"] == ARCHIVE_SHA
assert manifest["archive_bytes"] == len(archive)
assert (manifest["run"], manifest["job"]) == (41290985225, 124802014404)
assert manifest["launcher_commit"] == "ab015081534035ad34bea7c4dfac469b8fac79cf"
assert manifest["inspection_artifact"]["downloaded"] is False
with zipfile.ZipFile(io.BytesIO(archive)) as zipped:
    assert zipped.testzip() is None
    names = zipped.namelist()
    assert len(names) == len(set(names)) == len(manifest["files"])
    assert {entry["path"] for entry in manifest["files"]} == set(names)
    files = {name: zipped.read(name) for name in names}
for entry in manifest["files"]:
    data = files[entry["path"]]
    assert len(data) == entry["bytes"] and digest(data) == entry["sha256"]
for name in PLAIN:
    assert (SAVED / name).read_bytes() == files[name], name


def load(name):
    return json.loads(files[name])


provenance = json.loads((SAVED / "launch-provenance.json").read_text())
assert provenance["measured_head"] == HEAD
assert provenance["launcher_commit"] == manifest["launcher_commit"]
assert (provenance["run_id"], provenance["job_id"]) == (manifest["run"], manifest["job"])
assert provenance["profile"] == "full" and provenance["trigger"] == "push"
for name, revision, hash_key in (
    ("measured-workflow.yml", HEAD, "measured_workflow_sha256"),
    ("launcher-workflow.yml", manifest["launcher_commit"], "launcher_workflow_sha256"),
):
    snapshot = (SAVED / name).read_bytes()
    original = subprocess.run(["git", "show", revision + ":.github/workflows/contraction-tree-experiment.yml"],
                              cwd=REPOSITORY, check=True, stdout=subprocess.PIPE).stdout
    assert snapshot == original and digest(snapshot) == provenance[hash_key]
assert ("ref: " + HEAD) in (SAVED / "launcher-workflow.yml").read_text()
assert "TREE_PROFILE: full" in (SAVED / "launcher-workflow.yml").read_text()

environment = load("environment.json")
assert environment["toolchains"]["git"]["stdout"].strip() == HEAD
assert environment["toolchains"]["git_status"]["stdout"] == ""
assert environment["recorded_inputs_unchanged"] is True
assert environment["leak_sanitizer"] == "enabled"
assert environment["cpu"] in environment["cpu_affinity_before"]
assert environment["threads"] == 1 and environment["policy"] == "NativeFast"
assert "x86_64" in environment["platform"]
assert environment["expected_lean_toolchain"] == "leanprover/lean4:v4.35.0"
assert "--smoke" not in environment["argv"]
assert environment["argv"][environment["argv"].index("--samples") + 1] == "11"
assert environment["argv"][environment["argv"].index("--target-ms") + 1] == "5"
assert environment["flags"] == ["-std=c11", "-O3", "-fno-lto", "-Wall", "-Wextra", "-Werror"]
source_count = 0
for name, expected in environment["source_sha256"].items():
    if Path(name).is_absolute():
        continue  # Binary/backend hashes are recorded, not claimed archived.
    snapshot = files["source/" + name]
    assert digest(snapshot) == expected
    original = subprocess.run(["git", "show", HEAD + ":" + name], cwd=REPOSITORY,
                              check=True, stdout=subprocess.PIPE).stdout
    assert snapshot == original, name
    source_count += 1
assert source_count == len([p for p in environment["source_sha256"] if not Path(p).is_absolute()])
backend = load("openblas-build.json")
assert backend["version"] == "0.3.34" and backend["cpu_target"] == "HASWELL"
assert backend["integer_abi"] == "LP64" and backend["threading"] == "sequential with locking"
assert len([name for name in environment["source_sha256"] if name.endswith("/lib/libopenblas.a")]) == 1


rows = list(csv.DictReader(io.StringIO(files["raw.csv"].decode())))
cases = load("cases.json")
assert len(cases) == 12 and len({case["case"] for case in cases}) == 12
by_case = {case["case"]: case for case in cases}
case_order = {case["case"]: index for index, case in enumerate(cases)}


def costs(row, case, scope):
    repetitions = int(row["repetitions"])
    assert 0 < repetitions <= 1000000 and int(row["elapsed_ns"]) > 0
    width = 16 if case["scalar"] else 8
    i, k, j, a, b, padding = (case[key] for key in ("i", "k", "j", "a", "b", "pad"))
    dimensions = [(i, k*j), (k, a), (j, b), (i*j, k), (i*j, a), (i*a, b), (i*a, j)]
    capacities = [(index+1)*padding + (r+(index+2)*padding)*c + 3*padding
                  for index, (r, c) in enumerate(dimensions)]
    capacity = (sum(capacities[:6]) - capacities[3] + max(capacities[3], capacities[6])) * width
    first, second, output = (width*i*k*j, width*i*j*a, width*i*a*b)
    writes, copies = first + 2*second + output, first + second
    initialization = capacity + width*(i*k*j + k*a + j*b + 6)
    lifecycle = scope == "lifecycle"
    lives = repetitions if lifecycle else 1
    expected = {
        "data_allocations": 6*lives, "data_frees": 6*lives, "live_bytes_after": 0,
        "peak_data_bytes": capacity, "written_bytes": initialization*lives + writes*repetitions,
        "copied_bytes": copies*repetitions, "metadata_allocations": 2*lives,
        # Recorded x86-64 ABI: 88-byte arena plus eight 24-byte Buffer entries.
        "peak_metadata_bytes": 280,
        "timed_data_allocations": 6*repetitions if lifecycle else 0,
        "timed_data_frees": 6*repetitions if lifecycle else 0,
        "timed_written_bytes": (initialization+writes)*repetitions if lifecycle else writes*repetitions,
        "timed_copied_bytes": copies*repetitions,
        "timed_metadata_allocations": 2*repetitions if lifecycle else 0,
        "selected_pack_calls_timed": repetitions if scope in ("pack3_adapter", "regroup3_adapter") else 0,
        "blas_calls_timed": repetitions if scope in ("first_blas", "second_blas") else 0,
    }
    for key, value in expected.items():
        assert int(row[key]) == value, (case["case"], scope, key, row[key], value)


def match(left, right):
    assert left.keys() == right.keys()
    for key in left.keys() - {"implementation", "order", "elapsed_ns", "process_maxrss_kib"}:
        assert left[key] == right[key], (key, left[key], right[key])


pairs = defaultdict(dict)
for row in rows:
    key = tuple(row[field] for field in ("case", "scope", "phase", "pair"))
    assert row["scope"] in SCOPES and row["phase"] in ("warmup", "calibration", "measurement")
    assert row["implementation"] not in pairs[key]
    pairs[key][row["implementation"]] = row
    costs(row, by_case[row["case"]], row["scope"])
for key, pair in pairs.items():
    assert set(pair) == {"generated", "c"}
    assert {row["order"] for row in pair.values()} == {"0", "1"}
    match(pair["generated"], pair["c"])
    first = "generated" if (int(key[3]) + (case_order[key[0]] if key[2] == "measurement" else 0)) % 2 == 0 else "c"
    assert pair[first]["order"] == "0"
assert len(rows) == 2 * len(pairs)
assert Counter(row["phase"] for row in rows) == Counter(warmup=288, calibration=len(rows)-1872, measurement=1584)


def percentile(values, fraction):
    ordered = sorted(values)
    position = (len(ordered)-1)*fraction
    low = int(position)
    return ordered[low] + (ordered[min(low+1, len(ordered)-1)]-ordered[low])*(position-low)


def distribution(values):
    median = statistics.median(values)
    return dict(median=median, q25=percentile(values, .25), q75=percentile(values, .75),
                min=min(values), max=max(values), mad=statistics.median(abs(value-median) for value in values))


summaries = load("summary.json")
assert {(entry["case"], entry["scope"]) for entry in summaries} == {(case, scope) for case in by_case for scope in SCOPES}
assert len(summaries) == 72
final_calibrations = []
for summary in summaries:
    case, scope = summary["case"], summary["scope"]
    measured = [row for row in rows if row["case"] == case and row["scope"] == scope and row["phase"] == "measurement"]
    assert Counter(row["implementation"] for row in measured) == Counter(generated=11, c=11)
    assert {int(row["pair"]) for row in measured} == set(range(11))
    assert len({row["repetitions"] for row in measured}) == 1
    calibration = [row for row in rows if row["case"] == case and row["scope"] == scope and row["phase"] == "calibration"]
    last = max(int(row["pair"]) for row in calibration)
    assert {int(row["pair"]) for row in calibration} == set(range(last+1))
    final = pairs[case, scope, "calibration", str(last)]
    assert all(row["repetitions"] == measured[0]["repetitions"] for row in final.values())
    final_calibrations.append(min(int(row["elapsed_ns"]) for row in final.values()))
    ratios, deltas = [], []
    for pair_id in range(11):
        pair = pairs[case, scope, "measurement", str(pair_id)]
        generated, c = (int(pair[name]["elapsed_ns"])/int(pair[name]["repetitions"]) for name in ("generated", "c"))
        ratios.append(generated/c)
        deltas.append(generated-c)
    assert distribution(ratios) == summary["paired_ratio"]
    assert distribution(deltas) == summary["paired_delta_ns"]
    for name in ("generated", "c"):
        selected = [row for row in measured if row["implementation"] == name]
        result = summary["implementations"][name]
        assert distribution([int(row["elapsed_ns"])/int(row["repetitions"]) for row in selected]) == result["ns_per_operation"]
        assert distribution([int(row["process_maxrss_kib"]) for row in selected]) == result["process_maxrss_kib"]
        assert result["sample_count"] == 11 and result["repetitions"] == int(selected[0]["repetitions"])
        assert result["minimum_batch_ns"] == min(int(row["elapsed_ns"]) for row in selected)
        for field in ("peak_data_bytes", "peak_metadata_bytes"):
            assert result[field] == sorted({int(row[field]) for row in selected})
    implementations = summary["implementations"]
    assert summary["ratio_of_separate_medians"] == implementations["generated"]["ns_per_operation"]["median"] / implementations["c"]["ns_per_operation"]["median"]
    generator = random.Random(20261030)
    bootstrap = [statistics.median(generator.choices(ratios, k=11)) for _ in range(5000)]
    assert [percentile(bootstrap, .025), percentile(bootstrap, .975)] == summary["paired_ratio_bootstrap_95_interval"]

commands = load("commands.json")
timed_commands = [command for command in commands if command["phase"] in ("warmup", "calibration", "measurement")]
assert len(timed_commands) == len(rows)
for row, command in zip(rows, timed_commands):
    assert command["returncode"] == 0 and command["phase"] == row["phase"]
    assert command["command"][-4:] == [row["implementation"], str(SCOPES.index(row["scope"])), row["repetitions"], "0"]
    assert row["case"] in Path(command["command"][0]).parts
    for field, value in json.loads(command["stdout"]).items():
        assert row[field] == str(value)
verifications = [command for command in commands if command["phase"] == "runtime_validation"]
assert len(verifications) == 288
for offset in range(0, len(verifications), 2):
    left, right = verifications[offset:offset+2]
    assert left["returncode"] == right["returncode"] == 0
    assert left["command"][-3:] == right["command"][-3:]
    assert left["command"][-1] == "1" and {left["command"][-4], right["command"][-4]} == {"generated", "c"}
    case = next(part for part in Path(left["command"][0]).parts if part in by_case)
    scope = SCOPES[int(left["command"][-3])]
    a, b = json.loads(left["stdout"]), json.loads(right["stdout"])
    match(a, b)
    assert a["checksum"] != "0000000000000000"
    costs(a, by_case[case], scope)
    costs(b, by_case[case], scope)
native = load("native-validation.json")
assert len(native) == 24 and Counter((record["case"], record["sanitizer"]) for record in native) == Counter({(case, sanitizer): 1 for case in by_case for sanitizer in (False, True)})
native_commands = [command for command in commands if command["phase"] in ("native_correctness", "sanitizer")]
assert len(native_commands) == len(native)
for record, command in zip(native, native_commands):
    assert record["status"] == "passed" and len(record["rows"]) == 12 and command["returncode"] == 0
    assert record["case"] in Path(command["command"][0]).parts
    assert record["rows"] == [json.loads(line) for line in command["stdout"].splitlines()]
    assert command["phase"] == ("sanitizer" if record["sanitizer"] else "native_correctness")
    assert "parallel=0; threads=1" in command["stderr"]
    assert all(f"flat-copy stage {stage} rejected" in command["stderr"] for stage in (1, 2))
    for offset, scope in enumerate(SCOPES):
        a, b = record["rows"][2*offset:2*offset+2]
        match(a, b)
        costs(a, by_case[record["case"]], scope)
        costs(b, by_case[record["case"]], scope)
failed = [command for command in commands if command["returncode"]]
assert len(failed) == 12 and all(command["phase"] == "frontend_capture" and command["returncode"] == 1 and "E_CAPTURED" in command["stderr"] for command in failed)
phases = Counter(command["phase"] for command in commands)
assert all(phases[phase] == 12 for phase in ("independent_lean_check", "independent_lean_emit", "public_check_total", "public_build_total", "canonical_execution_validation", "generated_native_compile"))
emits = [command for command in commands if command["phase"] == "independent_lean_emit"]
canonical = [command for command in commands if command["phase"] == "canonical_execution_validation"]
for case, emit, execution in zip(cases, emits, canonical):
    base = "cases/" + case["case"] + "/"
    response = load(base + "response.json")
    assert response == json.loads(emit["stdout"]) and response["ok"] and response["version"] == 8
    generated = files[base + "Generated.lean"].decode()
    assert generated == response["lean_source"]
    wrapper = files[base + "Main.lean"].decode()
    operations = lambda text: [line.strip() for line in text.splitlines() if re.match(r"\s*(allocate|fill|store|expect|drop|pack3|regroup3|VastitasGemmNative\.gemm) arena ", line)]
    assert operations(wrapper) == operations(generated)*2
    assert wrapper.count("finally\n") == 2 and "IO.println" not in wrapper
    assert execution["returncode"] == 0 and execution["stdout"].strip() == "0"
inspections = [command for command in commands if command["phase"] == "inspection"]
assert len(inspections) == 36
assert sum(command["stdout_file"] in files for command in inspections) == 12
for command in inspections:
    assert command["returncode"] == 0 and command["stdout_bytes"] > 0
    if command["stdout_file"] in files:
        data = files[command["stdout_file"]]
        assert len(data) == command["stdout_bytes"] and digest(data) == command["stdout_sha256"]
    else:
        assert Path(command["stdout_file"]).name in ("symbols.txt", "disassembly.txt")
assert load("status.json") == {"status": "passed", "performance": "exploratory measurements on this host; not controlled-host acceptance", "rows": len(rows)}
assert load("compile-times.json") == [command for command in commands if any(word in command["phase"] for word in ("compile", "check", "capture", "build", "emit"))]

report = {
    "measured_head": HEAD, "archive_members": len(files), "plain_copies_verified": len(PLAIN),
    "archived_sources_exact_measured_git": source_count, "raw_rows": len(rows), "pairs": len(pairs),
    "phase_rows": dict(Counter(row["phase"] for row in rows)), "groups": len(summaries),
    "native_records": len(native), "verification_commands": len(verifications),
    "final_calibrations_reaching_5ms": sum(value >= 5000000 for value in final_calibrations),
    "minimum_final_calibration_batch_ns": min(final_calibrations),
    "measurement_batches_below_5ms": dict(Counter(row["scope"] for row in rows if row["phase"] == "measurement" and int(row["elapsed_ns"]) < 5000000)),
    "minimum_measurement_batch_ns": min(int(row["elapsed_ns"]) for row in rows if row["phase"] == "measurement"),
    "rss_kib_values": sorted({int(row["process_maxrss_kib"]) for row in rows}),
    "peak_arena_bytes": max(int(row["peak_data_bytes"]) for row in rows),
    "peak_metadata_bytes": sorted({int(row["peak_metadata_bytes"]) for row in rows}),
    "unexpected_command_failures": 0,
}
print(json.dumps(report, indent=2))
