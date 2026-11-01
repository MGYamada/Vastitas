"""Audit retained native adapter A/B data without executing the archived code."""
from collections import Counter, defaultdict
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import statistics
import subprocess
import zipfile

if not __debug__:
    raise RuntimeError("Run this audit without Python -O: assertions are required")

SAVED = Path(__file__).resolve().parent
ROOT = SAVED.parents[3]
BASE = "618508530cdd191ebe9a18d5ce6a9d03dc96c9a7"
HEAD = "2a59bdbd5262de386a018e5ad0befae6a762cac3"
SHA = "860ced38fb5b758a6089b4b35f8f7b6a37945ef4ca04bc0a9507bd5c4c23578c"
LABELS = {"variable_copy": 658, "unbounded_fixed": 664, "short_dirty": 660, "short_clean": 660}
FLAGS = ["cc", "-std=c11", "-O3", "-fno-lto", "-Wall", "-Wextra", "-Werror"]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source(commit, path):
    return subprocess.run(["git", "show", commit + ":" + path], cwd=ROOT, check=True,
                          stdout=subprocess.PIPE).stdout


archive = (SAVED / "evidence.zip").read_bytes()
assert len(archive) == 197024 and digest(archive) == SHA
manifest = json.loads((SAVED / "artifact-manifest.json").read_text())
assert manifest["archive_sha256"] == SHA and manifest["archive_bytes"] == len(archive)
assert manifest["baseline"] == BASE and manifest["measured_head"] == HEAD
assert manifest["runs"] == dict(variable_copy=2, unbounded_fixed=3, short_dirty=4, short_clean=5)
with zipfile.ZipFile(io.BytesIO(archive)) as zipped:
    assert zipped.testzip() is None
    names = zipped.namelist()
    assert len(names) == len(set(names)) == len(manifest["files"]) == 45
    assert {entry["path"] for entry in manifest["files"]} == set(names)
    files = {name: zipped.read(name) for name in names}
for entry in manifest["files"]:
    data = files[entry["path"]]
    assert len(data) == entry["bytes"] and digest(data) == entry["sha256"]
for name in ("raw.csv", "summary.json"):
    assert (SAVED / name).read_bytes() == files["short_clean/" + name]
old = source(BASE, "lean-kernel/native/storage.c")
header = source(BASE, "lean-kernel/native/storage.h")
current = source(HEAD, "lean-kernel/native/storage.c")
assert header == source(HEAD, "lean-kernel/native/storage.h")
symbols = sorted(set(re.findall(r"\bvstorage_\w+", old.decode())))
reports = {}
for label, count in LABELS.items():
    base = label + "/"
    load = lambda name: json.loads(files[base + name])
    record = load("record.json")
    assert record["base"] == BASE and files[base + "old.c"] == old
    assert files[base + "storage.h"] == header
    assert record["feature_head"] == (HEAD if label == "short_clean" else BASE)
    if label == "short_clean":
        assert record["clean_before"] == record["clean_after"] == record["diff"] == ""
        assert record["source_unchanged"] is True and files[base + "new.c"] == current
    else:
        assert record["diff"] and "clean_before" not in record
    expected_inventory = {name[len(base):] for name in files if name.startswith(base)} - {"record.json"}
    assert set(record["files"]) == expected_inventory
    for name, expected in record["files"].items():
        assert digest(files[base + name]) == expected
    assert files[base + "probe.c"] == files["short_clean/probe.c"]
    commands = load("commands.json")
    assert len(commands) == 4 and all(row["returncode"] == 0 for row in commands)
    assert commands[0]["command"] == FLAGS + ["-D" + n + "=old_" + n for n in symbols] + ["-c", "old.c", "-o", "old.o"]
    assert commands[1]["command"] == FLAGS + ["-c", "new.c", "-o", "new.o"]
    assert commands[2]["command"] == FLAGS + ["probe.c", "old.o", "new.o", "-o", "probe"]
    assert len(commands[3]["command"]) == 1 and Path(commands[3]["command"][0]).name == "probe"
    assert commands[3]["stdout"].encode() == files[base + "raw.csv"]
    rows = list(csv.DictReader(io.StringIO(files[base + "raw.csv"].decode())))
    assert len(rows) == count
    assert Counter(row["phase"] for row in rows) == Counter(calibration=count-264, measurement=264)
    pairs = defaultdict(dict)
    for row in rows:
        assert row["size"] in ("tiny", "small", "bulk")
        assert row["scalar"] in ("0", "1") and row["padding"] in ("0", "1")
        assert row["implementation"] in ("old", "new") and row["phase"] in ("calibration", "measurement")
        for field in ("pair", "order", "repetitions", "elapsed_ns"):
            assert row[field].isdigit()
        assert 0 < int(row["repetitions"]) <= 1000000
        # A one-operation calibration can fall below clock resolution. It is
        # retained and doubled, never used as a measured sample or divisor.
        assert int(row["elapsed_ns"]) > 0 or row["phase"] == "calibration"
        key = tuple(row[field] for field in ("size", "scalar", "padding", "phase", "pair"))
        assert row["implementation"] not in pairs[key]
        pairs[key][row["implementation"]] = row
    for key, pair in pairs.items():
        assert set(pair) == {"old", "new"}
        assert pair["old"]["repetitions"] == pair["new"]["repetitions"]
        assert {row["order"] for row in pair.values()} == {"0", "1"}
        offset = 0 if key[3] == "calibration" else ("tiny", "small", "bulk").index(key[0]) + int(key[1]) + int(key[2])
        first = "new" if (int(key[4]) + offset) % 2 else "old"
        assert pair[first]["order"] == "0"
    summaries = load("summary.json")
    subjects = {(size, scalar, pad) for size in ("tiny", "small", "bulk") for scalar in ("0", "1") for pad in ("0", "1")}
    assert len(summaries) == 12 and {(s["size"], s["scalar"], s["padding"]) for s in summaries} == subjects
    observations = []
    for summary in summaries:
        subject = (summary["size"], summary["scalar"], summary["padding"])
        selected = [row for row in rows if (row["size"], row["scalar"], row["padding"]) == subject]
        measured = [row for row in selected if row["phase"] == "measurement"]
        assert len(measured) == 22 and {int(r["pair"]) for r in measured} == set(range(11))
        assert len({r["repetitions"] for r in measured}) == 1
        calibration = [r for r in selected if r["phase"] == "calibration"]
        last = max(int(r["pair"]) for r in calibration)
        assert {int(r["pair"]) for r in calibration} == set(range(last+1))
        for index in range(last+1):
            trial = pairs[subject + ("calibration", str(index))]
            assert int(trial["old"]["repetitions"]) == min(2**index, 1000000)
        assert trial["old"]["repetitions"] == measured[0]["repetitions"]
        assert min(int(r["elapsed_ns"]) for r in trial.values()) >= 8000000 or int(measured[0]["repetitions"]) == 1000000
        ratios, deltas = [], []
        for index in range(11):
            pair = pairs[subject + ("measurement", str(index))]
            a, b = (int(pair[side]["elapsed_ns"])/int(pair[side]["repetitions"]) for side in ("old", "new"))
            ratios.append(b/a)
            deltas.append(b-a)
        assert summary["ratios"] == ratios and summary["deltas_ns"] == deltas
        assert summary["paired_median_ratio"] == statistics.median(ratios)
        assert summary["paired_median_delta_ns"] == statistics.median(deltas)
        observations.append(dict(size=subject[0], scalar=subject[1], padding=subject[2],
                                 median_ratio=statistics.median(ratios), min_ratio=min(ratios), max_ratio=max(ratios)))
    reports[label] = dict(raw_rows=len(rows), pairs=len(pairs), measurement_pairs=132,
                         under_target_batches=sum(r["phase"] == "measurement" and int(r["elapsed_ns"]) < 8000000 for r in rows),
                         observations=observations if label == "short_clean" else "retained unchanged")
print(json.dumps(dict(archive_members=len(files), measured_head=HEAD, records=reports,
                     scope="native adapter only; no C-performance acceptance"), indent=2))
