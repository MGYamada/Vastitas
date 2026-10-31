#!/usr/bin/env python3
"""Prepared diagonal adapter versus equivalent C; not public-source performance acceptance."""
import argparse
import csv
import datetime
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import statistics
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
FIELDS = "scope operation scalar n m uniform pair order implementation repetitions elapsed_ns hash data_allocations copied_bytes written_bytes".split()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--cc", default="cc")
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    prefix = args.prefix.resolve()
    commands = []
    env = dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1")
    def run(command):
        p = subprocess.run(list(map(str, command)), cwd=ROOT, env=env, capture_output=True, text=True)
        record = dict(command=list(map(str, command)), returncode=p.returncode, stdout=p.stdout, stderr=p.stderr)
        commands.append(record)
        (out / "commands.json").write_text(json.dumps(commands, indent=2)+"\n")
        if p.returncode:
            raise RuntimeError(f"{command}\n{p.stdout}\n{p.stderr}")
        return p.stdout
    files = [HERE / name for name in ["probe.c", "direct.c", "direct.h", "run.py"]]
    files += [ROOT / "lean-kernel/native" / name for name in ["storage.c", "storage.h", "diagonal.c", "diagonal.h"]]
    files += [ROOT / "lean-kernel/numerical" / name for name in ["gemm.c", "gemm.h"]]
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    for path in files:
        saved = out / "sources" / path.relative_to(ROOT)
        saved.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, saved)
    provenance = dict(timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(), platform=platform.platform(),
        machine=platform.machine(), head=run(["git", "rev-parse", "HEAD"]).strip(), dirty=run(["git", "status", "--short"]),
        sources={str(p.relative_to(ROOT)):sha(p) for p in files}, openblas_archive_sha256=sha(prefix / "lib/libopenblas.a"),
        compiler=run(shlex.split(args.cc)+["--version"]), scope="C adapter versus equivalent C in prepared-pointer and matched-preflight scopes; excludes public source, Lean FFI, lifecycle, metadata construction, and backend allocations")
    (out / "provenance.json").write_text(json.dumps(provenance, indent=2)+"\n")
    includes = ["-I", HERE, "-I", ROOT / "lean-kernel/native", "-I", ROOT / "lean-kernel/numerical", "-I", prefix / "include"]
    sources = [HERE / "probe.c", HERE / "direct.c", ROOT / "lean-kernel/native/storage.c",
               ROOT / "lean-kernel/native/diagonal.c", ROOT / "lean-kernel/numerical/gemm.c"]
    cases = [(0,n,m) for n,m in [(1,1),(3,5),(64,96),(192,256)]]+[(1,n,1) for n in [1,3,256,4096]]
    rows = []
    with tempfile.TemporaryDirectory(prefix="vastitas-diagonal-experiment-") as tmp:
        exe = Path(tmp) / "probe"
        flags = ["-std=c11", "-O3", "-fno-lto", "-Wall", "-Wextra", "-Werror"]
        run(shlex.split(args.cc)+flags+includes+sources+[prefix / "lib/libopenblas.a", "-lm", "-lpthread", "-o", exe])
        for scalar in [0,1]:
            for operation,n,m in cases:
                reps = max(64, 2000000//(n*(m if operation==0 else 1)))
                raw = run([exe,operation,scalar,n,m,reps])
                selected = list(csv.DictReader(io.StringIO(raw), fieldnames=FIELDS))
                if len(selected)!=44:
                    raise ValueError("missing paired measurements")
                for index in range(0,len(selected),2):
                    a,b = selected[index:index+2]
                    for field in FIELDS:
                        if field not in ["order","implementation","elapsed_ns"] and a[field]!=b[field]:
                            raise ValueError(f"different work/output: {field}: {a} / {b}")
                    if a["data_allocations"]!="0" or a["copied_bytes"]!="0":
                        raise ValueError("unexpected data allocation/copy")
                rows += selected
        sanitizer = Path(tmp) / "sanitizer"
        flags = ["-std=c11", "-O1", "-g", "-fno-lto", "-Wall", "-Wextra", "-Werror",
                 "-fsanitize=address,undefined", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer"]
        if platform.system()=="Linux":
            flags += ["-fno-pie", "-no-pie"]
        run(shlex.split(args.cc)+flags+includes+sources+[prefix / "lib/libopenblas.a", "-lm", "-lpthread", "-o", sanitizer])
        for scalar in [0,1]:
            for operation in [0,1]:
                run([sanitizer,operation,scalar,3,5 if operation==0 else 1,2])
    with (out / "samples.csv").open("w") as f:
        writer=csv.DictWriter(f,fieldnames=FIELDS);writer.writeheader();writer.writerows(rows)
    summary=[]
    for scope in ["prepared","checked"]:
      for scalar in [0,1]:
        for operation,n,m in cases:
            chosen=[r for r in rows if r["scope"]==scope and r["operation"]==("pair" if operation else "adjoint") and int(r["scalar"])==scalar and int(r["n"])==n and int(r["m"])==m and int(r["pair"])>=2]
            def durations(impl):
                return [int(r["elapsed_ns"])/int(r["repetitions"]) for r in chosen if r["implementation"]==impl]
            a,c=durations("adapter"),durations("c")
            ratios=[]
            for pair in range(2,11):
                members={r["implementation"]:int(r["elapsed_ns"]) for r in chosen if int(r["pair"])==pair}
                ratios.append(members["adapter"]/members["c"])
            summary.append(dict(scope=scope,operation="pair" if operation else "adjoint",scalar="complex" if scalar else "real",n=n,m=m,
                adapter_ns=statistics.median(a),c_ns=statistics.median(c),paired_ratio=statistics.median(ratios),
                min_ratio=min(ratios),max_ratio=max(ratios),sample_pairs=9))
    (out / "summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    lines=["# Prepared diagonal operation measurements", "", provenance["scope"]+".",
           "The first two pairs warm up each case; nine alternating-order pairs remain. Times are medians in ns/operation; ratio is the median of paired ratios. This shared host run is exploratory, with no performance acceptance claim.", "",
           "| Scope | Operation | Scalar | Shape n × m | Adapter ns | C ns | Paired ratio [min, max] |", "|---|---|---|---:|---:|---:|---:|"]
    for s in summary:
        lines.append(f'| {s["scope"]} | {s["operation"]} | {s["scalar"]} | {s["n"]} × {s["m"]} | {s["adapter_ns"]:.1f} | {s["c_ns"]:.1f} | {s["paired_ratio"]:.3f} [{s["min_ratio"]:.3f}, {s["max_ratio"]:.3f}] |')
    lines += ["", "All 352 output/cost pairs match, including both weighted scratch and scalar output. The four sanitizer cases also pass. Repeated operations allocate/copy zero arena data bytes and write exactly mn scalar-width bytes per adjoint or (n+1) scalar-width bytes per pairing. Both sides reuse padded caller storage; C receives pre-realized double coefficients, while the adapter decodes and validates immutable binary64 bits. Both sides record the same write-counter calls. The checked C scope repeats the complete applicable physical/bit/backend/counter preflight with the same primitive validators before writes; the prepared scope deliberately excludes those checks. Pairing uses the identical pinned sequential OpenBLAS GEMM; internal backend allocation is not counted.", "", "Setup (excluded): arena allocation/fill, coefficient allocation/encoding, pointer preparation. The harness creates four coefficient tables totaling 32·max(n,m) bytes; this is harness metadata, not generated-program allocation evidence. Production generated constants hold 8·(n+m) bytes for explicit adjoint diagonals or 8·n bytes for pairing (identity/scaled identity uses 8 bytes per metric), plus Lean object/container overhead. Public generated execution, Lean metadata initialization/lifetime, full lifecycle, total/backend allocation and controlled-host acceptance remain separate obligations. See the checked-source/native regressions and the Stage 1 gate."]
    (out / "RESULTS.md").write_text("\n".join(lines)+"\n")
    print(out / "RESULTS.md")


if __name__=="__main__":
    main()
