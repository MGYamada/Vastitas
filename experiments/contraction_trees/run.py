#!/usr/bin/env python3
"""Actual public two-edge tensor contraction tree versus matched C, pinned sequential OpenBLAS."""
import argparse
import csv
import datetime as dt
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import subprocess
import sys
import time

from cases import ROOT, c_header, cases, driver, write_package

HERE = Path(__file__).resolve().parent
# Reuse the copy experiment's statistical definitions, not a new convention.
_spec = importlib.util.spec_from_file_location("copy_experiment", ROOT / "experiments/storage_copy/run.py")
copy_experiment = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(copy_experiment)
FLAGS = ["-std=c11", "-O3", "-fno-lto", "-Wall", "-Wextra", "-Werror"]
SCOPES = ["lifecycle", "reused_buffers", "pack3_adapter", "regroup3_adapter", "first_blas", "second_blas"]


def dump(path, data):
    # Keep the last complete diagnostic snapshot if a job is interrupted.
    pending = path.with_name(path.name + ".tmp")
    pending.write_text(json.dumps(data, indent=2) + "\n")
    pending.replace(path)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_inputs(hashes):
    changed = []
    for name, expected in hashes.items():
        path = Path(name) if Path(name).is_absolute() else ROOT / name
        if not path.is_file() or sha(path) != expected:
            changed.append(name)
    if changed:
        raise ValueError(f"recorded inputs changed during the experiment: {changed}")


class Runner:
    def __init__(self, out, env):
        self.out, self.env, self.commands = out, env, []

    def run(self, args, *, cwd=ROOT, input=None, env=None, required=True, phase="setup",
            stdout_path=None):
        start = time.perf_counter_ns()
        output = stdout_path.open("w") if stdout_path is not None else None
        try:
            p = subprocess.run(list(map(str,args)), cwd=cwd, input=input, text=True,
                               stdout=output or subprocess.PIPE, stderr=subprocess.PIPE,
                               env=env or self.env, timeout=1200)
            entry = dict(command=list(map(str,args)), cwd=str(cwd), returncode=p.returncode,
                         stdout=p.stdout or "", stderr=p.stderr)
        except (OSError, subprocess.TimeoutExpired) as error:
            entry = dict(command=list(map(str,args)), cwd=str(cwd), returncode=-1, stdout="", stderr=str(error))
        finally:
            if output is not None:
                output.close()
        if stdout_path is not None:
            # Disassembly can be tens of MB per case. Retain it once, rather
            # than copying it into every subsequent command-log snapshot.
            entry.update(stdout_file=str(stdout_path.relative_to(self.out)),
                         stdout_bytes=stdout_path.stat().st_size, stdout_sha256=sha(stdout_path))
        entry.update(wall_ns=time.perf_counter_ns()-start, phase=phase)
        self.commands.append(entry)
        dump(self.out / "commands.json",self.commands)
        if required and entry["returncode"]:
            raise RuntimeError(f"{shlex.join(entry['command'])}\n{entry['stderr']}\n{entry['stdout']}")
        return entry


def instrument_gemm(original, dest):
    dest.write_text('#include "calls.h"\n#define cblas_dgemm bench_dgemm\n#define cblas_zgemm bench_zgemm\n' + original.read_text())


def native_test(runner, c, work, prefix, cc, sanitize, no_lsan):
    work.mkdir(parents=True)
    (work / "case.h").write_text(c_header(c))
    instrument_gemm(ROOT / "lean-kernel/numerical/gemm.c",work / "gemm.c")
    flags = FLAGS if not sanitize else ["-std=c11", "-O1", "-g", "-fno-lto", "-Wall", "-Wextra", "-Werror",
        "-fsanitize=address,undefined", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer"]
    if sanitize and sys.platform.startswith("linux"):
        flags += ["-fno-pie", "-no-pie"]
    exe = work / "test"
    runner.run(cc + flags + ["-DBENCH_STANDALONE", "-I", work, "-I", HERE,
        "-I", ROOT / "lean-kernel/native", "-I", ROOT / "lean-kernel/numerical", "-I", prefix / "include",
        HERE / "probe.c", ROOT / "lean-kernel/native/diagonal.c", work / "gemm.c", prefix / "lib/libopenblas.a", "-lm", "-lpthread", "-o", exe],
        phase="native_correctness_compile")
    env = dict(runner.env)
    if no_lsan:
        env["ASAN_OPTIONS"] = env.get("ASAN_OPTIONS", "") + ":detect_leaks=0"
    result = runner.run([exe], env=env, phase="sanitizer" if sanitize else "native_correctness")
    # Selftest reports alternate C/adapter rows, never public runtime performance.
    rows = [json.loads(line) for line in result["stdout"].splitlines()]
    if len(rows) != 12:
        raise ValueError("missing native validation rows")
    for i in range(0,12,2):
        compare_pair(rows[i],rows[i+1])
    return dict(case=c["case"], status="passed", sanitizer=sanitize, rows=rows)


def compare_pair(a,b):
    excluded = {"elapsed_ns", "process_maxrss_kib"}
    if a.keys() != b.keys():
        raise ValueError("mismatched row schema")
    for key in a:
        if key not in excluded and a[key] != b[key]:
            raise ValueError(f"unequal output/cost contract: {key}: {a[key]} != {b[key]}")


def capture_wire(runner, frontend, package):
    """A deliberately rejecting capture adapter, never an acceptance substitute."""
    capture = package / "capture.py"
    wire = package / "wire.json"
    capture.write_text(f'''#!{sys.executable}
import json, pathlib, sys
pathlib.Path({str(wire)!r}).write_text(sys.stdin.read())
print(json.dumps({{"version":8,"ok":False,"diagnostics":[{{"code":"E_CAPTURED","message":"capture only"}}]}}))
sys.exit(1)
''')
    capture.chmod(0o755)
    env = dict(runner.env, VASTITAS_KERNEL=str(capture))
    result = runner.run([frontend,"check","--manifest-path",package / "Vastitas.toml"],
                        env=env, required=False, phase="frontend_capture")
    if "E_CAPTURED" not in result["stderr"] or result["returncode"] == 0:
        raise ValueError(f"frontend did not reach the protocol-8 boundary: {result}")
    raw = json.loads(wire.read_text())
    if raw["version"] != 8:
        raise ValueError("not public protocol 8")
    return wire.read_text()


def private_runtime(work, c):
    """Instrument private copies; the repository's compiler/runtime is untouched."""
    for pkg in ("native", "numerical"):
        shutil.copytree(ROOT / "lean-kernel" / pkg,work / pkg,
                        ignore=shutil.ignore_patterns(".lake"))
    (work / "native/case.h").write_text(c_header(c))
    # Include the original storage in probe.c, not the copied wrapper recursively.
    (work / "native/storage.c").write_text(f'#include {json.dumps(str(HERE / "probe.c"))}\n')
    (work / "native/ffi.c").write_text((ROOT / "lean-kernel/native/ffi.c").read_text() + "\n" + (HERE / "ffi.c").read_text())
    instrument_gemm(ROOT / "lean-kernel/numerical/gemm.c",work / "numerical/gemm.c")
    for pkg in ("native", "numerical"):
        shutil.copyfile(HERE / "calls.h",work / pkg / "calls.h")
        path = work / pkg / "lakefile.lean"
        text = path.read_text().replace('"-std=c11", "-O3"',
            '"-std=c11", "-O3", "-fno-lto", ' + json.dumps("-I" + str(work / "native")) +
            ', ' + json.dumps("-I" + str(work / "numerical")) +
            ', ' + json.dumps("-I" + str(HERE)) +
            ', ' + json.dumps("-I" + str(work / "openblas_include")))
        path.write_text(text)


def build_case(runner, c, work, wire, prefix, cc, kernel, lean_root, frontend):
    env = dict(runner.env,VASTITAS_KERNEL=str(kernel),VASTITAS_KERNEL_ROOT=str(ROOT / "lean-kernel"))
    manifest = work / "package/Vastitas.toml"
    runner.run([frontend,"check","--manifest-path",manifest],env=env,phase="public_check_total")
    canonical = work / "canonical-program"
    runner.run([frontend,"build","--manifest-path",manifest,"--openblas-prefix",prefix,
                "--native-cc",cc[0],"-o",canonical],env=env,phase="public_build_total")
    result = runner.run([canonical],phase="canonical_execution_validation")
    if result["stdout"].strip() != "0":
        raise ValueError("canonical executable did not return the checked pure result")
    result = runner.run([kernel,"check"],input=wire,phase="independent_lean_check")
    if not json.loads(result["stdout"]).get("ok"):
        raise ValueError("independent Lean rejection")
    result = runner.run([kernel,"emit"],input=wire,phase="independent_lean_emit")
    response = json.loads(result["stdout"])
    dump(work / "response.json",response)
    if response.get("version") != 8 or not response.get("ok") or not response.get("numerical_runtime"):
        raise ValueError("not a checked public numerical response")
    generated = response["lean_source"]
    (work / "Generated.lean").write_text(generated)
    (work / "Main.lean").write_text(driver(generated))
    private_runtime(work,c)
    (work / "openblas_include").symlink_to(prefix / "include",target_is_directory=True)
    (work / "lean-toolchain").write_text((ROOT / "lean-kernel/lean-toolchain").read_text())
    (work / "lakefile.lean").write_text(f'''import Lake
open Lake DSL
package tree_benchmark where
  moreLinkArgs := #["-fno-lto", "-L", {json.dumps(str(lean_root / 'lib'))}]
require vastitas_kernel from {json.dumps(str(ROOT / 'lean-kernel'))}
require vastitas_gemm_native from "./numerical" with
  NameMap.empty.insert `openblas {json.dumps(str(prefix))}
lean_exe bench where
  root := `Main
  moreLeancArgs := #["-O3", "-fno-lto"]
''')
    env = dict(runner.env,LEAN_CC=cc[0])
    runner.run(["lake","build","bench"],cwd=work,env=env,phase="generated_native_compile")
    exe = work / ".lake/build/bin/bench"
    for name,command in {"symbols.txt":["nm", "-S",exe], "disassembly.txt":["objdump","-d",exe],
                        "linked-libraries.txt":(["otool","-L",exe] if sys.platform == "darwin" else ["ldd",exe])}.items():
        runner.run(command,required=False,phase="inspection",stdout_path=work / name)
    return exe


def measure(runner, c, exe, samples, target_ms, rows, raw, index):
    def pair(scope, phase, pair_id, reps, first, verify=False):
        found = {}
        for order,impl in enumerate([first,"c" if first == "generated" else "generated"]):
            result = runner.run([exe,impl,scope,reps,int(verify)],phase="runtime_validation" if verify else phase)
            record = json.loads(result["stdout"])
            found[impl] = record
            if not verify:
                row = dict(case=c["case"],scope=SCOPES[scope],phase=phase,pair=pair_id,order=order,implementation=impl,**record)
                rows.append(row)
                if raw.tell() == 0:
                    csv.DictWriter(raw,fieldnames=list(row)).writeheader()
                csv.DictWriter(raw,fieldnames=list(row)).writerow(row); raw.flush()
        compare_pair(found["generated"],found["c"])
        return min(v["elapsed_ns"] for v in found.values())
    for scope in range(len(SCOPES)):
        pair(scope,"verification",0,1,"generated",True)
        for i in range(2): pair(scope,"warmup",i,3,"generated" if i % 2 == 0 else "c")
        reps = 1
        for attempt in range(16):
            elapsed = pair(scope,"calibration",attempt,reps,"generated" if attempt % 2 == 0 else "c")
            if elapsed >= target_ms*1e6 or reps >= 1000000:
                break
            reps = min(1000000,max(reps+1,min(reps*8,int(reps*target_ms*1e6/max(elapsed,1)*1.2))))
        for i in range(samples):
            pair(scope,"measurement",i,reps,"generated" if (index+i) % 2 == 0 else "c")
        pair(scope,"verification",1,1,"c",True)


def summarize(rows,out):
    # Reuse medians/IQR/MAD, paired ratios/deltas and paired bootstrap from #283.
    renamed = [{**r,"implementation":"adapter" if r["implementation"] == "generated" else "c"} for r in rows]
    copy_experiment.summarize(renamed,out)
    text = (out / "summary.md").read_text().replace("# C storage-copy measurements","# Two-edge contraction-tree measurements")
    text = text.replace("All scopes are C only. Lifecycle is primary; the other scopes exclude common work.",
        "Lifecycle is the emitted public resource program; reused_buffers includes four FFI calls and physical preflight. The four primitive diagnostic scopes exclude FFI and time one selected pack/regroup/BLAS call, while executing the complete two-stage schedule.")
    text = text.replace("adapter/C","generated/C").replace("Adapter median","Generated median")
    (out / "summary.md").write_text(text)
    data = json.loads((out / "summary.json").read_text())
    for item in data:
        impl = item["implementations"]
        impl["generated"] = impl.pop("adapter")
        item["ratio_of_separate_medians"] = impl["generated"]["ns_per_operation"]["median"] / impl["c"]["ns_per_operation"]["median"]
        for name, values in impl.items():
            chosen = [r for r in rows if r["phase"] == "measurement" and r["case"] == item["case"]
                      and r["scope"] == item["scope"] and r["implementation"] == name]
            values["process_maxrss_kib"] = copy_experiment.distribution([r["process_maxrss_kib"] for r in chosen])
            values["peak_data_bytes"] = sorted({r["peak_data_bytes"] for r in chosen})
            values["peak_metadata_bytes"] = sorted({r["peak_metadata_bytes"] for r in chosen})
    dump(out / "summary.json",data)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--prefix",type=Path,required=True)
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--frontend",type=Path,default=ROOT / "target/release/vastitas")
    p.add_argument("--cc",default=os.environ.get("CC","cc"))
    p.add_argument("--samples",type=int,default=11)
    p.add_argument("--target-ms",type=float,default=5)
    p.add_argument("--smoke",action="store_true")
    p.add_argument("--cpu",type=int)
    p.add_argument("--no-leak-sanitizer",action="store_true")
    p.add_argument("--kernel",type=Path,default=ROOT / "lean-kernel/.lake/build/bin/vastitas-kernel")
    args = p.parse_args()
    if not (sys.platform.startswith("linux") or sys.platform == "darwin"):
        p.error("supported hosts are Linux and macOS")
    if sys.platform == "darwin" and not args.no_leak_sanitizer:
        p.error("Apple ASan has no LeakSanitizer; pass --no-leak-sanitizer explicitly")
    if not 3 <= args.samples <= 1000 or not 0 < args.target_ms <= 1000:
        p.error("samples 3..1000; target-ms (0,1000]")
    cc = shlex.split(args.cc)
    if len(cc) != 1:
        p.error("--cc must be a single compiler executable (also used for LEAN_CC)")
    out,prefix,frontend = args.output.resolve(),args.prefix.resolve(),args.frontend.resolve()
    out.mkdir(parents=True,exist_ok=False)
    env = dict(os.environ,OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1",GOTO_NUM_THREADS="1")
    allowed = sorted(os.sched_getaffinity(0)) if hasattr(os,"sched_getaffinity") else []
    cpu = (allowed[0] if args.cpu is None else args.cpu) if allowed else None
    if allowed:
        os.sched_setaffinity(0,{cpu})
    elif args.cpu is not None:
        p.error("CPU affinity is not available on this host")
    runner = Runner(out,env)
    all_cases = cases(args.smoke)
    dump(out / "cases.json",all_cases)
    environment = dict(started_utc=dt.datetime.now(dt.timezone.utc).isoformat(),argv=sys.argv,
        platform=platform.platform(),python=sys.version,cpu_affinity_before=allowed,cpu=cpu,flags=FLAGS,
        policy="NativeFast",threads=1,source_sha256={},toolchains={},host={},
        performance="unmeasured",leak_sanitizer="disabled explicitly" if args.no_leak_sanitizer else "enabled",
        memory_scope="exact arena data counters; ru_maxrss may include launcher pre-exec footprint and is not isolated executable heap; BLAS private packing/allocations not instrumented")
    environment["expected_lean_toolchain"] = (ROOT / "lean-kernel/lean-toolchain").read_text().strip()
    for rel in ["experiments/contraction_trees", "experiments/storage_copy/run.py", "lean-kernel/native", "lean-kernel/numerical",
                "lean-kernel/VastitasKernel/TensorNumerical.lean",
                "lean-kernel/VastitasKernel/TensorContraction.lean",
                "lean-kernel/VastitasKernel/TensorTree.lean",
                "lean-kernel/VastitasKernel/StorageTensorLayout.lean",
                "lean-kernel/VastitasKernel/StorageFunctions.lean",
                "lean-kernel/VastitasKernel/Storage.lean",
                "lean-kernel/VastitasKernel/StorageProtocol.lean",
                "lean-kernel/VastitasKernel/ResourceSource.lean",
                "lean-kernel/VastitasKernel/ResourceProtocol.lean",
                "lean-kernel/VastitasKernel/ResourceCodegen.lean",
                "src/frontend/resource_parser.rs", "src/storage.rs",
                "lean-kernel/VastitasKernel/StorageCodegen.lean"]:
        path = ROOT / rel
        files = [path] if path.is_file() else path.rglob("*")
        for f in files:
            if f.is_file() and not any(x in f.parts for x in (".lake","__pycache__","results")):
                r = f.relative_to(ROOT); target = out / "source" / r
                target.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(f,target)
                environment["source_sha256"][str(r)] = sha(f)
    for f in [prefix / "lib/libopenblas.a",prefix / "include/cblas.h",prefix / "include/openblas_config.h",frontend,args.kernel.resolve()]:
        if f.exists(): environment["source_sha256"][str(f)] = sha(f)
    if (prefix / "vastitas-openblas.json").exists():
        shutil.copyfile(prefix / "vastitas-openblas.json",out / "openblas-build.json")
    for name,cmd in {"cc":cc+["--version"],"rustc":["rustc","--version"],"cargo":["cargo","--version"],
                     "lean":["lean","--version"],"lake":["lake","--version"],"git":["git","rev-parse","HEAD"],
                     "git_status":["git","status","--short"],"cpu":(["sysctl","-n","machdep.cpu.brand_string"] if sys.platform == "darwin" else ["lscpu"]),"libc":(["sw_vers"] if sys.platform == "darwin" else ["ldd","--version"])}.items():
        environment["toolchains"][name] = runner.run(cmd,required=False,phase="environment")
    for name in ("/proc/loadavg","/sys/fs/cgroup/cpu.max","/sys/fs/cgroup/memory.max","/sys/fs/cgroup/cpu.stat"):
        if Path(name).exists(): environment["host"][name] = Path(name).read_text()
    dump(out / "environment.json",environment)
    dump(out / "status.json",dict(performance="unmeasured",status="in_progress"))
    try:
        if not frontend.is_file() or not args.kernel.is_file():
            raise ValueError("Build the frontend and kernel first; see README")
        # Require standalone correctness and sanitizer checks before generated timing.
        validation = []
        for c in all_cases:
            work = out / "cases" / c["case"]
            write_package(c,work / "package")
            capture_wire(runner,frontend,work / "package")
            validation.append(native_test(runner,c,work / "native-test",prefix,cc,False,args.no_leak_sanitizer))
            validation.append(native_test(runner,c,work / "sanitized",prefix,cc,True,args.no_leak_sanitizer))
            dump(out / "native-validation.json",validation)
            print(f"{c['case']}: frontend capture and native correctness passed",flush=True)
        if "version 4.35.0" not in environment["toolchains"]["lean"]["stdout"]:
            raise ValueError("this experiment requires the repository-pinned Lean 4.35.0")
        kernel = args.kernel.resolve()
        lean_root = Path(runner.run(["lean","--print-prefix"])["stdout"].strip())
        rows = []
        with (out / "raw.csv").open("w",newline="") as raw:
            for i,c in enumerate(all_cases):
                work = out / "cases" / c["case"]
                wire = (work / "package/wire.json").read_text()
                started = time.perf_counter()
                print(f"[{i+1}/{len(all_cases)}] {c['case']}: public check/build and wrapper compilation",flush=True)
                exe = build_case(runner,c,work,wire,prefix,cc,kernel,lean_root,frontend)
                built = time.perf_counter()
                print(f"[{i+1}/{len(all_cases)}] {c['case']}: generated validation/compilation passed in {built-started:.1f}s; paired scopes",flush=True)
                measure(runner,c,exe,args.samples,args.target_ms,rows,raw,i)
                print(f"[{i+1}/{len(all_cases)}] {c['case']}: all paired scopes passed in {time.perf_counter()-built:.1f}s",flush=True)
        summarize(rows,out)
        verify_inputs(environment["source_sha256"])
        environment["recorded_inputs_unchanged"] = True
        environment["performance"] = "smoke only" if args.smoke else "exploratory measurements on this host; not controlled-host acceptance"
        dump(out / "status.json",dict(status="passed",performance=environment["performance"],rows=len(rows)))
    except Exception as error:
        dump(out / "status.json",dict(status="failed",performance="unmeasured",reason=str(error)))
        raise
    finally:
        environment["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        if Path("/proc/loadavg").exists(): environment["host"]["loadavg_after"] = Path("/proc/loadavg").read_text()
        dump(out / "environment.json",environment)
        dump(out / "compile-times.json",[r for r in runner.commands if any(x in r["phase"] for x in ("compile","check","capture","build","emit"))])


if __name__ == "__main__":
    main()
