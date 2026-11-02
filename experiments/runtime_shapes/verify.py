#!/usr/bin/env python3
"""Independent retained-record arithmetic/hash audit; no compiler execution."""
if not __debug__:
    raise RuntimeError("verification requires Python assertions; remove -O / PYTHONOPTIMIZE")

import argparse
import hashlib
import json
from pathlib import Path
import struct
import zipfile

PROFILES = ("real-normal", "real-transpose", "complex-normal", "complex-transpose")
SHAPES = ((2,3,4,0), (3,5,2,2), (17,13,19,3), (0,3,4,1), (2,0,4,1), (2,3,0,1))
FAILURES = ((2147483648,3,4,1), (2**64,3,4,1), (2,3,4,2**63))


def word(value):
    return struct.unpack("<Q", struct.pack("<d", value))[0]


def expected(row):
    scalar = row["profile"].startswith("complex")
    transpose = row["profile"].endswith("transpose")
    m,k,n,pad,reps,scope = (row[x] for x in ("m","k","n","pad","repetitions","scope"))
    layouts = [(k,m,k+pad) if transpose else (m,k,m+pad), (k,n,k+pad), (m,n,m+pad)]
    capacities = [leading*columns for _,columns,leading in layouts]
    width = 16 if scalar else 8
    lives = 1 if scope else reps
    allocs = sum(bool(x) for x in capacities)*lives
    initialized = width*(m*k+k*n)*lives
    output = 2*width*m*n*reps
    hash_value = 1469598103934665603
    for ident,(rows,columns,leading) in enumerate(layouts):
        for index in range(leading*columns):
            for part in range(2 if scalar else 1):
                bits = 0x7ff8000000001357
                if index%leading < rows:
                    value = 1 if ident==0 else (-1 if part else 2) if ident==1 else k if part else (3 if scalar else 2)*k
                    bits = word(value)
                hash_value = ((hash_value ^ bits)*1099511628211) % 2**64
    return dict(checksum=f"{hash_value:016x}",data_allocations=allocs,data_frees=allocs,
                live_bytes=0,peak_data_bytes=width*sum(capacities),written_bytes=initialized+output,
                copied_bytes=0,metadata_allocations=2*lives,
                scope_data_allocations=0 if scope else allocs,scope_data_frees=0 if scope else allocs,
                scope_written_bytes=output if scope else initialized+output,scope_metadata_allocations=0 if scope else 2*lives,
                scope_guards=0 if scope else 6*reps,
                scope_nat_narrowings=9*reps if row["implementation"]=="generated" and not scope else 0,
                blas_calls=2*reps if m and k and n else 0)


def verify(read, names):
    info = json.loads(read("environment.json"))
    status = json.loads(read("status.json"))
    records = json.loads(read("records.json"))
    assert status == dict(status="passed",records=288,native=8,failures=12,performance="not measured"), status
    assert info["inputs_unchanged"] and len(records)==288
    scenario_fields=("profile","scope","repetitions","m","k","n","pad","implementation")
    assert all(type(row[x]) is int for row in records for x in scenario_fields[1:-1])
    assert all(type(row[x]) is str for row in records for x in ("profile","implementation"))
    actual_scenarios=[tuple(row[x] for x in scenario_fields) for row in records]
    expected_scenarios={(profile,scope,reps,*shape,implementation)
                        for profile in PROFILES for scope in (0,1)
                        for reps in (1,3,7) for shape in SHAPES
                        for implementation in ("generated","c")}
    assert len(set(actual_scenarios))==len(actual_scenarios)
    assert set(actual_scenarios)==expected_scenarios,"unsupported or missing recorded scenario"
    pairs = {}
    for row in records:
        for key,value in expected(row).items():
            assert row[key]==value,(key,row[key],value,row)
        # Arena/buffer descriptor sizes are reported native ABI facts, not
        # assumed portable constants. They must remain constant in this run.
        assert row["peak_metadata_bytes"]>0
        key=tuple(row[x] for x in ("profile","scope","repetitions","m","k","n","pad"))
        assert row["implementation"] not in pairs.setdefault(key,{})
        pairs[key][row["implementation"]]=row
    assert len(pairs)==144
    for values in pairs.values():
        a,b=values["generated"],values["c"]
        assert all(a[key]==b[key] for key in a if key not in ("implementation","scope_nat_narrowings"))
    assert len({r["peak_metadata_bytes"] for r in records})==1
    validation=json.loads(read("native-validation.json"))
    assert len(validation)==8 and sum(v["sanitizer"] for v in validation)==4
    assert all(type(v["sanitizer"]) is bool and type(v["scalar"]) is int and type(v["transpose"]) is int for v in validation)
    assert {(v["scalar"],v["transpose"],v["sanitizer"]) for v in validation}=={
        (scalar,transpose,sanitizer) for scalar in (0,1) for transpose in (0,1) for sanitizer in (False,True)}
    assert all(len(v["rows"])==12 for v in validation)
    for item in validation:
        native_scenarios=[]
        for raw in item["rows"]:
            row=dict(profile=("complex" if item["scalar"] else "real")+("-transpose" if item["transpose"] else "-normal"),implementation="c",scope=1 if raw["scope_data_allocations"]==0 else 0,**raw)
            # For zero-capacity cases scope is still determined by metadata.
            row["scope"]=0 if raw["scope_metadata_allocations"] else 1
            native_scenarios.append((row["scope"],row["repetitions"],*(row[x] for x in ("m","k","n","pad"))))
            for key,value in expected(row).items():assert row[key]==value,(key,row)
        assert set(native_scenarios)=={(scope,3,*shape) for scope in (0,1) for shape in SHAPES}
    failures=json.loads(read("failure-validation.json"))
    assert len(failures)==12
    assert all(type(x) is int for r in failures for x in r["dimensions"])
    assert {(r["profile"],tuple(r["dimensions"])) for r in failures}=={(profile,dimensions) for profile in PROFILES for dimensions in FAILURES}
    for result in failures:
        assert result["returncode"] and not result["stdout"] and "E_RUNTIME_" in result["stderr"]
        line=next(x for x in result["stderr"].splitlines() if x.startswith("AUDIT_FAILURE_CLEANUP "))
        assert json.loads(line.split(" ",1)[1])==dict(arenas=1,data_allocations=0,data_frees=0,live_bytes=0)
    commands=json.loads(read("commands.json"))
    assert sum(c["phase"]=="public_execution" and c["returncode"]==0 and c["stdout"].strip()=="0" for c in commands)==4
    assert sum(c["phase"]=="coordinate_cost_validation" and c["returncode"]==0 for c in commands)==48
    snapshots=0
    for path,digest in info["source_sha256"].items():
        if path.startswith("/"):continue
        assert hashlib.sha256(read("source/"+path)).hexdigest()==digest,path
        snapshots+=1
    for profile in ("real-normal","real-transpose","complex-normal","complex-transpose"):
        public=json.loads(read(profile+"/public-response.json"))
        actual=json.loads(read(profile+"/response.json"))
        emitted=read(profile+"/Generated.lean").decode()
        wrapped=read(profile+"/Main.lean").decode()
        assert public["ok"] and public["lean_source"].count("    VastitasGemmNative.gemm ")==4
        assert actual["ok"] and actual["lean_source"]==emitted
        assert emitted.count("    VastitasGemmNative.gemm ")==2
        assert "def generatedOnce (m k n pad : Nat)" in wrapped
        assert any(x.startswith(profile+"/") and x.endswith("/Main.c") for x in names)
    return dict(records=len(records),pairs=len(pairs),source_snapshots=snapshots,native=len(validation),failure_cleanup=len(failures),performance="not measured")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record",type=Path)
    args=parser.parse_args()
    if args.record.is_dir():
        print(json.dumps(verify(lambda name:(args.record/name).read_bytes(),[str(p.relative_to(args.record)) for p in args.record.rglob("*") if p.is_file()]),indent=2))
    else:
        with zipfile.ZipFile(args.record) as archive:
            assert len(archive.namelist())==len(set(archive.namelist()))
            assert all(not x.startswith("/") and ".." not in Path(x).parts for x in archive.namelist())
            print(json.dumps(verify(archive.read,archive.namelist()),indent=2))


if __name__=="__main__":main()
