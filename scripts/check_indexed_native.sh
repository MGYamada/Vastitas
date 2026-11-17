#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../lean-kernel"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
lake build \
  VastitasKernel.IndexedCoreRegression \
  VastitasKernel.IndexedPackageSemanticRegression \
  VastitasKernel.IndexedSourceRegression \
  VastitasKernel.IndexedSourceTypeRegression \
  VastitasKernel.IndexedSourceBodyRegression \
  VastitasKernel.IndexedFunctionRegression \
  VastitasKernel.IndexedDispatchRegression \
  VastitasKernel.IndexedAuthorityRegression \
  VastitasKernel.SmoothObjectRegression \
  VastitasKernel.CotangentRegression \
  VastitasKernel.MetricFormRegression \
  VastitasKernel.ReverseCoreRegression \
  VastitasKernel.FrameRegression \
  VastitasKernel.SpectralRegression \
  VastitasKernel.AverageRegression \
  VastitasKernel.IndexedCodegen \
  VastitasKernel.IndexedRuntime:c.o \
  VastitasKernel.AlgebraRuntime:c.o \
  VastitasKernel.SmoothRuntime:c.o \
  VastitasKernel.FrameRuntime:c.o \
  VastitasKernel.SpectralRuntime:c.o
lake env lean --run ../scripts/check_indexed_codegen.lean "$work"

# Each worker links its own generated module with only the runtime objects that
# module imports. SmoothRuntime imports AlgebraRuntime, FrameRuntime imports
# SmoothRuntime, and SpectralRuntime imports FrameRuntime, so each also links
# the runtimes it imports.
lake env xargs -n 2 -P 4 bash -euc '
  work=$1
  fixture=$2
  expected=$3
  runtime=.lake/build/ir/VastitasKernel
  objects=("$runtime/IndexedRuntime.c.o.export")
  spectral=false
  frame=false
  smooth=false
  if grep -q "^import VastitasKernel.SpectralRuntime$" "$work/$fixture.lean"; then spectral=true; fi
  if $spectral || grep -q "^import VastitasKernel.FrameRuntime$" "$work/$fixture.lean"; then frame=true; fi
  if $frame || grep -q "^import VastitasKernel.SmoothRuntime$" "$work/$fixture.lean"; then smooth=true; fi
  if $smooth || grep -q "^import VastitasKernel.AlgebraRuntime$" "$work/$fixture.lean"; then
    objects+=("$runtime/AlgebraRuntime.c.o.export")
  fi
  if $smooth; then objects+=("$runtime/SmoothRuntime.c.o.export"); fi
  if $frame; then objects+=("$runtime/FrameRuntime.c.o.export"); fi
  if $spectral; then objects+=("$runtime/SpectralRuntime.c.o.export"); fi
  case "$fixture:${#objects[@]}" in
    spectral_*:5) ;;
    spectral_*:*) echo "$fixture: expected the algebra, smooth, frame and spectral runtimes" >&2; exit 1 ;;
    frame_*:4) ;;
    frame_*:*) echo "$fixture: expected the algebra, smooth and frame runtimes" >&2; exit 1 ;;
    smooth_*:3) ;;
    smooth_*:*) echo "$fixture: expected the algebra and smooth runtimes" >&2; exit 1 ;;
    *:1) ;;
    *) echo "$fixture: a descriptor fixture imports an exact runtime" >&2; exit 1 ;;
  esac
  # The program exits with the result of main modulo 256 and writes nothing
  # on either stream (#836). A result outside 0..255 is also checked whole:
  # the program that observes it with `show!` writes `main = <result>` on
  # standard error, nothing on standard output, and exits with 0 (#840).
  lean -R "$work" -c "$work/$fixture.c" "$work/$fixture.lean"
  leanc "$work/$fixture.c" "${objects[@]}" -o "$work/$fixture"
  status=0
  actual=$("$work/$fixture" 2>&1) || status=$?
  wanted=$(python3 -c "import sys; print(int(sys.argv[1]) % 256)" "$expected")
  if [[ -n "$actual" || "$status" != "$wanted" ]]; then
    echo "$fixture: expected exit status $wanted and no output, got $status and \"$actual\"" >&2
    exit 1
  fi
  if [[ "$wanted" != "$expected" ]]; then
    lean -R "$work" -c "$work/${fixture}_shown.c" "$work/${fixture}_shown.lean"
    leanc "$work/${fixture}_shown.c" "${objects[@]}" -o "$work/${fixture}_shown"
    status=0
    actual=$("$work/${fixture}_shown" 2>&1 >"$work/${fixture}_shown.out") || status=$?
    if [[ "$actual" != "main = $expected" || -s "$work/${fixture}_shown.out" || "$status" != 0 ]]; then
      echo "$fixture: expected main = $expected on standard error only and exit status 0, got \"$actual\" and $status" >&2
      exit 1
    fi
  fi
' check-fixture "$work" <<'FIXTURES'
package 2
primitives 42
scalar 999999999999999999999999999999999999999997
global_witness 0
opened_object 41
multiple_fields 0
source_declarations 7
source_types 13
source_bodies 2
source_scalars 999999999999999999999999999999999999999997
source_fields 3
functions 42
function_objects 10
function_private 9
function_fields 3
dispatch 42
dispatch_contract 42
dispatch_nominal 17
dispatch_pair 1
authority 42
authority_transfer 42
authority_repaired 42
authority_empty 5
smooth_programs 42
smooth_cotangent_programs 42
smooth_metric_programs 42
smooth_reverse_programs 42
smooth_reverse_extended 42
frame_programs 42
spectral_programs 42
spectral_reverse_programs 42
spectral_average_programs 42
FIXTURES
echo 'indexed Core: all standalone native fixtures passed'
