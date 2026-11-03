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
  VastitasKernel.IndexedCodegen \
  VastitasKernel.IndexedRuntime:c.o
lake env lean --run ../scripts/check_indexed_codegen.lean "$work"

# Each worker links only its own generated module and the shared runtime object.
lake env xargs -n 2 -P 4 bash -euc '
  work=$1
  fixture=$2
  expected=$3
  lean -R "$work" -c "$work/$fixture.c" "$work/$fixture.lean"
  leanc "$work/$fixture.c" .lake/build/ir/VastitasKernel/IndexedRuntime.c.o.export -o "$work/$fixture"
  actual=$("$work/$fixture")
  if [[ "$actual" != "$expected" ]]; then
    echo "$fixture: expected $expected, got $actual" >&2
    exit 1
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
FIXTURES
echo 'indexed Core: all standalone native fixtures passed'
