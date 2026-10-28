#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
lake -d lean-kernel build VastitasKernel.IndexedCoreRegression VastitasKernel.IndexedCodegen VastitasKernel.IndexedRuntime:c.o
(cd lean-kernel && lake env lean --run ../scripts/check_indexed_codegen.lean "$work")
# Compile the runtime and generated modules directly. No compiler, oracle or
# mathlib module is present in the executable dependency graph.
for fixture in package primitives scalar; do
  (cd lean-kernel && lake env lean -R "$work" -c "$work/$fixture.c" "$work/$fixture.lean")
  (cd lean-kernel && lake env leanc "$work/$fixture.c" .lake/build/ir/VastitasKernel/IndexedRuntime.c.o.export -o "$work/$fixture")
  actual=$("$work/$fixture")
  case "$fixture" in
    package) expected=2 ;;
    primitives) expected=42 ;;
    scalar) expected=999999999999999999999999999999999999999997 ;;
  esac
  test "$actual" = "$expected" || { echo "$fixture: expected $expected, got $actual" >&2; exit 1; }
done
echo 'indexed Core: 3 standalone native fixtures passed'
