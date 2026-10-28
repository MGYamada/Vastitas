#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/experiments/iterator_prefix"
lean -o "$work/experiments/iterator_prefix/FinitePrefixDraft.olean" experiments/iterator_prefix/FinitePrefixDraft.lean
LEAN_PATH="$work" lean experiments/iterator_prefix/Audit.lean
