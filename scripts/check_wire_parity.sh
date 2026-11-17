#!/usr/bin/env bash
# old-route(#533): the development-only wire parity check of #533, round 1
# (W2) and round 2 (W6, W7), removed with the routes that it compares at the
# cutover to epoch 10. It builds the kernel, writes the wire report and the
# request pairs of the corpus (tests/wire_parity.rs): the request that the
# frontend writes and the one that it wrote before round 2. It then compares
# the checked Core and the namespace work of each pair
# (scripts/wire_parity.lean). Both reports go to the directory, by default
# target/tmp/wire-parity: report.txt (wire) and core.txt (Core).
# Usage: bash scripts/check_wire_parity.sh [directory]
set -euo pipefail
cd "$(dirname "$0")/.."
directory=${1:-target/tmp/wire-parity}
mkdir -p "$directory"
directory=$(cd "$directory" && pwd)
lake -d lean-kernel build vastitas-kernel
VASTITAS_WIRE_PARITY_DIR="$directory" \
  cargo test --locked --test wire_parity wire_parity_report -- --exact --nocapture
cd lean-kernel
lake env lean -DwarningAsError=true --run ../scripts/wire_parity.lean "$directory"
