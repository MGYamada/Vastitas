#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_storage_native.py
python3 scripts/check_ffi_result.py
