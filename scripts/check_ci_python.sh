#!/usr/bin/env bash
# Hosted CPython embeds its toolcache lib directory in RUNPATH. setup-python
# additionally exports that directory as LD_LIBRARY_PATH; remove only that
# known override before native calibration, whose environment audit stays strict.
set -euo pipefail
: "${GITHUB_ENV:?CI environment file is required}"
: "${pythonLocation:?setup-python must run first}"
if [[ -n "${LD_LIBRARY_PATH:-}" && "$LD_LIBRARY_PATH" != "$pythonLocation/lib" ]]; then
  echo 'unexpected loader override before CI Python validation' >&2
  exit 1
fi
env -u LD_LIBRARY_PATH python3 --version
printf '%s\n' 'LD_LIBRARY_PATH=' >> "$GITHUB_ENV"
