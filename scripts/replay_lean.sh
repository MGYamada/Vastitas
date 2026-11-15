#!/usr/bin/env bash
# Replay built Lean modules with the official kernel (`leanchecker`) under a
# bounded number of Lean worker threads.
#
# leanchecker replays each target module as a separate task, and each task
# loads that module's whole import environment. Lean runs the tasks on its
# worker pool, whose size is LEAN_NUM_THREADS, or the number of cores when the
# variable is unset. For modules that import Mathlib, every concurrent task
# holds its own copy of the environment, so an unset thread count exhausts
# memory on a 16 GiB machine (#600).
#
# leanchecker also treats every argument that starts with "-" as a flag. With
# no module argument it falls back to the current Lake package, and outside a
# package directory it replays every module on its search path. This script
# therefore requires explicit module names and accepts only `-v`.
#
# usage: scripts/replay_lean.sh <lake-package-dir> [-v] <Module> [<Module>...]
# VASTITAS_REPLAY_THREADS sets LEAN_NUM_THREADS; it defaults to 1.
#
# The replay runs under a resource timer, VASTITAS_REPLAY_TIME, which defaults
# to /usr/bin/time where that program exists; an empty value turns the timer
# off. The timer only reports. The exit status is the one that leanchecker
# records itself, so a timer that fails, such as `time -l` in a macOS sandbox
# that denies `sysctl kern.clockrate` (#798), neither fails a passing replay
# nor hides a failed one. When no status is recorded, the replay fails.
set -euo pipefail

usage() {
  echo "usage: $0 <lake-package-dir> [-v] <Module> [<Module>...]" >&2
  exit 2
}

[ $# -ge 2 ] || usage
package=$1
shift

flags=()
modules=()
for arg in "$@"; do
  case $arg in
    -v | --verbose) flags+=("-v") ;;
    -*)
      echo "replay_lean: unsupported flag '$arg'; leanchecker would ignore it" >&2
      exit 2
      ;;
    "") usage ;;
    *) modules+=("$arg") ;;
  esac
done
[ ${#modules[@]} -ge 1 ] || {
  echo "replay_lean: name at least one module; without one leanchecker replays far more" >&2
  exit 2
}

threads=${VASTITAS_REPLAY_THREADS:-1}
case $threads in
  '' | *[!0-9]* | 0)
    echo "replay_lean: VASTITAS_REPLAY_THREADS must be a positive integer" >&2
    exit 2
    ;;
esac

[ -f "$package/lakefile.toml" ] || [ -f "$package/lakefile.lean" ] || {
  echo "replay_lean: '$package' is not a Lake package directory" >&2
  exit 2
}
cd "$package"

time_program=/usr/bin/time
[ -x "$time_program" ] || time_program=
time_program=${VASTITAS_REPLAY_TIME-$time_program}
timer=()
if [ -n "$time_program" ]; then
  if [ "$(uname)" = Darwin ]; then timer=("$time_program" -l); else timer=("$time_program" -v); fi
fi

status_file=$(mktemp "${TMPDIR:-/tmp}/replay_lean.XXXXXX")
trap 'rm -f "$status_file"' EXIT

echo "replay_lean: leanchecker ${modules[*]} in $package with LEAN_NUM_THREADS=$threads"
timer_status=0
# shellcheck disable=SC2016 # the inner shell expands "$@" and the status file
LEAN_NUM_THREADS=$threads REPLAY_STATUS_FILE=$status_file ${timer[@]+"${timer[@]}"} \
  /bin/sh -c 'lake env leanchecker "$@"; s=$?; echo "$s" > "$REPLAY_STATUS_FILE"; exit "$s"' replay_lean \
  ${flags[@]+"${flags[@]}"} "${modules[@]}" || timer_status=$?
status=$(cat "$status_file")
case $status in
  '' | *[!0-9]*)
    echo "replay_lean: leanchecker recorded no exit status (timer exit $timer_status)" >&2
    status=$timer_status
    [ "$status" -ne 0 ] || status=1
    ;;
  *)
    if [ "$timer_status" -ne "$status" ]; then
      echo "replay_lean: the resource timer exited $timer_status; the status is leanchecker's" >&2
    fi
    ;;
esac
if [ "$status" -ne 0 ]; then
  echo "replay_lean: exit $status; the replay is not verified" >&2
fi
exit "$status"
