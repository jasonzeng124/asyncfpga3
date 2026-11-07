#!/usr/bin/env bash
# flock-based semaphore: run "$@" holding one of $FORMAL_SLOTS slots.
# Every lean/lake process in formal/ goes through this.
#   formal/slot.sh lake env lean Formal/Core/Trace.lean
# Default slots: min(nproc-1, (MemTotal GB - 2) / 4), at least 1.
# A Lean process importing Mathlib uses roughly 2-4 GB.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
if [ -z "${FORMAL_SLOTS:-}" ]; then
  mem=$(awk '/MemTotal/{print int($2/1048576)}' /proc/meminfo)
  c=$(( $(nproc) - 1 )); m=$(( (mem - 2) / 4 ))
  FORMAL_SLOTS=$(( c < m ? c : m )); [ "$FORMAL_SLOTS" -ge 1 ] || FORMAL_SLOTS=1
fi
LOCKDIR="${FORMAL_SLOT_DIR:-/tmp/formal-slots}"
mkdir -p "$LOCKDIR"
waited=0
while :; do
  for i in $(seq 1 "$FORMAL_SLOTS"); do
    exec {fd}>"$LOCKDIR/slot$i"
    if flock -n "$fd"; then
      [ "$waited" -gt 0 ] && echo "[slot] got slot $i after ${waited}s" >&2
      cd "${FORMAL_SLOT_CWD:-$HERE/lean}" 2>/dev/null || true
      # Run with the lock held; the child inherits fd, released on exit.
      "$@"; rc=$?
      exec {fd}>&-
      exit $rc
    fi
    exec {fd}>&-
  done
  sleep 2; waited=$((waited+2))
done
