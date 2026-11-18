#!/bin/sh
# Gate-level vs stage-level liveness on the real cells: writes RESULTS.md here.
# QUICK=1 for a smaller sweep (S <= 9).
set -e
cd "$(dirname "$0")"
exec python3 -B run.py "$@"
