#!/usr/bin/env bash
# auto_rewrites.sh IN.mlir OUT.mlir [--bdc BDCDIR]
# Every loop-test rewrite formal has as a PASS, applied to any kernel, each kept only when Lean proves it:
#   1. plain_pass.py  (pre_dec, plain form: `i + 1 < n` -> `i < n - 1`; PlainPass certificate, Lean)
#   2. eq2_pass.py    (the test on the update -> the test on the value; scripts of proved local steps, Lean)
# Structure only: no kernel names, no file hashes. OUT = IN where nothing is proved. Exit 0 always on a clean run;
# the log line per pass says PROVED / refused / no match. Needs formal/setup.sh (Lean; the checked modules import
# no Mathlib).
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
IN=$1; OUT=$2; shift 2
MID=$(mktemp --suffix=.mlir)
python3 "$HERE/plain_pass.py" "$IN" "$MID" "$@" | tail -1
python3 "$HERE/eq2_pass.py" "$MID" "$OUT" "$@" | tail -1
rm -f "$MID"
