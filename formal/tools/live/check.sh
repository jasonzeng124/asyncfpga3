#!/bin/sh
# check.sh MLIR [MAX_STATES] -- formal's exhaustive liveness check of the circuit bdc emits for one handshake MLIR.
# Runs formal/tools/live/fixtures/live.py (model: fixtures/MODEL.md) under the BDC_* environment you run it with
# (BDC_AUTO, BDC_TOKEN_FLOOR, BDC_LINK_DEPTHS, ...), on research's bdc at LIVE_BDC_DIR (default: ../bdc of the
# checkout this script is in if it has one, else /home/user/rs/bdc). Prints one line and the result JSON (last line).
# Exit: 0 LIVE (every reachable state of the model searched, 1 invocation; LIVE_INV=2 for two back-to-back),
#       1 DEADLOCK (prints the condition choices that reach it and the token-free walk, in instance names),
#       2 not decided (state budget, crash, refused by emit).
# Untrusted: it is a model of the cells (FOR-RESEARCH C55-C59), not a proof; python3 only.
set -u
M=${1:?usage: check.sh MLIR [MAX_STATES]}
MAX=${2:-3000000}
HERE=$(cd "$(dirname "$0")" && pwd)
if [ -z "${LIVE_BDC_DIR:-}" ]; then
  if [ -f "$HERE/../../../bdc/emit.py" ]; then LIVE_BDC_DIR=$(cd "$HERE/../../../bdc" && pwd); else LIVE_BDC_DIR=/home/user/rs/bdc; fi
fi
export LIVE_BDC_DIR PYTHONDONTWRITEBYTECODE=1
J=$(python3 "$HERE/fixtures/live.py" "$M" --inv "${LIVE_INV:-1}" --max-states "$MAX" 2>/dev/null | grep '^{' | tail -1)
[ -n "$J" ] || { echo "live: CRASH (no result; run fixtures/live.py by hand for the error)"; exit 2; }
printf '%s\n' "$J" | python3 -c '
import json, sys
d = json.loads(sys.stdin.read())
v = d.get("verdict")
if v == "LIVE":
    print(f"live: LIVE, exhaustive, {d.get(\"states\")} states, {d.get(\"hazards\")} hazards, floor stages {d.get(\"token_floor\")}")
elif v == "DEADLOCK":
    print("live: DEADLOCK after conditions " + " ".join(d.get("trace_choices", [])) +
          "; token-free walk: " + " -> ".join(d.get("trap") or ["?"]))
else:
    print(f"live: {v} (not decided)")
'
printf '%s\n' "$J"
case "$J" in *'"verdict": "LIVE"'*) exit 0;; *'"verdict": "DEADLOCK"'*) exit 1;; *) exit 2;; esac
