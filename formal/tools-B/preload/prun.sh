#!/usr/bin/env bash
# tools-B/preload/prun.sh BASE_OUT OUT I0 LINK "PAIRS" DRAWS SEED0 [JOBS]   (shard B, UNTRUSTED)
# BASE_OUT: a margin/run.sh output dir of the build (net.json, bnd.json, routed.json from its decode).
# Preloads LINK's latches with I0 (preload_net.py, checked constant in an ordinary run when BASE_OUT/ref_dump.json
# exists), then runs shard C's draws.py with the oracle from the same state (pdraws.py). Env DRAW_XBAND passes through;
# TMAX (ps, default 4e8) bounds simulated time. KERNEL (default xorshift) selects the kernel and its oracle. DRAWS_EXTRA is appended to draws.py's arguments (e.g. "--inject I.json": extra delay on named arcs, a negative control).
set -euo pipefail
B=$1; O=$2; I0=$3; LINK=$4; PAIRS=$5; N=$6; S0=$7; J=${8:-2}
H=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$O"
python3 "$H/preload_net.py" "$B/net.json" "$B/routed.json" "$O/net.json" --link "$LINK" --value "$I0" \
  $([ -f "$B/ref_dump.json" ] && echo --dump "$B/ref_dump.json")
cp "$B/bnd.json" "$O/bnd.json"
echo "$PAIRS" > "$O/pairs.txt"; echo "$I0 $LINK" > "$O/preload.txt"
PRELOAD_I0=$I0 python3 "$H/pdraws.py" "$O/net.json" "$O/bnd.json" "$O" --kernel "${KERNEL:-xorshift}" --pairs $PAIRS --draws "$N" \
  --seed0 "$S0" --jobs "$J" --routed "$B/routed.json" --tmax "${TMAX:-400000000}" ${DRAWS_EXTRA:-} 2>&1 | grep -E "^draws|^last|seed [0-9]+ (FAIL|UND)"
