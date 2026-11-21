#!/bin/bash
# selrun.sh OUT/  (shard A, 2026-11-16; UNTRUSTED search)
# After formal/tools/margin/run.sh BUILD.fasm OUT/ has run (it leaves net.json, bnd.json, arbs.json, routed.json and
# ref_dump.json in OUT/), sweep the races C's candidate list leaves out: late inputs of COMBINATIONAL LUTs one gate
# before storage (selrace.py; research's select-arrival race at the umux data LUTs is one of them). Same adversary,
# same rank.py, margin.py, checkrows.py and names.py as C's run.sh, unchanged; results in OUT/sel/ (kappa_hi.txt,
# checked.txt, names.txt, margins.txt). Knobs as run.sh: KERNEL, PAIRS, JOBS, KHI (0.45), KLO (0.20), W0, TFULL, SIM.
set -uo pipefail
O=$(cd "$1" && pwd); A=$(cd "$(dirname "$0")" && pwd); H=$(cd "$A/../../tools/margin" && pwd)
KHI=${KHI:-0.45}; KLO=${KLO:-0.20}; JOBS=${JOBS:-4}; W0=${W0:-0}; TOP=${TOP:-0}
for f in net.json bnd.json arbs.json ref_dump.json; do [ -f "$O/$f" ] || { echo "selrun: $O/$f missing (run run.sh first)"; exit 2; }; done
S="$O/sel"; mkdir -p "$S"
for f in net.json bnd.json arbs.json routed.json; do [ -f "$O/$f" ] && ln -sf "$O/$f" "$S/$f"; done
python3 "$A/selrace.py" "$S/net.json" "$S/bnd.json" "$S/races.json" ${DEPTH:+--depth $DEPTH} 2>&1 | tee "$S/run.log"
python3 "$H/rank.py" "$S/net.json" "$S/races.json" "$KHI" "$S/ranked.json" "$O/ref_dump.json"
[ -f "$O/simx" ] && export SIMX="$O/simx"
python3 "$H/margin.py" "$S/net.json" "$S/bnd.json" "$S/ranked.json" "$S" --jobs "$JOBS" --top "$TOP" --khi "$KHI" \
  --klo "$KLO" --tfull "${TFULL:-5000000}" --pairs $PAIRS --kernel "$KERNEL" --w 20 $([ "$W0" = 1 ] && echo --w0) \
  --arbs "$S/arbs.json" 2>&1 | tail -5 | tee -a "$S/run.log"
python3 "$H/checkrows.py" "$S" > /dev/null 2>&1 || true
[ -f "$S/routed.json" ] && python3 "$H/names.py" "$S" > /dev/null 2>&1 || true
echo "selrun: done: $S/kappa_hi.txt $S/checked.txt $S/names.txt" | tee -a "$S/run.log"
