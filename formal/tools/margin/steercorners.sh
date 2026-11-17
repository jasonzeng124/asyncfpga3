#!/bin/bash
# steercorners.sh OUT KERNEL VECHEX "BANDS..." CONDREGEX...   (shard C, 2026-11-17; UNTRUSTED simulation)
# Settle margin of each named loop condition at the steers reading it (steermargin.py), at each band triple chains,rest,carry.
#   OUT     a run.sh output directory (net.simx, simx, gclass.txt, routed.json; decode once with run.sh DRAWS=1 ...)
#   VECHEX  "a b" hex pairs per line (research's gate .hex format)
#   BANDS   e.g. "corners8" (chains, rest in {.20,.31} x CARRY/F7 in {.20,1.0}) or explicit "0.20,0.31,1.0 0.20,0.31,0.6"
#   CONDREGEX  the compare's output LUT, e.g. 'ucmpi0\.uz_n3$'
# Prints one line per (condition, bands): RESULT, the smallest settle gap (ps) and its steer, and the number of runts
# (requests under which the condition moved). A long-vector run dumps every node's flips: keep memory free (~4 GB).
set -uo pipefail
O=$1; K=$2; V=$3; B=$4; shift 4
H="$(cd "$(dirname "$0")" && pwd)"
[ "$B" = corners8 ] && B="0.20,0.20,0.20 0.20,0.20,1.0 0.20,0.31,0.20 0.20,0.31,1.0 0.31,0.20,0.20 0.31,0.20,1.0 0.31,0.31,0.20 0.31,0.31,1.0"
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' "$V")
for b in $B; do for c in "$@"; do
  python3 "$H/steermargin.py" "$O" "$c" --kernel "$K" --pairs $PAIRS --bands "$b" 2>&1 | python3 -c '
import re, sys
L = sys.stdin.read().splitlines(); res = L[0].split(":", 1)[-1].strip()[:24] if L else "no output"
best = None; runts = 0; rows = 0
for l in L[1:]:
    m = re.search(r"(\d+) with the condition moving under them; smallest settle gaps \[([-\d, ]*)\]", l)
    if not m: continue
    rows += 1; runts += int(m.group(1)); g = [int(x) for x in m.group(2).split(",") if x.strip()]
    if g and (best is None or g[0] < best[0]): best = (g[0], l.split(" pin")[0].replace("bridge_i.udut.", ""))
print("%s bands %s | %s | min gap %s ps at %s | runts %d%s" % (sys.argv[1], sys.argv[2], res, best[0] if best else "-",
      best[1] if best else "-", runts, "" if rows else " | NO ROWS (killed? out of memory?)"))
' "$c" "$b"
done; done
