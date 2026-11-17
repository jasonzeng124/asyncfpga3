#!/usr/bin/env bash
# tools-B/preload/carryslack.sh BASE_OUT OUT KERNEL I0|- LINK|- "PAIRS" CELLREGEX SEED0 NDRAWS [HI]   (shard B, UNTRUSTED)
# Consequence slack of a carry chain's high part: the largest extra delay PS on the carry-in of the CARRY4 placed for
# the yosys cell matching CELLREGEX (e.g. 'uaddi0\..*slice\[4\]\.genblk1\.carry4$') at which every one of NDRAWS
# draws (research's draw K from SEED0) still returns the right answers; bisection on [0, HI] (default 20000) to 50 ps.
# With I0 and LINK: preloaded runs (prun.sh, oracle from the same state); with "- -": ordinary draws (C's draws.py).
# An upper bound of the settle margin of the carry into that slice; an undecided run (event cap) counts as not passing.
set -euo pipefail
B=$1; O=$2; K=$3; I0=$4; LINK=$5; PAIRS=$6; RX=$7; S0=$8; ND=$9; HI=${10:-20000}
H=$(cd "$(dirname "$0")" && pwd); M=$(cd "$H/../../tools/margin" && pwd); mkdir -p "$O"
SL=$(python3 -c "
import json,re,sys
c=json.load(open('$B/routed.json'))['modules']['top']['cells']
m=[v['attributes']['NEXTPNR_BEL'].split('/')[0] for n,v in c.items() if re.search(r'''$RX''',n)]
assert len(m)==1, m; print(m[0])")
echo "carryslack: $RX at $SL, kernel $K, preload $I0 $LINK, draws $S0+$ND" | tee "$O/carryslack.txt"
ok() { python3 "$H/inject_carry.py" "$B/net.json" "$SL" "$1" "$O/inj$1.json"
  if [ "$I0" = "-" ]; then
    python3 "$M/draws.py" "$B/net.json" "$B/bnd.json" "$O/d$1" --kernel "$K" --pairs $PAIRS --draws "$ND" --seed0 "$S0" --jobs 4 \
      --routed "$B/routed.json" --tmax 400000000 --inject "$O/inj$1.json" 2>/dev/null | grep -q "FAIL 0 UNDECIDED 0"
  else
    DRAWS_EXTRA="--inject $O/inj$1.json" "$H/prun.sh" "$B" "$O/d$1" "$I0" "$LINK" "$PAIRS" "$ND" "$S0" 4 2>/dev/null | grep -q "FAIL 0 UNDECIDED 0"
  fi; }
ok "$HI" && { echo "no failure up to $HI ps" | tee -a "$O/carryslack.txt"; exit 0; }
lo=0; hi=$HI
ok 0 || { echo "fails with no injection" | tee -a "$O/carryslack.txt"; exit 0; }
while [ $((hi - lo)) -gt 50 ]; do m=$(((lo + hi) / 2)); if ok $m; then lo=$m; else hi=$m; fi; done
echo "slack >= $lo ps (all $ND draws pass), fails at $hi ps" | tee -a "$O/carryslack.txt"
