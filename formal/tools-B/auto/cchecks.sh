#!/usr/bin/env bash
# tools-B/auto/cchecks.sh DIR SEED0 STEPSRX NRX  (shard B, UNTRUSTED simulation): B5's full-range checks on a decoded collatz
# bench build (DIR/m): c32hi (31-bit trajectories; the decoded kernel boundary carries all 32 bits, the bench's 16-bit mask
# is outside it) 8 draws; the steps counter preloaded at 0x3ffffff0 through ulink_n7 (c32hi + col18 without n = 1) 8 draws;
# slack of the steps counter's carry into bit 16 (STEPSRX, e.g. 'uaddi1\..*slice\[4\]\.genblk1\.carry4$') in the LAST
# increment (n = 0x10000: 16 steps -> 0x40000000); slack of the 3n+1 carry into bit 28 (NRX) on c32hi. A slack is found by
# bisection; a failure at the top of the bisection is the negative control (the path is reached). Summary DIR/cchecks.txt.
set -uo pipefail
D=$1; S0=$2; SRX=$3; NRX=$4; F=$(cd "$(dirname "$0")/../.." && pwd); P=$F/tools-B/preload; O=$D/m; S=$D/cchecks.txt; : > "$S"
R=${RS:-/home/user/rs}; export TMPDIR=$D
HI=$(awk '{printf "0x%s,0x%s ", $1, $1}' "$P/vec/c32hi.hex")
C18=$(awk '$1!="00000001"{printf "0x%s,0x%s ", $1, $1}' "$R/research/data/eventgraph/gate/col18.hex")
echo "c32hi: $(python3 "$F/tools/margin/draws.py" "$O/net.json" "$O/bnd.json" "$D/hi" --kernel collatz --pairs $HI --draws 8 --seed0 $S0 \
  --jobs 4 --routed "$O/routed.json" --tmax 400000000 2>&1 | grep '^draws')" | tee -a "$S"
echo "steps preloaded 0x3ffffff0: $(KERNEL=collatz "$P/prun.sh" "$O" "$D/pre" 0x3ffffff0 ulink_n7 "$HI $C18" 8 $S0 4 2>&1 | grep '^draws')" | tee -a "$S"
KERNEL=collatz "$P/carryslack.sh" "$O" "$D/cs_steps" collatz 0x3ffffff0 ulink_n7 "0x10000,0x10000" "$SRX" $S0 4 ${HI_STEPS:-40000} | tail -1 | sed 's/^/steps carry (last increment): /' | tee -a "$S"
"$P/carryslack.sh" "$O" "$D/cs_n" collatz - - "$HI" "$NRX" $S0 4 ${HI_N:-40000} | tail -1 | sed 's/^/3n+1 carry into bit 28: /' | tee -a "$S"
