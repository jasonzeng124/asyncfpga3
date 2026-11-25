#!/usr/bin/env bash
# tools-B/auto/xorchecks.sh DIR CARRYSLICE [NDRAWS] (shard B, UNTRUSTED simulation): B2's checks on a decoded xorshift bench
# build (DIR/m from decode.sh): research's xor19 draws (K 2101..), the loop counter preloaded at 0x3ffffff0 through the entry
# pipe ulink_n6 (set A, oracle from the same state), and the negative control (+20 ns on the carry-in of CARRYSLICE, the
# incrementer's bits 16-19): ordinary must pass, preloaded must fail. Summary in DIR/xorchecks.txt.
set -uo pipefail
D=$1; CS=$2; ND=${3:-4}; H=$(cd "$(dirname "$0")" && pwd); F=$(cd "$H/../.." && pwd); P=$F/tools-B/preload; O=$D/m
R=${RS:-$HOME/rs}; S=$D/xorchecks.txt; : > "$S"; export TMPDIR=$D
PAIRS=$(awk 'NF==2{printf "0x%s,0x%s ", $1, $2}' "$R/research/data/eventgraph/gate/xor19.hex")
JOBS=2 DRAWS=$ND DRAW_SEED0=2101 DRAW_MODEL=research HOSTDELAY=12000 KERNEL=xorshift PAIRS="$PAIRS" TFULL=400000000 BND=$O/bnd.json \
  bash "$F/tools/margin/run.sh" "$O/fromBit.fasm" "$O" > "$D/xor19.txt" 2>&1
echo "xor19 draws: $(grep -m1 '^draws' "$O/draws_summary.txt" 2>/dev/null || grep '^draws' "$D/xor19.txt" | tail -1)" | tee -a "$S"
P3="0x92d68ca2,0x3 0x9e3779b9,0x3 0x12345678,0x64"; W3=$(python3 "$F/tools/margin/kernels.py" xorshift $P3)
"$O/simx" "$O/net.simx" --want $W3 --hostdelay 12000 --pairs $P3 --kernel xorshift --corner 0 --data0 --full --R 400000 --su 1000 \
  --datachange broad --nextreq seq --tmax 40000000 --draw 2101 --gclass "$O/gclass.txt" --bands 0.25,0.25,0.6 --sreg 0.02 --w 20 \
  --dump "$O/ref_dump.json" 2>&1 | grep -o "RESULT [A-Z]*" | sed 's/^/ref run: /' | tee -a "$S"
PA="0x92d68ca2,0x3ffffff1 0x92d68ca2,0x3fffffff 0x92d68ca2,0x40000000 0x92d68ca2,0x40000001 0x13579bdf,0x40000001 0xdeadbeef,0x40000010 0x9e3779b9,0x40000002"
echo "preload A (i0 0x3ffffff0): $("$P/prun.sh" "$O" "$D/pa" 0x3ffffff0 ulink_n6 "$PA" $((2 * ND)) 2101 2 2>&1 | grep '^draws')" | tee -a "$S"
python3 "$P/inject_carry.py" "$O/net.json" "$CS" ${INJ_PS:-20000} "$D/inj.json"
echo "control, ordinary xor19 +20 ns at $CS: $(python3 "$F/tools/margin/draws.py" "$O/net.json" "$O/bnd.json" "$D/negA" --kernel xorshift \
  --pairs $PAIRS --draws 2 --seed0 2101 --jobs 2 --routed "$O/routed.json" --tmax 400000000 --inject "$D/inj.json" 2>&1 | grep '^draws')" | tee -a "$S"
echo "control, preloaded +20 ns at $CS: $(DRAWS_EXTRA="--inject $D/inj.json" "$P/prun.sh" "$O" "$D/negB" 0x3ffffff0 ulink_n6 "$PA" 2 2101 2 2>&1 | grep '^draws')" | tee -a "$S"
