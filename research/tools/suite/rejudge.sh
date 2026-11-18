#!/usr/bin/env bash
# rejudge.sh KERNEL SEED SIZES_VH [NDRAWS] -- rebuild an automatic route from the sizes its loop kept (sizes_final.vh,
# BDC_AUTO=1, the same seed: the same route, lane2.sh is deterministic) and judge it as suite_one.sh does (bits, draws
# K = 10000 + 100 * SEED + j, latency, LUTs).  For routes a farm run judged with an older checker (suite1 ran before
# fasm_equiv's GND-LUT false alarm was fixed, 745cb181a) or that it never simulated.  Prints suite_one.sh's result line.
set -uo pipefail
K=$1; S=$2; Z=$(readlink -f "$3"); ND=${4:-4}
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}; export RUNS
export PNR_TIMEOUT=${PNR_TIMEOUT:-3600}
O=$RUNS/suite/${K}_$S; mkdir -p "$O"; : > "$O/draws.txt"; D=${K}_bench_gen
case $K in
  xorshift) V=research/data/eventgraph/gate/xor19.hex; PV=research/data/fifteen/vec_xorshift.hex; OR="research/tools/fifteen/kernel_oracle.sh xorshift";;
  collatz) V=research/data/eventgraph/gate/col18.hex; PV=research/data/fifteen/vec_collatz.hex; OR="research/tools/fifteen/kernel_oracle.sh collatz";;
  collatz64) V=research/data/eventgraph/gate/c6419.hex; PV=research/data/fifteen/vec_c64_871.hex; OR="research/tools/fifteen/kernel_oracle.sh collatz64";;
  ipow) V=research/data/eventgraph/gate/ipow17.hex; PV=research/data/fifteen/vec_ipow.hex; OR="research/tools/fifteen/kernel_oracle.sh ipow";;
  isprime) V=research/data/alltable/isp17.hex; PV=research/data/suite/vec/isprime_period.hex; OR="research/tools/fifteen/kernel_oracle.sh isprime";;
  gcd) V=research/data/suite/vec/gcd8.hex; PV=research/data/suite/vec/gcd_period.hex; OR="research/data/gcd_draws/gcd_oracle.sh";;
  *) V=kernels/$K/vec.hex; PV=kernels/$K/period.hex; [ -f "$R/$PV" ] || PV=$V; OR="research/tools/suite/oracle.sh $K";;
esac
fin() { echo "$K $S $*" | tee "$O/result.txt"; exit 0; }
( cd "$R" && $OR < "$V" ) > "$O/exp.txt" 2> "$O/oracle.err" || fin "status=NO-ORACLE"
RT=rj_${K}_$S; HW=$RUNS/hw/$RT; RD=$RUNS/r/$RT
LINE=$("$R/research/tools/fifteen/lane2.sh" "rj_${K}_$S" "$RT" "$K" "$Z" "$S" "$R/$PV" BDC_AUTO=1 2>&1 | tail -1)
echo "$LINE" > "$O/rejudge_build.txt"
md5=$(echo "$LINE" | awk '{print $2}'); P=$(echo "$LINE" | grep -o 'P=[0-9A-Z]*' | cut -d= -f2)
eq=$(echo "$LINE" | grep -q 'NOT EQUIVALENT' && echo NOT-EQUIVALENT || (echo "$LINE" | grep -q 'EQUIVALENT' && echo EQUIVALENT || echo EQUIV?))
ff=$(echo "$LINE" | grep -q 'FFMUX-FLAG' && echo FFMUX-FLAG || echo ffmux-clean)
cp "$RD/fid/equiv.txt" "$O/equiv.txt" 2>/dev/null
luts=$(python3 -c "import json,sys; m=json.load(open(sys.argv[1]))['modules']; print(sum(1 for t in m.values() for c,v in t.get('cells',{}).items() if v['type']=='SLICE_LUTX' and 'udut' in c))" "$HW/${D}_routed.json" 2>/dev/null)
base="P=${P:-NA} luts=$luts sdf=$md5 rule=rejudged it=final bits=$eq $ff"
if [ "$eq" != EQUIVALENT ] || [ "$ff" != ffmux-clean ]; then fin "status=NOT-A-BOARD-ROUTE $base"; fi
pass=0
for j in $(seq 1 "$ND"); do
  k=$((10000 + 100 * S + j)); W=$RUNS/g/$RT/d$k; mkdir -p "$W"; cp "$RD/xray.sdf" "$W/xray.sdf"
  g=$("$R/research/tools/eventgraph/bench_gate.sh" "$HW" "$D" "$W" "$R/$V" "$O/exp.txt" "draw:$k" 2>&1 | tail -1)
  echo "draw $k $(cut -d' ' -f3-8 "$W/draw_$k.txt" 2>/dev/null) :: ${g:-none}" | tee -a "$O/draws.txt" > "$O/draw_$k.txt"
  grep '^BENCHRES' "$W/draw_$k/run.log" 2>/dev/null | sed 's/sig=[0-9a-f]* //' > "$O/benchres_$k.txt"
  echo "$g" | grep -q "^PASS " && pass=$((pass + 1)); rm -rf "$W/draw_$k"
done
st=PASS; [ "$pass" = "$ND" ] || st=FAIL
fin "status=$st draws=$pass/$ND $base"
