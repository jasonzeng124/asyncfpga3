#!/usr/bin/env bash
# auto_size.sh LANE NAME KERNEL SEED VEC [MAXIT] -- BDC_AUTO=1 with its sizes chosen by the flow: nothing per kernel
# (PROGRAM "General first", owner 2026-11-17: no sizes file, no factor, no instance name).
#
#   iteration 0  build with every matched delay at bdc/emit.py's estimate (est_sizes.py: the kernel's own defaults);
#                corner_audit.py CA_SIZERULE=1 on that route proposes every line (the one sizing rule: chain and
#                LUT / wire at one band, CARRY4 / F7F8 / FF at SLOW_MAX, the measured-residual guards, a shortened line
#                priced at its own mean step, selects sized by rules E / M like any line).
#   iteration i  build with the sizes S_i, run the same rule on the new route.  The route is CLEAN when no sized kernel
#                constraint is below slack on it as built (negative_sized.tsv empty): ship it.  Otherwise
#                S_{i+1} = max(S_i, proposal_i) per line (ratchet.py) and route again.
#
# Why a loop: sizes belong to one route, and the route built from them is a different one (cells/hw/tighten_loop.sh's
# header: a 24-element line re-placed as 8 elements got 27 % cheaper per element, so a proposal priced on the long line
# under-delivers, in the short direction).  CA_SIZERULE prices a shortened line at its own mean step on purpose (the
# default price, the route's single cheapest hop, is the 1.6-2x term in research/data/sizerule/README.md), so this
# re-check of the route actually built is what makes it safe.  Why the ratchet: without it the loop oscillates
# (tighten_loop.sh, measured); with it the sizes are non-decreasing from the first proposal and bounded, so it ends.
# Every iteration is a full lane2.sh build (bits-decoded netlist, prjxray SDF, fid run, event-graph period P).
#
# Writes $RUNS/auto/NAME/{sizes_I.vh, it_I.txt, ca_I.txt, result.txt}.  result.txt: "CLEAN it=I route=NAME_I P=.."
# or "NOT CLEAN after MAXIT".  The shipped route's files are $RUNS/hw/NAME_I, $RUNS/r/NAME_I (lane2.sh).
set -uo pipefail
L=$1; N=$2; K=$3; S=$4; VEC=$5; MAXIT=${6:-4}
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}; export RUNS
LANE=$R/research/tools/fifteen/lane2.sh; T=$R/research/tools/auto
O=$RUNS/auto/$N; mkdir -p "$O"; : > "$O/result.txt"
D=${K}_bench_gen
rule() {   # rule I SIZES: corner_audit CA_SIZERULE=1 on route NAME_I as built with SIZES
  local i=$1 Z=$2 NI=${N}_$1; local HW=$RUNS/hw/$NI RD=$RUNS/r/$NI CA=$RUNS/ca/$NI
  rm -rf "$CA"; mkdir -p "$CA/seed1/pnr"
  ln -sf "$RD/xray.sdf" "$CA/seed1/pnr/soak_xray.sdf"; ln -sf "$HW/${D}_routed.json" "$CA/seed1/pnr/soak_routed.json"
  cp "$Z" "$CA/seed1/pnr/sizes.vh"
  CA_SIZERULE=1 python3 "$R/research/tools/corner_audit.py" "$CA/seed1" --prefix bridge_i.udut. --out "$CA/rule" \
      > "$O/ca_$i.txt" 2>&1
  [ -f "$CA/rule/sizes.vh" ] && [ -f "$CA/rule/negative_sized.tsv" ]
}
build() {  # build I SIZES
  local i=$1 Z=$2
  "$LANE" "$L" "${N}_$i" "$K" "$Z" "$S" "$VEC" BDC_AUTO=1 > "$O/it_$i.log" 2>&1
  tail -1 "$O/it_$i.log" > "$O/it_$i.txt"
  [ -f "$RUNS/r/${N}_$i/xray.sdf" ] && [ -f "$RUNS/hw/${N}_$i/${D}_routed.json" ]
}
echo "auto_size $N kernel $K seed $S maxit $MAXIT $(date -u +%FT%TZ) head $(git -C "$R" rev-parse --short HEAD)" > "$O/log.txt"
build 0 none || { echo "BUILD FAILED it=0" | tee -a "$O/result.txt"; exit 1; }
python3 "$T/est_sizes.py" "$RUNS/hw/${N}_0/${K}_kernel_bench.v" "$K" > "$O/sizes_0.vh" || { echo "NO ESTIMATES" >> "$O/result.txt"; exit 1; }
echo "it 0 $(cat "$O/it_0.txt") lines $(grep -c '^`define' "$O/sizes_0.vh")" >> "$O/log.txt"
rule 0 "$O/sizes_0.vh" || { echo "RULE FAILED it=0" | tee -a "$O/result.txt"; exit 1; }
cp "$RUNS/ca/${N}_0/rule/sizes.vh" "$O/sizes_1.vh"
echo "it 0 rule: $(grep -c . "$RUNS/ca/${N}_0/rule/negative_sized.tsv") negative rows (incl. header); $(grep '^proposal' "$O/ca_0.txt")" >> "$O/log.txt"
for i in $(seq 1 "$MAXIT"); do
  build "$i" "$O/sizes_$i.vh" || { echo "BUILD FAILED it=$i" | tee -a "$O/result.txt"; exit 1; }
  rule "$i" "$O/sizes_$i.vh" || { echo "RULE FAILED it=$i" | tee -a "$O/result.txt"; exit 1; }
  st=$(python3 "$T/ratchet.py" "$O/sizes_$i.vh" "$RUNS/ca/${N}_$i/rule/sizes.vh" "$RUNS/ca/${N}_$i/rule/negative_sized.tsv" \
       "$O/sizes_$((i + 1)).vh")
  echo "it $i $(cat "$O/it_$i.txt") | $(echo "$st" | head -1)" >> "$O/log.txt"
  echo "$st" > "$O/ratchet_$i.txt"
  neg=$(echo "$st" | head -1 | awk '{print $6}'); nr=$(echo "$st" | head -1 | awk '{print $2}')
  if [ "$neg" = 0 ]; then
    echo "CLEAN it=$i route=${N}_$i $(cat "$O/it_$i.txt")" | tee -a "$O/result.txt"; cp "$O/sizes_$i.vh" "$O/sizes_final.vh"; exit 0
  fi
  if [ "$nr" = 0 ]; then   # negative, but no line the rule could raise: the same sizes would give the same route
    echo "NOT CLEAN it=$i: $neg negative, none fixable by a line (route ${N}_$i)" | tee -a "$O/result.txt"; exit 3
  fi
done
echo "NOT CLEAN after $MAXIT (last route ${N}_$MAXIT; next sizes sizes_$((MAXIT + 1)).vh)" | tee -a "$O/result.txt"
exit 2
