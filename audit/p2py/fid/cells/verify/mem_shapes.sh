#!/usr/bin/env bash
# Elaborate every memory port/station shape bdc/mem.py can generate.
#
# tb_bdc_mem.v tests ONE shape (10-bit address, 32-bit word, 2 slots) and
# tests it properly -- oracle, edge count, setup and hold windows.  It cannot
# test the generator, and the generator is where the bugs have been:
#
#   .we(0'b0)            an f-string that produced a zero-width literal
#   24'h5A3C1E2D         32 bits of hex poured into a 24-bit seed
#
# Both are width-dependent and both elaborate-fail instantly, so the cheapest
# useful gate is to build every shape and see that yosys' front end accepts
# it.  Seconds to run.  This does NOT check behaviour; it checks that the
# generator's arithmetic about its own widths is self-consistent.
#
#   ./verify/mem_shapes.sh
#
# Nonzero exit means a shape failed to generate or failed to elaborate, and
# the offending width triple is named.
set -euo pipefail
cd "$(dirname "$0")/.."
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

ok=0; bad=0
for aw in 4 8 10; do
  for dw in 16 32 48 64; do
    for slots in 1 2 4; do
      f="$TMP/shape.v"
      if ! python3 ../bdc/mem.py "port:$aw:$dw:$slots" "store:$aw:$dw" \
           "load:$aw:$dw" -o "$f" > "$TMP/gen.log" 2>&1; then
        echo "GENERATE FAIL  aw=$aw dw=$dw slots=$slots"
        sed -n '1,6p' "$TMP/gen.log"
        bad=$((bad + 1)); continue
      fi
      if ! iverilog -g2012 -gspecify -Wall -Wno-timescale -DBD_ROUTE_PS=0 \
           -o "$TMP/s.vvp" -s "bdc_memport_${aw}_${dw}_${slots}" \
           sim/bd_prims_sim.v rtl/*.v "$f" > "$TMP/elab.log" 2>&1; then
        echo "ELABORATE FAIL aw=$aw dw=$dw slots=$slots"
        sed -n '1,6p' "$TMP/elab.log"
        bad=$((bad + 1)); continue
      fi
      ok=$((ok + 1))
    done
  done
done

# The refusal is part of the contract, so check it goes the other way too:
# 2^11 words does not fit the one RAMB18E1 gang bd_mem builds, and mem.py's
# check() is supposed to say so rather than silently fold memory in half.
if python3 ../bdc/mem.py "port:11:32:2" -o "$TMP/over.v" > "$TMP/over.log" 2>&1; then
    echo "REFUSAL FAIL   aw=11 generated instead of being refused"
    bad=$((bad + 1))
else
    ok=$((ok + 1))
fi

echo "mem_shapes: $ok ok, $bad failed"
[ "$bad" -eq 0 ]
