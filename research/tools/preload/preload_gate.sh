#!/usr/bin/env bash
# preload_gate.sh HWDIR WORK XRAY_SDF VECSET COL -- bench_gate.sh on a preloaded vector set (research/data/preload/VECSET.{hex,pre,exp}):
# the same build, netlist from the bits, SDF, corner/draw and verdict as bench_gate.sh, plus the opt-in preload module
# (PS_MON_GEN=gen_preload.py) and +PRELOAD=VECSET.pre. bench_gate.sh and build_ps.sh are unchanged: PS_MON_GEN is
# build_ps.sh's existing monitor hook and GATE_PLUSARGS bench_gate.sh's existing plusarg pass-through.
# GATE_TBATCH (bench_gate.sh's opt-in, default here 30000 ns = 30 us; a preloaded batch needs <= 3 us, and a livelocked
# loop would otherwise simulate 1.2 ms per batch). Prints bench_gate's verdict line; the PRELOAD readback lines are in WORK/<col>/run.log.
set -euo pipefail
HW=$1; W=$2; XS=$3; V=$4; COL=$5
R=$(cd "$(dirname "$0")/../../.." && pwd); P=$R/research/data/preload
mkdir -p "$W"; [ -f "$W/xray.sdf" ] || cp "$XS" "$W/xray.sdf"
GATE_TBATCH=${GATE_TBATCH:-30000} PS_MON_GEN=$R/research/tools/preload/gen_preload.py GATE_PLUSARGS="+PRELOAD=$P/$V.pre ${GATE_PLUSARGS:-}" \
  "$R/research/tools/eventgraph/bench_gate.sh" "$HW" xorshift_bench_gen "$W" "$P/$V.hex" "$P/$V.exp" "$COL"
