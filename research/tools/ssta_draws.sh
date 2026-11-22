#!/usr/bin/env bash
# ssta_draws.sh ROUTED_JSON XRAY_SDF SIZES_VH OUT "KEYS" [JOBS] [CARRY_LO,HI] -- the static rules under many draws of the
# delay model: for each draw K, research/tools/draw_sdf.py writes the route's xray SDF as bench_gate.sh draw:K would
# time it (one delay per arc), and research/tools/corner_audit.py measures every constraint on it with NO guard
# (--guard-lo 1 --guard-hi 1 --a-frac 0 --a-min 0, BD_RAM_GUARD_PS=0) and the sizing loop's rule switches
# (research/tools/auto/auto_size.sh rule()); CA_ALLCONS=1 writes each constraint's raw margin. research/tools/
# ssta_table.py OUT then gives, per constraint, the margin's distribution over the draws (mean, sd, minimum, how many
# draws below 0) -- how often each race the rule names is lost in the model, far beyond what 4 simulated draws resolve.
# The rules are a model of the races, not the simulation: a lost race here is a race lost on paper; whether the circuit
# then gives a wrong answer is the GLS's to say (research/tools/eventgraph/bench_gate.sh on the same K).
set -uo pipefail
RJ=$(readlink -f "$1"); XS=$(readlink -f "$2"); Z=$(readlink -f "$3"); OUT=$4; KEYS=$5; J=${6:-4}; DC=${7:-0.20,1.0}
R=$(cd "$(dirname "$0")/../.." && pwd); mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
one() { local K=$1 D=$OUT/d$1
  [ -s "$D/raw/all_constraints.tsv" ] && return 0
  rm -rf "$D"; mkdir -p "$D/seed1/pnr"; ln -sf "$RJ" "$D/seed1/pnr/soak_routed.json"; cp "$Z" "$D/seed1/pnr/sizes.vh"
  python3 "$R/research/tools/draw_sdf.py" "$RJ" "$XS" "$K" "$D/seed1/pnr/soak_xray.sdf" --carry "$DC" > "$D/draw.txt" 2>&1 || return 1
  BD_SKEW_MUXN=1 PYTHONHASHSEED=1 CA_FAST=1 BD_RAM_GUARD_PS=0 BD_SKEW_STEER_SELF=1 CA_JOINAWARE=1 BD_SKEW_AND_JOIN=1 \
  CA_SIZERULE=1 CA_BENCHCAP=${CA_BENCHCAP:-1} CA_ALLCONS=1 \
    python3 "$R/research/tools/corner_audit.py" "$D/seed1" --prefix bridge_i.udut. --uniform 0.5 --no-size \
      --guard-lo 1 --guard-hi 1 --a-frac 0 --a-min 0 --out "$D/raw" > "$D/ca.log" 2>&1
  rm -f "$D/seed1/pnr/soak_xray.sdf" "$D/raw/soak.sdf" "$D/raw/"*.log
  [ -s "$D/raw/all_constraints.tsv" ]; }
for K in $KEYS; do one "$K" & while [ "$(jobs -rp | wc -l)" -ge "$J" ]; do sleep 2; done; done; wait
echo "ssta_draws: $(ls "$OUT"/d*/raw/all_constraints.tsv 2>/dev/null | wc -l) draws in $OUT"
