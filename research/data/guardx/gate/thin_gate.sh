#!/bin/bash
# thin_gate.sh -- the strict gate (GATE_RUNTS=fail) on item 44's three thinnest routes (formal's first failure x <= 0.15):
# worst, max, min + 16 draws each (K 44K01..44K16), the kernel's own suite vectors and C oracle (as suite_one.sh)
cd /tmp/bot/repo; O=/tmp/bot/thin; mkdir -p $O; G=$O/gate.txt
CASE=$(sed -n '/^case \$K in$/,/^esac$/p' research/tools/suite/suite_one.sh)
one() { local K=$1 c=$2 HW=$3 XS=$4 V=$5; local W=$O/g/$K/${c/:/_}; mkdir -p $W; cp $XS $W/xray.sdf
  local r; r=$(GATE_RUNTS=fail research/tools/eventgraph/bench_gate.sh $HW ${K}_bench_gen $W $V $O/$K.exp $c 2>&1 | tail -1)
  echo "$K $c :: $r" >> $G; }
i=0
for K in sqrtsub lfsrfind collatz64; do
  i=$((i + 1)); R=$(pwd)
  V=""; OR=""; eval "$CASE"
  ( $OR < "$V" ) > $O/$K.exp 2> $O/$K.oracle.err
  HW=/tmp/bot/census/$K/hw
  case $K in collatz64) XS=/tmp/bot/runs/bq10c64/r/bq_collatz64_1/xray.sdf;; *) XS=$(ls /tmp/bot/runs/bsuite/r/bq_${K}_*/xray.sdf | head -1);; esac
  for c in worst max min $(for d in $(seq 1 16); do printf 'draw:44%d%02d ' $i $d; done); do
    one $K $c $HW $XS $R/$V & while [ "$(jobs -rp | wc -l)" -ge ${GJ:-6} ]; do sleep 5; done
  done
done
wait; echo DONE >> $G
