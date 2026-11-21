#!/bin/bash
# guard_gate.sh -- the strict gate (GATE_RUNTS=fail) on the three guarded routes (research/data/suite/board/guard_g10):
# worst, max, min + 16 draws each (K 45K01..45K16), the kernel's own suite vectors and C oracle (as suite_one.sh)
cd /tmp/bot/repo; O=/tmp/bot/gguard; mkdir -p $O; G=$O/gate.txt
CASE=$(sed -n '/^case \$K in$/,/^esac$/p' research/tools/suite/suite_one.sh)
one() { local K=$1 c=$2 HW=$3 XS=$4 V=$5; local W=$O/g/$K/${c/:/_}; mkdir -p $W; cp $XS $W/xray.sdf
  local r; r=$(GATE_RUNTS=fail research/tools/eventgraph/bench_gate.sh $HW ${K}_bench_gen $W $V $O/$K.exp $c 2>&1 | tail -1)
  echo "$K $c :: $r" >> $G; }
i=0
for kx in sqrtsub:9 lfsrfind:10 collatz64:9; do
  K=${kx%%:*}; X=${kx##*:}; i=$((i + 1)); R=$(pwd)
  V=""; OR=""; eval "$CASE"
  ( $OR < "$V" ) > $O/$K.exp 2> $O/$K.oracle.err
  HW=/tmp/bot/runs/g10/hw/g10_${K}_1_$X; XS=/tmp/bot/runs/g10/r/g10_${K}_1_$X/xray.sdf
  for c in worst max min $(for d in $(seq 1 16); do printf 'draw:45%d%02d ' $i $d; done); do
    one $K $c $HW $XS $R/$V & while [ "$(jobs -rp | wc -l)" -ge ${GJ:-6} ]; do sleep 5; done
  done
done
wait; echo DONE >> $G
