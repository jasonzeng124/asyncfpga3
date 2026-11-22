#!/bin/bash
# qr_gate.sh -- the strict gate (GATE_RUNTS=fail) on quadrec s3's v13-preview route (so2: the search's pinned structure,
# overbuilt BD_SYMTRIM, trimmed; sdf 20d29647): worst, SLOW_MAX, FAST_MIN + 32 draws (K 45301..45332), suite vectors and C oracle
cd /tmp/bot/repo; O=/tmp/bot/qrgate; mkdir -p $O; G=$O/gate.txt; : > $G
K=quadrec; R=$(pwd)
CASE=$(sed -n '/^case \$K in$/,/^esac$/p' research/tools/suite/suite_one.sh); V=""; OR=""; eval "$CASE"
( $OR < "$V" ) > $O/$K.exp 2> $O/$K.oracle.err
HW=/tmp/bot/runs/so2/hw/kd_quadrec_3_12; XS=/tmp/bot/runs/so2/r/kd_quadrec_3_12/xray.sdf
md5sum $HW/${K}_bench_gen.fasm $XS | cut -c1-8 > $O/inputs.md5
one() { local c=$1; local W=$O/g/${c/:/_}; mkdir -p $W; cp $XS $W/xray.sdf
  local r; r=$(GATE_RUNTS=fail research/tools/eventgraph/bench_gate.sh $HW ${K}_bench_gen $W $R/$V $O/$K.exp $c 2>&1 | tail -1)
  echo "$K $c :: $r" >> $G; rm -rf $W/draw_* 2>/dev/null; }
for c in worst max min $(for d in $(seq 1 32); do printf 'draw:453%02d ' $d; done); do
  one $c & while [ "$(jobs -rp | wc -l)" -ge ${GJ:-6} ]; do sleep 5; done
done
wait; echo DONE >> $G
