#!/bin/bash
# predict_variants.sh RUNS -- PROGRAM.md FIRST item step 3: predict every built second-latch variant (and collatz's
# merge-output link) from its seed's BASE graph alone.  Edits (fixed before any prediction was computed):
#   p8    depth:ulink_n_trueResult_8:3:0      (BDC_LINK_DEPTHS=ulink_n_trueResult_8=2; new stage SDELAY = STAGE_PAD 3, DACK 0)
#   p11   depth:ulink_n11__1:3:0
#   p12   depth:ulink_n_trueResult_12:1:0     (the pipe's SDELAY macro is 1 in the x0.5 sizes; every stage takes it)
#   all3  the three together
#   mo    stage:ucontrol_merge0_req:ucontrol_merge0_ack:4:6:fastrise   (BDC_MERGE_OUT_LINK: DELAY SELECT_PAD 4, DACK ACK_PAD 6)
#   p8mo  p8 + mo
#   collatz cdmo: mo on the collatz BDC_CONST_DATA base
R=$1; W=$(dirname "$0")/whatif.py
P8=depth:ulink_n_trueResult_8:3:0; P11=depth:ulink_n11__1:3:0; P12=depth:ulink_n_trueResult_12:1:0
MO=stage:ucontrol_merge0_req:ucontrol_merge0_ack:4:6:fastrise
for s in 1 2 3 4; do
  g=$R/r/x50_$s/eventgraph; [ -f $g/arcs.tsv ] || continue
  for v in "p8 $P8" "all3 $P8 $P11 $P12" "p11 $P11" "p12 $P12" "mo $MO" "p8mo $P8 $MO"; do
    set -- $v; n=$1; shift
    echo "xorshift $n seed $s: $(python3 $W $g period "$@" 2>&1 | tr '\n' ' ')"
  done
done
for s in 1 2 3 4; do
  g=$R/r/col_cd_$s/eventgraph; [ -f $g/arcs.tsv ] || continue
  echo "collatz cdmo seed $s: $(python3 $W $g period $MO 2>&1 | tr '\n' ' ')"
done
