#!/usr/bin/env bash
# ident.sh REPO OUTDIR : emit.py over every fixture x {top, --no-top} x knob sets; one file each + a log of exit codes
R=$1; O=$2; mkdir -p "$O"
declare -A SETS
SETS[plain]=""
SETS[xor_hand]="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0"
SETS[col_hand]="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
SETS[ipow_hand]="BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
SETS[auto0]="BDC_AUTO=0"
for K in collatz collatz64 fir gcd ipow isprime single_loop test_loop_free xorshift; do
  M=$R/build/frontend/$K/comp/handshake_transformed.mlir
  for s in "${!SETS[@]}"; do
    for t in top notop; do
      a=""; [ $t = notop ] && a="--no-top"
      ( cd "$R" && env ${SETS[$s]} python3 bdc/emit.py "$M" $a -o "$O/${K}_${s}_$t.v" > "$O/${K}_${s}_$t.log" 2>&1; echo "$K $s $t rc=$?" ) 
    done
  done
done > "$O/rc.txt"
# the hand recipes on their pre-pass MLIR
for p in "xorshift research/data/fifteen/xorshift_predec.mlir xor_hand" "collatz research/data/fifteen/collatz_preeq2.mlir col_hand" "collatz64 research/data/fifteen/collatz64_preeq2.mlir col_hand"; do
  set -- $p; K=$1; M=$R/$2; s=$3
  for t in top notop; do a=""; [ $t = notop ] && a="--no-top"
    ( cd "$R" && env ${SETS[$s]} python3 bdc/emit.py "$M" $a -o "$O/${K}_pre_${s}_$t.v" > "$O/${K}_pre_${s}_$t.log" 2>&1; echo "$K pre_$s $t rc=$?" )
  done
done >> "$O/rc.txt"
