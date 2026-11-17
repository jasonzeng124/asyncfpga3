#!/usr/bin/env bash
# T147: research 26c095065 "bdc: BDC_AUTO=1 ... Off (unset or not "1"), nothing here is called and bdc/emit.py's output is
# byte-identical". Own check: bdc/emit.py from the parent commit (26c095065^) and from 26c095065, clean worktrees, on every
# kernel's handshake MLIR (taken from one place, so both sides read the same input) and the three hand-recipe pre-pass MLIRs,
# top and --no-top, under own knob sets: none, BDC_AUTO=0, BDC_AUTO=2, BDC_AUTO=true (all must be OFF), and the three hand
# recipes. Prints per-case md5 equality; any difference is a counterexample.
set -u
W=/root/t147; rm -rf $W; mkdir -p $W/a $W/b
R=/root/wt-r91
git -C $R worktree remove --force /root/wt-t147a 2>/dev/null; git -C $R worktree remove --force /root/wt-t147b 2>/dev/null
git -C $R worktree add -q --detach /root/wt-t147a 26c095065^ && git -C $R worktree add -q --detach /root/wt-t147b 26c095065
declare -A S
S[none]=""; S[auto0]="BDC_AUTO=0"; S[auto2]="BDC_AUTO=2"; S[autotrue]="BDC_AUTO=true"
S[xor]="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0"
S[col]="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
INS=""
for K in collatz collatz64 fir gcd ipow isprime single_loop test_loop_free xorshift; do f=$R/build/frontend/$K/comp/handshake_transformed.mlir; [ -f $f ] && INS="$INS $K:$f"; done
INS="$INS xorpre:$R/research/data/fifteen/xorshift_predec.mlir colpre:$R/research/data/fifteen/collatz_preeq2.mlir c64pre:$R/research/data/fifteen/collatz64_preeq2.mlir"
n=0; d=0
for kv in $INS; do K=${kv%%:*}; M=${kv#*:}
  for s in "${!S[@]}"; do for t in top notop; do a=""; [ $t = notop ] && a="--no-top"
    for side in a b; do (cd /root/wt-t147$side && env ${S[$s]} python3 bdc/emit.py "$M" $a -o $W/$side/${K}_${s}_$t.v > $W/$side/${K}_${s}_$t.log 2>&1; echo $? > $W/$side/${K}_${s}_$t.rc); done
    n=$((n+1))
    if cmp -s $W/a/${K}_${s}_$t.v $W/b/${K}_${s}_$t.v && cmp -s $W/a/${K}_${s}_$t.rc $W/b/${K}_${s}_$t.rc; then :; else d=$((d+1)); echo "DIFF $K $s $t rc $(cat $W/a/${K}_${s}_$t.rc)/$(cat $W/b/${K}_${s}_$t.rc)"; fi
  done; done
done
echo "cases $n, differing $d, outputs non-empty: $(find $W/b -name '*.v' -size +0 | wc -l)"
