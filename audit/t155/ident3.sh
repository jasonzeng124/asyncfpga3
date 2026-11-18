#!/usr/bin/env bash
# T155: research a77d3da59 / 846da5507 / e164a0275 / 8a7a18e02 (bdc stores: each block's outgoing control joins its stores'
# completions) claims "105 old outputs byte-identical". Own check: bdc/emit.py at BASE (296c3bf13, before the stores work)
# and NEW (7197d85c2), clean worktrees, on every fixture's handshake MLIR in NEW's cloud/fixtures/frontend (one input
# copy for both sides) plus the three hand pre-pass MLIRs, top and --no-top, with knob sets: none, BDC_AUTO=1, and the
# xorshift / collatz hand recipes. Any byte difference (or rc difference) is listed.
set -u
BASE=${BASE:-296c3bf13}; NEW=${NEW:-7197d85c2}
W=/root/t155; rm -rf $W; mkdir -p $W/a $W/b $W/in
R=/home/user/asyncfpga3
for s in a b; do git -C $R worktree remove --force /root/wt-t155$s 2>/dev/null; done
git -C $R worktree add -q --detach /root/wt-t155a $BASE && git -C $R worktree add -q --detach /root/wt-t155b $NEW
cp -r /root/wt-t155b/cloud/fixtures/frontend $W/in/
declare -A S
S[none]=""; S[auto1]="BDC_AUTO=1"
S[xor]="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0"
S[col]="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
INS=""
for f in $W/in/frontend/*/comp/handshake_transformed.mlir; do K=$(basename $(dirname $(dirname $f))); INS="$INS $K:$f"; done
for p in xorshift_predec collatz_preeq2 collatz64_preeq2; do cp /root/wt-t155b/research/data/fifteen/$p.mlir $W/in/; INS="$INS $p:$W/in/$p.mlir"; done
n=0; d=0; okA=0; okB=0
for kv in $INS; do K=${kv%%:*}; M=${kv#*:}
  for s in "${!S[@]}"; do
    case $s in xor|col) case $K in collatz*|xorshift*) ;; *) continue;; esac;; esac
    for t in top notop; do a=""; [ $t = notop ] && a="--no-top"
    for side in a b; do (cd /root/wt-t155$side && env ${S[$s]} timeout 300 python3 bdc/emit.py "$M" $a -o $W/$side/${K}_${s}_$t.v > $W/$side/${K}_${s}_$t.log 2>&1; echo $? > $W/$side/${K}_${s}_$t.rc); done
    n=$((n+1)); [ "$(cat $W/a/${K}_${s}_$t.rc)" = 0 ] && okA=$((okA+1)); [ "$(cat $W/b/${K}_${s}_$t.rc)" = 0 ] && okB=$((okB+1))
    if cmp -s $W/a/${K}_${s}_$t.v $W/b/${K}_${s}_$t.v && cmp -s $W/a/${K}_${s}_$t.rc $W/b/${K}_${s}_$t.rc; then :; else d=$((d+1)); echo "DIFF $K $s $t rc $(cat $W/a/${K}_${s}_$t.rc)/$(cat $W/b/${K}_${s}_$t.rc)"; fi
  done; done
done
echo "cases $n, differing $d, emitted ok: base $okA, new $okB"
