#!/usr/bin/env bash
# T80: is bdc/emit.py's output byte-identical between two research commits, with every opt-in knob unset, and with the
# board items' knobs set?  usage: emitdiff.sh OLD NEW   (git commits; run from the repo)
set -u; O=$1; N=$2; S=/root/emitdiff_$$; mkdir -p $S/o $S/n
git archive $O bdc cloud/fixtures/frontend | tar -x -C $S/o; git archive $N bdc cloud/fixtures/frontend | tar -x -C $S/n
UNSET="-u BDC_MERGE_RES_LINK -u BDC_RING_COUNT_OLINKS -u BDC_FORK_OUT_LINK -u BDC_NO_LINK -u BDC_MERGE_OUT_LINK -u BDC_LINK_FASTFALL -u BDC_LINK_DEPTHS -u BDC_CONST_DATA"
for k in collatz collatz64 fir gcd ipow isprime test_loop_free xorshift; do
  f=cloud/fixtures/frontend/$k/comp/handshake_transformed.mlir
  for v in o n; do (cd $S/$v && env $UNSET python3 bdc/emit.py $f --no-top -o $S/$v.$k.v >/dev/null 2>&1
     env $UNSET BDC_CONST_DATA=1 BDC_LINK_FASTFALL=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 python3 bdc/emit.py $f --no-top -o $S/$v.$k.k.v >/dev/null 2>&1); done
  d() { [ -f $S/o.$1 ] || [ -f $S/n.$1 ] || { echo none; return; }; cmp -s $S/o.$1 $S/n.$1 && echo SAME || echo DIFF; }
  echo "$k default $(d $k.v) knobs $(d $k.k.v)"
done; rm -rf $S
