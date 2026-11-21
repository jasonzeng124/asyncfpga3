#!/bin/sh
# run.sh -- probe Fid3 (session 2026-10-29): the glsdiff/glsdiff3 differential suite and
# this session's extra experiments, against origin/claude/research @ 6524fa3.
# src/ is a read-only copy: git archive origin/claude/research cells/gls | tar -x (no checkout).
# Output: out/suite.log (compare with ../out/run.log = 350f9be and ../out/ref_5d535d7.log),
#         out/f3.log (research's own run_f3.sh on the same sources), out/extra.log.
# Compiled .vvp files are deleted at the end (not committed).
set -e
H=$(cd "$(dirname "$0")" && pwd); cd "$H"
T=$H/..; G=$T/../glsdiff; C=$T/../gls-compare
SRC=$H/src; W=$H/work; O=$H/out
mkdir -p $W $O
{ echo '`timescale 1ps/1ps'; echo '`define GLS_FID'; cat $SRC/fid_core.vh; sed 's/^`include "fid_core.vh"//' $SRC/prims.v; } > $W/prims_fid.v
cp $SRC/prims.v $W/prims_def.v
cd $W
{
echo "# research tip: $(cat $H/TIP 2>/dev/null)"
for P in def fid; do
  echo "== $P: Kleene (43,767 vectors)"; python3 -I $C/kleene_check.py prims_$P.v | tail -1
  echo "== $P: 1-pin channel fit";        python3 -I $C/channel_fit.py prims_$P.v 60 | sed -n 1,4p
  echo "== $P: 2-pin per-pin transport";  python3 -I $G/perpin_fit.py prims_$P.v 60 | head -1

  iverilog -gspecify -o seqx_$P.vvp $G/tb_seq_x.v prims_$P.v;   vvp -n seqx_$P.vvp | grep CASE
  iverilog -gspecify -o carry_$P.vvp $G/tb_carry_saf.v prims_$P.v; vvp -n carry_$P.vvp | grep -v finish
done
python3 $G/gen_meta_centre.py 200 > tb_meta_centre.v
iverilog -gspecify -DGLS_TRANSPORT_IC -o meta_fid.vvp tb_meta_centre.v prims_fid.v
for s in 100 200 230 250 270 300 320 340 349 360 380 400 420; do vvp -n meta_fid.vvp +S=$s | grep '^S'; done
python3 $G/gen_meta_centre.py 1 | sed 's/^initial begin/always @(q[0]) $display("Q %0d %b", $time, q[0]);\ninitial begin/' > tb_meta_one.v
iverilog -gspecify -DGLS_TRANSPORT_IC -o one.vvp tb_meta_one.v prims_fid.v; vvp -n one.vvp +S=100 +META_VERBOSE=2 | head -4
} > $O/suite.log 2>&1
echo "wrote $O/suite.log"
F3_OUT=$W/f3 ; mkdir -p $F3_OUT; export F3_OUT
sh $SRC/fid/f3/run_f3.sh > $O/f3.log 2>&1 || echo "run_f3.sh rc=$?" >> $O/f3.log
echo "wrote $O/f3.log"
[ -f $H/extra.sh ] && sh $H/extra.sh > $O/extra.log 2>&1 && echo "wrote $O/extra.log"
rm -rf $W    # scratch only; summaries are in out/
