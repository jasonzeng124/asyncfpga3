#!/bin/sh
# run_all.sh -- probe Fid3: rerun the A-gls-compare-2 differential suite (glsdiff/)
# against the CURRENT research GLS. src/ holds read-only copies (git show, no checkout)
# from origin/claude/research @ 350f9be (2026-10-27 12:50, the remote head on 2026-10-28).
# Testbenches and fit scripts are reused unchanged from ../glsdiff and ../gls-compare.
# Output: out/run.log (diff it against out/ref_5d535d7.log, the same suite on glsdiff/src).
set -e
H=$(cd "$(dirname "$0")" && pwd); cd "$H"
G=../glsdiff; C=../gls-compare
SRC=${1:-src}; LOG=${2:-out/run.log}
mkdir -p out/work
{ echo '`timescale 1ps/1ps'; echo '`define GLS_FID'; cat $SRC/fid_core.vh; sed 's/^`include "fid_core.vh"//' $SRC/prims.v; } > out/work/prims_fid.v
cp $SRC/prims.v out/work/prims_def.v
W=$H/out/work
{
cd $W
for P in def fid; do
  echo "== $P: Kleene (43,767 vectors)"; python3 -I $H/$C/kleene_check.py prims_$P.v | tail -1
  echo "== $P: 1-pin channel fit";        python3 -I $H/$C/channel_fit.py prims_$P.v 60 | sed -n 1,4p
  echo "== $P: 2-pin per-pin transport";  python3 -I $H/$G/perpin_fit.py prims_$P.v 60 | head -1
  iverilog -gspecify -o seqx_$P.vvp $H/$G/tb_seq_x.v prims_$P.v;   vvp -n seqx_$P.vvp | grep CASE
  iverilog -gspecify -o carry_$P.vvp $H/$G/tb_carry_saf.v prims_$P.v; vvp -n carry_$P.vvp | grep -v finish
done
python3 $H/$G/gen_meta_centre.py 200 > tb_meta_centre.v
iverilog -gspecify -DGLS_TRANSPORT_IC -o meta_fid.vvp tb_meta_centre.v prims_fid.v
for s in 100 200 230 250 270 300 320 340 349 360 380 400 420; do vvp -n meta_fid.vvp +S=$s | grep '^S'; done
python3 $H/$G/gen_meta_centre.py 1 | sed 's/^initial begin/always @(q[0]) $display("Q %0d %b", $time, q[0]);\ninitial begin/' > tb_meta_one.v
iverilog -gspecify -DGLS_TRANSPORT_IC -o one.vvp tb_meta_one.v prims_fid.v; vvp -n one.vvp +S=100 +META_VERBOSE=2 | head -4
} > $H/$LOG 2>&1
echo "wrote $LOG"
