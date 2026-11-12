#!/bin/sh
# run_all.sh -- reproduce formal/notes/A-gls-compare-2.md (iverilog 12; ~3 min).
# src/ holds read-only copies from origin/claude/research @ 5d535d7 (git show, no checkout).
set -e
H=$(cd "$(dirname "$0")" && pwd); cd "$H"
{ echo '`timescale 1ps/1ps'; echo '`define GLS_FID'; cat src/fid_core.vh; sed 's/^`include "fid_core.vh"//' src/prims.v; } > prims_fid.v
cp src/prims.v prims_def.v
mkdir -p out; cd out
for P in def fid; do
  echo "== $P: Kleene (43,767 vectors)"; python3 -I ../../gls-compare/kleene_check.py ../prims_$P.v | tail -1
  echo "== $P: 1-pin channel fit";        python3 -I ../../gls-compare/channel_fit.py ../prims_$P.v 60 | sed -n 1,4p
  echo "== $P: 2-pin per-pin transport";  python3 -I ../perpin_fit.py ../prims_$P.v 60 | head -1
  iverilog -gspecify -o seqx_$P.vvp ../tb_seq_x.v ../prims_$P.v;   vvp -n seqx_$P.vvp | grep CASE
  iverilog -gspecify -o carry_$P.vvp ../tb_carry_saf.v ../prims_$P.v; vvp -n carry_$P.vvp | grep -v finish
done
python3 ../gen_meta_centre.py 200 > ../tb_meta_centre.v
iverilog -gspecify -DGLS_TRANSPORT_IC -o meta_fid.vvp ../tb_meta_centre.v ../prims_fid.v
for s in 100 200 230 250 270 300 320 340 349 360 380 400 420; do vvp -n meta_fid.vvp +S=$s | grep '^S'; done
python3 ../gen_meta_centre.py 1 | sed 's/^initial begin/always @(q[0]) $display("Q %0d %b", $time, q[0]);\ninitial begin/' > ../tb_meta_one.v
iverilog -gspecify -DGLS_TRANSPORT_IC -o one.vvp ../tb_meta_one.v ../prims_fid.v; vvp -n one.vvp +S=100 +META_VERBOSE=2 | head -4
python3 ../orb_crit.py 424
