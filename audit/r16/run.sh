#!/bin/sh
# audit r16 rerun (iverilog 12): source ~/audit-tc/openxc7/export.sh first. fid_core.vh copied from ~/wt-r15.
set -e; cd "$(dirname "$0")"
cp /root/wt-r15/cells/gls/fid_core.vh .; md5sum fid_core.vh
printf '`timescale 1ps/1ps\n`include "fid_core.vh"\n' > top.v
iverilog -g2012 -o c2r.vvp top.v tb_c2r.v
for W in 20 60 100 140 150 180 199 200 300; do vvp -n c2r.vvp +W=$W +META_VERBOSE=2 > log_W$W.txt; python3 -I chk.py log_W$W.txt | tail -1; done > sweep.log
vvp -n c2r.vvp +W=20 +META_OFF=1 > log_W20_off.txt
for X in 150 200 600; do vvp -n c2r.vvp +W=20 +GAP=1 +W2=$X +META_VERBOSE=2 > log_follow_W2_$X.txt; done
vvp -n c2r.vvp +W=20 +GAP=1 +W2=200 +META_OFF=1 > log_follow_off.txt
for S in 1 2; do mkdir -p fr_s$S; python3 -I gen_fidrand.py $S 40 20000 fr_s$S
  iverilog -g2012 -o fr_s$S/sim.vvp top.v fr_s$S/tb_fidrand.v
  for LV in 0 7 40; do vvp -n fr_s$S/sim.vvp +FID_LEVEL_PS=$LV > fr_s$S/log_lv$LV.txt; python3 -I cmp_fidrand.py fr_s$S/stim.json fr_s$S/log_lv$LV.txt $LV; done; done > fidrand.log
iverilog -g2012 -o xor.vvp top.v tb_xor.v && vvp -n xor.vvp > xor.log
