#!/bin/sh
# audit r20 rerun (iverilog 12, one sim at a time): source ~/audit-tc/openxc7/export.sh first.
# old = /root/wt-r12 fid_core.vh (2422ccea, 034636b2 = r16's file), new = /root/wt-r13 (5ccef3ed, 103fbbe9).
set -e; cd "$(dirname "$0")"
mkdir -p old new mask
cp /root/wt-r12/cells/gls/fid_core.vh old/; cp /root/wt-r13/cells/gls/fid_core.vh new/; md5sum old/fid_core.vh new/fid_core.vh
for v in old new; do printf '`timescale 1ps/1ps\n`include "fid_core.vh"\n' > $v/top.v; done
NEWD="-DFIDNEW -DFB6MASK=6'b000100"
iverilog -g2012 $NEWD -I new -o new/c2r.vvp new/top.v tb_c2r.v; iverilog -g2012 -I old -o old/c2r.vvp old/top.v tb_c2r.v
iverilog -g2012 $NEWD -I new -o new/adv.vvp new/top.v tb_adv.v; iverilog -g2012 -I old -o old/adv.vvp old/top.v tb_adv.v
# 1. r16 follow pulse + r16 sweep + META_OFF + xor
for v in old new; do for X in 150 200 600; do vvp -n $v/c2r.vvp +W=20 +GAP=1 +W2=$X +META_VERBOSE=2 > $v/log_follow_W2_$X.txt
  echo "$v W2=$X: $(grep -c '^F .* 1$' $v/log_follow_W2_$X.txt) q=1, $(grep -c '^F .* 0$' $v/log_follow_W2_$X.txt) q=0"; done; done > follow.log
for v in old new; do for W in 20 60 100 140 150 180 199 200 300; do vvp -n $v/c2r.vvp +W=$W +META_VERBOSE=2 > $v/log_W$W.txt
  echo "$v W=$W $(python3 -I chk.py $v/log_W$W.txt | tail -1)"; done; done > sweep.log
for v in old new; do vvp -n $v/c2r.vvp +W=20 +META_OFF=1 > $v/log_W20_off.txt; iverilog -g2012 -I $v -o $v/xor.vvp $v/top.v tb_xor.v; vvp -n $v/xor.vvp | sort > $v/xor.log; done
# 2. adversarial
for v in old new; do for H in 50 100 150 180; do for L in 1 10 30; do vvp -n $v/adv.vvp +NP=10 +H=$H +L=$L | grep RES | sed "s/^/$v /"; done; done; done > train.log
for m in 000000 000001 000110; do iverilog -g2012 -DFIDNEW "-DFB6MASK=6'b$m" -I new -o mask/adv_$m.vvp new/top.v tb_adv.v
  for a in "+H=20" "+H=300" "+H=20 +GAP2=1 +W2=200"; do echo "FB6=$m $a: $(vvp -n mask/adv_$m.vvp +NP=1 $a | grep -E 'RES|resolver enabled' | head -1)"; done; done > mask.log
for v in old new; do for X in 150 200 600; do echo "$v META_X W2=$X $(vvp -n $v/adv.vvp +H=20 +GAP2=1 +W2=$X +META_X=1 | grep RES)"; done; done > metax.log
for v in old new; do for BX in 30 100 300; do echo "$v BX=$BX $(vvp -n $v/adv.vvp +H=20 +BX=$BX | grep RES) | OFF $(vvp -n $v/adv.vvp +H=20 +BX=$BX +META_OFF=1 | grep RES)"; done; done > xin.log
for v in old new; do for H in 100 150; do a=$(vvp -n $v/adv.vvp +NP=1 +H=$H | grep QV | cut -d' ' -f2); b=$(vvp -n $v/adv.vvp +NP=2 +H=$H +L=10 | grep QV | cut -d' ' -f2)
  python3 -I -c "import sys;a,b=sys.argv[1:3];print('$v H=$H NP1 ones',a.count('1'),'NP2 ones',b.count('1'),'latched with 1 pulse but not with 2:',sum(x=='1' and y=='0' for x,y in zip(a,b)),'reverse:',sum(x=='0' and y=='1' for x,y in zip(a,b)))" "$a" "$b"; done; done > nonmono.log
vvp -n new/adv.vvp +NP=2 +H=100 +L=10 +META_VERBOSE=2 > new/adv_np2_h100.log
