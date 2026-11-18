#!/usr/bin/env bash
# T150: BOARD-QUEUE item 37 (research b7d5d2c59): xorshift x55a10 seed 21 (item 35's sizes, UCMPI0 6 -> 10), route sdf
# 42b4fb4c. Own build (as T139), own FF scan, own GLS with own oracle + own latch/steer monitors on xor19 (t144/xor19.hex)
# and own long-rounds vectors (t142/xorshift_long.hex, rounds up to the bench maximum 4095) at FAST_MIN, SLOW_MAX, worst,
# advA (chains 0.20, rest 0.31, CARRY 1.0) with and without scatter, advC (0.20 / 0.20 / 1.0) without scatter.
# Question: does the entry-compare fix lift item 35's ucond_br2 margin (T139 / T142 / T144: 60-485 ps) as formal C48 says?
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91; L=/root/t150.log; K=xorshift; S=21; v=x55a10; H=xd${v}_$S
git -C $R fetch -q origin; git -C $R checkout -q --detach b7d5d2c59
F=$R/build/frontend/xorshift/comp/handshake_transformed.mlir
echo "research $(git -C $R rev-parse --short HEAD) $(date -u)" > $L
mv /root/t65/xd_$S /root/t65/xd_$S.keep 2>/dev/null; cp $F /root/t150_orig.mlir; cp $R/research/data/fifteen/xorshift_predec.mlir $F
(cd $A/t91; SZ=../research/data/xorshift_sizes_T3s50_fr4a_${v}_bench.vh R=$R bash build_lev.sh xd $S > /root/t90/build_$H.log 2>&1)
cp /root/t150_orig.mlir $F
rm -rf /root/t65/$H; mv /root/t65/xd_$S /root/t65/$H; mv /root/t65/xd_$S.keep /root/t65/xd_$S 2>/dev/null
echo "$v s$S build: sdf $(md5sum /root/t65/$H/${K}_bench_gen.sdf | cut -c1-8) (item 37: 42b4fb4c); UCMPI0 $(grep UCMPI0 $R/research/data/xorshift_sizes_T3s50_fr4a_${v}_bench.vh | awk '{print $3}')" >> $L
python3 $A/t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff: $(tail -1 /root/t90/ff_$H.txt | sed 's/.*flops/flops/')" >> $L
sed 's/GLS_SCATTER=0.126/GLS_SCATTER=${SCAT:-0.126}/' $A/t142/gate.sh > /root/t150_gate.sh
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py
one() { local T=$1 V=$2 FLD=$3 C=${4:-0.21} RR=${5:-0.288} X=${6:-1} SC=${7:-0.126}
  HWD=$H GLS_SDF_FIELD=$FLD VECF=$V BAND_CHAIN=$C BAND_REST=$RR BAND_CELLX=$X SCAT=$SC timeout 7200 bash /root/t150_gate.sh $K $T
  python3 ../t65/oracle_xorshift.py check $V /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$T: $(grep agreement /root/t90/${H}_${T}_oracle.txt); runts $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log); min margins $(for b in 2 5 6 7 8; do grep STEERMON /root/t65/${H}_$T.log | grep "ucond_br$b.u\$LUT6" | tail -1 | sed 's/.*udut.\(ucond_br[0-9]\).*min_rise_margin_ps=\([0-9-]*\).*/\1=\2/'; done | tr '\n' ' '); latch viol lines $(grep LATCHMON /root/t65/${H}_$T.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
X19=$A/t144/xor19.hex; LR=$A/t142/xorshift_long.hex
one x19_fastmin $X19 min & one x19_advA_ns $X19 band 0.20 0.31 1.0 0 & wait
one x19_advC_ns $X19 band 0.20 0.20 1.0 0 & one x19_worst $X19 band & wait
one x19_advA $X19 band 0.20 0.31 1.0 0.126 & one x19_slowmax $X19 max & wait
one lr_advA $LR band 0.20 0.31 1.0 0.126 & one lr_advA_ns $LR band 0.20 0.31 1.0 0 & wait
echo DONE >> $L; echo DONE > /root/t150.done
