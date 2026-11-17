#!/usr/bin/env bash
# T139: research affc211d5 "shrink5: xorshift x0.55a 128/128 draws on 32 routes, median 16.85 ns"; board route seed 21
# (P 16.84). x0.55a = item 33 sizes x0.55 except UADDI0 (UCMPI0 10 -> 6, UCMPI1 9 -> 5). After T137 (x0.40a hangs at
# FAST_MIN / worst / advA on seed 27 after a ucmpi1 -> ucond_br8 select race): own build of seed 21, own FF scan, own GLS
# with own oracle + own latch/steer monitors at FAST_MIN (outside the draw band), worst, advA (chains 0.20, rest 0.31,
# cells 1.0) and SLOW_MAX; hangs stopped by hangdog.sh after 8 wall minutes without a result.
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91; L=/root/t139.log; K=xorshift; S=21; v=x55a; H=xd${v}_$S
until [ -f /root/t137.done ]; do sleep 60; done
(nohup bash $A/t139/hangdog.sh > /dev/null 2>&1 &)
git -C $R fetch -q origin; git -C $R checkout -q --detach affc211d5
F=$R/build/frontend/xorshift/comp/handshake_transformed.mlir
echo "research $(git -C $R rev-parse --short HEAD) $(date -u)" > $L
mv /root/t65/xd_$S /root/t65/xd_$S.keep 2>/dev/null; cp $F /root/t139_orig.mlir; cp $R/research/data/fifteen/xorshift_predec.mlir $F
(cd $A/t91; SZ=../research/data/xorshift_sizes_T3s50_fr4a_${v}_bench.vh R=$R bash build_lev.sh xd $S > /root/t90/build_$H.log 2>&1)
cp /root/t139_orig.mlir $F
rm -rf /root/t65/$H; mv /root/t65/xd_$S /root/t65/$H; mv /root/t65/xd_$S.keep /root/t65/xd_$S 2>/dev/null
echo "$v s$S build: $(md5sum /root/t65/$H/${K}_bench_gen.sdf | cut -c1-8)" >> $L
python3 $A/t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff: $(tail -1 /root/t90/ff_$H.txt | sed 's/.*flops/flops/')" >> $L
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py
one() { local T=$1 FLD=$2
  HWD=$H GLS_SDF_FIELD=$FLD BAND_CHAIN=${3:-0.21} BAND_REST=${4:-0.288} BAND_CELLX=${5:-1} timeout 5400 bash ../t136/gate_adv.sh $K $T
  python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "$T: $(grep agreement /root/t90/${H}_${T}_oracle.txt); steer viol $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log) [$(grep 'STEERMON VIOLATION' /root/t65/${H}_$T.log | sed 's/.*udut.\(ucond_br[0-9]*\).*/\1/' | sort | uniq -c | tr -s ' ' | tr '\n' ' ')]; min margins $(for b in 2 5 8; do grep STEERMON /root/t65/${H}_$T.log | grep "ucond_br$b.u\$LUT6" | tail -1 | sed 's/.*udut.\(ucond_br[0-9]\).*min_rise_margin_ps=\([0-9-]*\).*/\1=\2/'; done | tr '\n' ' '); latch viol lines $(grep LATCHMON /root/t65/${H}_$T.log | grep -cE 'violations=[1-9]')" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
one fastmin min
one worst band
one advA band 0.20 0.31 1.0
one slowmax max
echo DONE >> $L; echo DONE > /root/t139.done
