#!/usr/bin/env bash
# T137: research shrink4 candidates (ee3e7cf2f). x0.40a (all sizes x0.40 except UADDI0; UCMPI0 4) and control x0.40c
# (UADDI0/UCMPI0/UCMPI1 kept) on the board seed 27: own build, own FF scan, own GLS with own oracle + own latch/steer
# monitors at research's worst band and the model corner advA (chains 0.20, rest 0.31, cells 1.0), plus FAST_MIN.
# Question (from T136): does UCMPI0 = 4 give live select changes under req at ucond_br2/br5 on x0.40a, and is x0.40c clean?
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91; L=/root/t137.log; K=xorshift
until [ -f /root/t136.done ]; do sleep 60; done
git -C $R fetch -q origin; git -C $R checkout -q --detach ee3e7cf2f
F=$R/build/frontend/xorshift/comp/handshake_transformed.mlir
echo "research $(git -C $R rev-parse --short HEAD) $(date -u)" > $L
for v in x40a x40c; do
  H=xd${v}_27
  [ -f $R/research/data/xorshift_sizes_T3s50_fr4a_${v}_bench.vh ] || { echo "$v: no sizes file" >> $L; continue; }
  mv /root/t65/xd_27 /root/t65/xd_27.keep; cp $F /root/t137_orig.mlir; cp $R/research/data/fifteen/xorshift_predec.mlir $F
  (cd $A/t91; SZ=../research/data/xorshift_sizes_T3s50_fr4a_${v}_bench.vh R=$R bash build_lev.sh xd 27 > /root/t90/build_$H.log 2>&1)
  cp /root/t137_orig.mlir $F
  rm -rf /root/t65/$H; mv /root/t65/xd_27 /root/t65/$H; mv /root/t65/xd_27.keep /root/t65/xd_27
  echo "$v build: $(md5sum /root/t65/$H/${K}_bench_gen.sdf | cut -c1-8); $(grep -E 'UCMPI0|UADDI0' $R/research/data/xorshift_sizes_T3s50_fr4a_${v}_bench.vh | tr -s ' ' | cut -d' ' -f2,3 | tr '\n' ' ')" >> $L
  python3 $A/t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "$v ff: $(tail -1 /root/t90/ff_$H.txt | sed 's/.*flops/flops/')" >> $L
  cd $A/t90
  export PS_MON_GEN=$A/t104/mon_both1.py
  one() { local T=$1 FLD=$2
    HWD=$H GLS_SDF_FIELD=$FLD BAND_CHAIN=${3:-0.21} BAND_REST=${4:-0.288} BAND_CELLX=${5:-1} timeout 5400 bash ../t136/gate_adv.sh $K $T
    python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
    echo "$v $T: $(grep agreement /root/t90/${H}_${T}_oracle.txt); steer viol $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_$T.log) [$(grep 'STEERMON VIOLATION' /root/t65/${H}_$T.log | sed 's/.*udut.\(ucond_br[0-9]*\).*/\1/' | sort | uniq -c | tr -s ' ' | tr '\n' ' ')]; br2/br5 margin $(grep STEERMON /root/t65/${H}_$T.log | grep -E 'ucond_br(2|5)\.u\$LUT6' | tail -2 | sed 's/.*udut.\(ucond_br[0-9]\).*min_rise_margin_ps=\([0-9-]*\).*/\1=\2/' | tr '\n' ' '); latch viol lines $(grep LATCHMON /root/t65/${H}_$T.log | grep -cE 'violations=[1-9]')" >> $L
    rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv; }
  one fastmin min
  # band SDF once, then the two band runs in parallel
  HWD=$H GLS_SDF_FIELD=band BAND_CHAIN=0.21 BAND_REST=0.288 BAND_CELLX=1 one worst band
  one advA band 0.20 0.31 1.0
  cd $A/t137
done
echo DONE >> $L; echo DONE > /root/t137.done
