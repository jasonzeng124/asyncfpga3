#!/usr/bin/env bash
# T136: research f7130a5dc "shrink1: item 33 sizes hold to x0.40 under 8 draws". Own build of the x0.40 sizes on the
# board seed (27, pre_dec rewrite, recipe as T126k item 33), own FF/defect scan, then own GLS with own oracle
# (xorshift_17.hex) and own latch/steer monitors (t104/mon_both1.py) at:
#   the prjxray corners FAST_MIN / SLOW_MAX, research's 'worst' band, and the four extreme corners of research's own
#   draw model (chains, rest in [0.20, 0.31]; CARRY4/F7F8/FF in [0.20, 1.0]) that its 8 draws never reach:
#   advA chains 0.20 rest 0.31 cells 1.0 (data slow vs fast chains), advB chains 0.31 rest 0.20 cells 0.20 (hold side),
#   advC chains 0.20 rest 0.20 cells 1.0, advD chains 0.31 rest 0.31 cells 0.20;
#   then 16 own uniform draws of the same model (own RNG, seed 136000+i), 2 runs at a time.
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91; L=/root/t136.log; H=xd40_27; K=xorshift
git -C $R fetch -q origin; git -C $R checkout -q --detach f7130a5dc
F=$R/build/frontend/xorshift/comp/handshake_transformed.mlir
echo "research $(git -C $R rev-parse --short HEAD) $(date -u)" > $L
mv /root/t65/xd_27 /root/t65/xd_27.keep; cp $F /root/t136_orig.mlir; cp $R/research/data/fifteen/xorshift_predec.mlir $F
cd $A/t91; SZ=../research/data/xorshift_sizes_T3s50_fr4a_x40_bench.vh R=$R bash build_lev.sh xd 27 > /root/t90/build_$H.log 2>&1
cp /root/t136_orig.mlir $F
rm -rf /root/t65/$H /root/t65/$H.tmp; mv /root/t65/xd_27 /root/t65/$H.tmp
echo "build: $(grep -E 'bench_gen.sdf$' /root/t90/build_$H.log | grep -v -- '->'); uforkdec0 $(grep -c 'uforkdec0 (' /root/t65/$H.tmp/${K}_kernel_bench.v)" >> $L
mv /root/t65/$H.tmp /root/t65/$H; mv /root/t65/xd_27.keep /root/t65/xd_27
md5sum /root/t65/$H/${K}_bench_gen.sdf /root/t65/$H/${K}_bench_gen.bit >> $L
python3 ../t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff: $(tail -1 /root/t90/ff_$H.txt)" >> $L
cd $A/t90
export PS_MON_GEN=$A/t104/mon_both1.py
one() { # TAG FIELD [BAND_CHAIN BAND_REST BAND_CELLX SCSEED]
  local T=$1 FLD=$2
  HWD=$H GLS_SDF_FIELD=$FLD BAND_CHAIN=${3:-0.21} BAND_REST=${4:-0.288} BAND_CELLX=${5:-1} SCSEED=${6:-1} timeout 5400 bash ../t136/gate_adv.sh $K $T
  python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/${H}_$T.log 2 > /root/t90/${H}_${T}_oracle.txt 2>&1
  echo "gate $T [$FLD ${3:-} ${4:-} ${5:-} ${6:-}]: $(tail -1 /root/t90/${H}_${T}_oracle.txt); nonzero LATCH/STEER violations $(grep -E 'LATCHMON|STEERMON' /root/t65/${H}_$T.log | grep -cE 'violations=[1-9]'); min latch setup $(grep LATCHMON /root/t65/${H}_$T.log | tail -80 | sed 's/.*min_setup_ps=\([0-9-]*\).*/\1/' | sort -n | head -1)" >> $L
  rm -rf /root/t65/work_${H}_$T/*.json /root/t65/work_${H}_$T/*.tsv
}
one fastmin min & one slowmax max & wait
one worst band & one advA band 0.20 0.31 1.0 & wait
one advB band 0.31 0.20 0.20 & one advC band 0.20 0.20 1.0 & wait
one advD band 0.31 0.31 0.20 &
python3 - > /root/t136_draws.txt <<'PY'
import random
for i in range(1, 17):
    r = random.Random(136000 + i)
    print(i, '%.4f %.4f %.4f' % (r.uniform(.20, .31), r.uniform(.20, .31), r.uniform(.20, 1.0)))
PY
wait
while read i c rr x; do
  one dr$i band $c $rr $x $((136000+i)) &
  [ $((i % 2)) = 0 ] && wait
done < /root/t136_draws.txt
wait
echo DONE >> $L; echo DONE > /root/t136.done
