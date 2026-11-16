#!/usr/bin/env bash
# T126k: BOARD-QUEUE item 33 (xorshift item 27 + seed 2's datapath proposal, sizes fr4a, pre_dec rewrite, seed 27, recipe
# sdf 7f0c0592; research 1f945f33a: "rule M rows umux1 -113 nom / -192 worst, umux0 -71 worst are pessimism: mux data LEADS
# z_req by >= 1042 ps (FAST_MIN) on every token"). Own build now (t91/build_lev.sh xd); after T126j: own z_data monitor
# (t130/mon_zdata.py, state A) at FAST_MIN and worst, GLS 3 corners (oracle + t104 monitors), period, rule H, rule E.
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91; L=/root/t126k.log; H=xd_27; K=xorshift
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
F=$R/build/frontend/xorshift/comp/handshake_transformed.mlir
echo "research $(git -C $R rev-parse --short HEAD) $(date -u)" > $L
cp $F /root/t126k_orig.mlir; cp $R/research/data/fifteen/xorshift_predec.mlir $F
cd $A/t91; SZ=../research/data/xorshift_sizes_T3s50_fr4a_bench.vh R=$R bash build_lev.sh xd 27 > /root/t90/build_$H.log 2>&1
cp /root/t126k_orig.mlir $F
echo "build: $(grep -E 'bench_gen.sdf$' /root/t90/build_$H.log | grep -v -- '->'); uforkdec0 $(grep -c 'uforkdec0 (' /root/t65/$H/${K}_kernel_bench.v)" >> $L
python3 ../t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff: $(tail -1 /root/t90/ff_$H.txt)" >> $L
until [ -f /root/t126j.done ]; do sleep 60; done
cd $A/t90
export PS_MON_GEN=$A/t130/mon_zdata.py MON_KERNEL=/root/t65/$H/${K}_kernel_bench.v
for c in zd2_fastmin:min zd2_worst:band; do
  HWD=$H GLS_SDF_FIELD=${c##*:} timeout 5400 bash gate.sh $K ${c%%:*}
  python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/${H}_${c%%:*}.log 2 > /root/t90/${H}_${c%%:*}_oracle.txt 2>&1
  echo "zdata ${c%%:*}: $(tail -1 /root/t90/${H}_${c%%:*}_oracle.txt); $(grep 'ZDMON t=\|mon_zdata' /root/t65/${H}_${c%%:*}.log | tail -5 | tr '\n' ' ')" >> $L
done
export PS_MON_GEN=$A/t104/mon_both1.py
for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
  HWD=$H GLS_SDF_FIELD=${c##*:} timeout 5400 bash gate.sh $K ${c%%:*}
  python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/${H}_${c%%:*}.log 2 > /root/t90/${H}_${c%%:*}_oracle.txt 2>&1
  echo "gate ${c%%:*}: $(tail -1 /root/t90/${H}_${c%%:*}_oracle.txt); nonzero LATCH/STEER violations $(grep -E 'LATCHMON|STEERMON' /root/t65/${H}_${c%%:*}.log | grep -cE 'violations=[1-9]'); min latch setup $(grep LATCHMON /root/t65/${H}_${c%%:*}.log | tail -80 | sed 's/.*min_setup_ps=\([0-9-]*\).*/\1/' | sort -n | head -1)" >> $L
done
unset PS_MON_GEN MON_KERNEL
bash ../t100/run_per_xs.sh $H; echo "per: $(tail -3 /root/t90/per_$H.log 2>/dev/null | tr '\n' ' ')" >> $L
for c in fastmin worst slowmax; do JSON=$A/t126/h_${H}_$c.json PATHS=0 python3 ../t109/rule_h.py /root/t65/work_${H}_mon1_$c /root/t65/$H/${K}_bench_gen_routed.json > $A/t126/rule_h_${H}_$c.txt 2>&1
  echo "ruleH $c: $(grep -m1 margin $A/t126/rule_h_${H}_$c.txt | cut -c1-120)" >> $L; done
python3 ../t93/sites_any.py $H $K 33 7f0c0592 >> $L 2>&1
echo DONE >> $L; echo DONE > /root/t126k.done
