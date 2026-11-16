#!/usr/bin/env bash
# T126j: BOARD-QUEUE item 29, second version (fisel3m: ipow h4 + select links at 3 + mux delays by rule M, seed 19, recipe
# sdf b521630f; research 83808aea5). Builds now; GLS after T130. Own md5 / FF scan; GLS 3 corners (oracle + t104 monitors);
# own z_data settle monitor (t130/mon_zdata.py, state A) at FAST_MIN; slope vs item 19; own rule H and rule E.
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91; L=/root/t126j.log; H=ipsel3m_19; K=ipow
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
cd $A/t90; echo "research $(git -C $R rev-parse --short HEAD) $(date -u)" > $L
R=$R bash build.sh ipsel3m 19 > /root/t90/build_$H.log 2>&1
echo "build: $(grep -E 'bench_gen.sdf$' /root/t90/build_$H.log | grep -v -- '->')" >> $L
python3 ../t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff: $(tail -1 /root/t90/ff_$H.txt)" >> $L
until [ -f /root/t130.done ]; do sleep 60; done
export PS_MON_GEN=$A/t104/mon_both1.py MON_KERNEL=/root/t65/$H/${K}_kernel_bench.v
for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
  HWD=$H GLS_SDF_FIELD=${c##*:} timeout 5400 bash gate.sh $K ${c%%:*}
  python3 ../t65/oracle_ipow.py check ../t65/ipow_17.hex /root/t65/${H}_${c%%:*}.log 2 > /root/t90/${H}_${c%%:*}_oracle.txt 2>&1
  echo "gate ${c%%:*}: $(tail -1 /root/t90/${H}_${c%%:*}_oracle.txt); nonzero LATCH/STEER violations $(grep -E 'LATCHMON|STEERMON' /root/t65/${H}_${c%%:*}.log | grep -cE 'violations=[1-9]'); min latch setup $(grep LATCHMON /root/t65/${H}_${c%%:*}.log | tail -80 | sed 's/.*min_setup_ps=\([0-9-]*\).*/\1/' | sort -n | head -1)" >> $L
done
echo "slope: $(python3 ../t67/ipow_slope.py /root/t90/ipowr_1_h_fastmin_oracle.txt /root/t90/${H}_mon1_fastmin_oracle.txt /root/t90/ipowr_1_h_worst_oracle.txt /root/t90/${H}_mon1_worst_oracle.txt | tr '\n' ' ')" >> $L
export PS_MON_GEN=$A/t130/mon_zdata.py
HWD=$H GLS_SDF_FIELD=min timeout 5400 bash gate.sh $K zd2_fastmin
echo "zdata: $(grep 'ZDMON t=\|mon_zdata' /root/t65/${H}_zd2_fastmin.log | tail -5 | tr '\n' ' ')" >> $L
unset PS_MON_GEN MON_KERNEL
for c in fastmin worst slowmax; do JSON=$A/t126/h_${H}_$c.json PATHS=0 python3 ../t109/rule_h.py /root/t65/work_${H}_mon1_$c /root/t65/$H/${K}_bench_gen_routed.json > $A/t126/rule_h_${H}_$c.txt 2>&1
  echo "ruleH $c: $(grep -m1 margin $A/t126/rule_h_${H}_$c.txt | cut -c1-120)" >> $L; done
python3 ../t93/sites_any.py $H $K 29 b521630f >> $L 2>&1
echo DONE >> $L; echo DONE > /root/t126j.done
