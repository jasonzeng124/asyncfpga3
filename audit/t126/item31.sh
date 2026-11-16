#!/usr/bin/env bash
# T126c: BOARD-QUEUE item 31 (collatz item 28 + uselect0 7 / uaddi0 9, nl6s3a, pre_eq2, seed 20, recipe sdf 7aefc4bd).
# Waits for t126/run.sh. Own build (research HEAD), md5, usinkeq2, FF scan, period (run_per.sh), GLS 3 corners with own
# oracle + t104 latch/steer/mux monitors, own rule H and rule E.
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91
until [ -f /root/t126.done ]; do sleep 60; done
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
cd $A/t90; L=/root/t126c.log; echo "research $(git -C $R rev-parse --short HEAD) $(date -u)" > $L
F=$R/build/frontend/collatz/comp/handshake_transformed.mlir
cp $F /root/t126c_col_orig.mlir; cp $R/research/data/fifteen/collatz_preeq2.mlir $F
R=$R bash build.sh colsel3a 20 > /root/t90/build_colsel3a_20.log 2>&1
cp /root/t126c_col_orig.mlir $F
H=colsel3a_20; K=collatz
echo "build: $(grep -E 'bench_gen.sdf$' /root/t90/build_colsel3a_20.log | grep -v -- '->'); usinkeq2 $(grep -c usinkeq2 /root/t65/$H/${K}_kernel_bench.v)" >> $L
python3 ../t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff: $(tail -1 /root/t90/ff_$H.txt)" >> $L
bash run_per.sh collatz $H; echo "per: $(grep BENCHRES /root/t90/per_$H.log | tail -2 | tr '\n' ' ')" >> $L
export PS_MON_GEN=$A/t104/mon_both1.py MON_KERNEL=/root/t65/$H/${K}_kernel_bench.v
for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
  HWD=$H GLS_SDF_FIELD=${c##*:} timeout 5400 bash gate.sh $K ${c%%:*}
  python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/${H}_${c%%:*}.log 2 > /root/t90/${H}_${c%%:*}_oracle.txt 2>&1
  echo "gate ${c%%:*}: $(tail -1 /root/t90/${H}_${c%%:*}_oracle.txt); nonzero violations $(grep -cE 'violations=[1-9]|HVIOL' /root/t65/${H}_${c%%:*}.log)" >> $L
done
unset PS_MON_GEN MON_KERNEL
for c in fastmin worst slowmax; do JSON=$A/t126/h_${H}_$c.json PATHS=0 python3 ../t109/rule_h.py /root/t65/work_${H}_mon1_$c /root/t65/$H/${K}_bench_gen_routed.json > $A/t126/rule_h_${H}_$c.txt 2>&1
  echo "ruleH $c: $(grep -m1 margin $A/t126/rule_h_${H}_$c.txt | cut -c1-120)" >> $L; done
python3 ../t93/sites_any.py $H $K 31 7aefc4bd >> $L 2>&1
echo DONE >> $L; echo DONE > /root/t126c.done
