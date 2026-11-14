#!/usr/bin/env bash
# T103: pre-audit xf4 seed 1 (research 0b26211c: xf3 + umux2 1->2, sizes fr3).
cd /home/user/asyncfpga3/audit/t91
SZ=../research/data/xorshift_sizes_T3s50_fr3_bench.vh R=/root/wt-r91 bash build_lev.sh xf4 1 > /root/t90/build_xf4_1.log 2>&1
cd ../t90; export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py MON_KERNEL=/root/t65/xf4_1/xorshift_kernel_bench.v
bash ../t100/run_per_xs.sh xf4_1 &
for c in mon_fastmin:min mon_worst:band mon_slowmax:max; do HWD=xf4_1 GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
  python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xf4_1_${c%%:*}.log 2 > /root/t90/xf4_1_${c%%:*}_oracle.txt 2>&1; done; wait
echo DONE > /root/t103.done
