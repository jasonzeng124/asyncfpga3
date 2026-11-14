#!/usr/bin/env bash
# T106: BOARD-QUEUE item 23 (#24, research bf5289ce): xf4 seed 10, recipe sdf 2f825834.
cd /home/user/asyncfpga3/audit/t91
git -C /root/wt-r91 fetch -q origin; git -C /root/wt-r91 checkout -q --detach origin/claude/research
SZ=../research/data/xorshift_sizes_T3s50_fr3_bench.vh R=/root/wt-r91 bash build_lev.sh xf4 10 > /root/t90/build_xf4_10.log 2>&1
python3 ../t67/scan_ff_own.py /root/t65/xf4_10/*.fasm > /root/t90/ff_xf4_10.txt 2>&1
cd ../t90; export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/xf4_10/xorshift_kernel_bench.v
bash ../t100/run_per_xs.sh xf4_10 &
sleep 20; ( for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do HWD=xf4_10 GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
  python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xf4_10_${c%%:*}.log 2 > /root/t90/xf4_10_${c%%:*}_oracle.txt 2>&1; done ) &
sleep 20; VEC=/home/user/asyncfpga3/audit/t91/xs_long.hex HWD=xf4_10 GLS_SDF_FIELD=min TBATCH=4000000 bash ../t91/gate_vec.sh xorshift long_fastmin
python3 ../t65/oracle_xorshift.py check ../t91/xs_long.hex /root/t65/xf4_10_long_fastmin.log 2 > /root/t90/xf4_10_long_fastmin_oracle.txt 2>&1
wait; echo DONE > /root/t106.done
