#!/usr/bin/env bash
# T97: reproduce research's fxf2 seed 1 FAST_MIN failure (a491c2b4): item 17's knobs + xorshift_sizes_T3s50_fr2_bench.vh,
# own build at wt-r91, FAST_MIN with t83 monitors, own 17 vectors and oracle; then worst and SLOW_MAX.
cd /home/user/asyncfpga3/audit/t91
SZ=../research/data/xorshift_sizes_T3s50_fr2_bench.vh R=/root/wt-r91 bash build_lev.sh xf2 1 > /root/t90/build_xf2_1.log 2>&1
cd ../t90; V=../t65/xorshift_17.hex; export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py MON_KERNEL=/root/t65/xf2_1/xorshift_kernel_bench.v
for c in mon_fastmin:min mon_worst:band mon_slowmax:max; do HWD=xf2_1 GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
  python3 ../t65/oracle_xorshift.py check $V /root/t65/xf2_1_${c%%:*}.log 2 > /root/t90/xf2_1_${c%%:*}_oracle.txt 2>&1; done
echo DONE > /root/t97.done
