#!/usr/bin/env bash
# T101: spot check of research 3a4a4445 (fxf2h hold check): fxf2 seed 30 (tightest passing, +1421 ps) FAST_MIN with own latch monitor.
cd /home/user/asyncfpga3/audit/t91
SZ=../research/data/xorshift_sizes_T3s50_fr2_bench.vh R=/root/wt-r91 bash build_lev.sh xf2 30 > /root/t90/build_xf2_30.log 2>&1
cd ../t90; export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py MON_KERNEL=/root/t65/xf2_30/xorshift_kernel_bench.v
HWD=xf2_30 GLS_SDF_FIELD=min bash gate.sh xorshift mon_fastmin
python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xf2_30_mon_fastmin.log 2 > /root/t90/xf2_30_mon_fastmin_oracle.txt 2>&1
echo DONE > /root/t101.done
