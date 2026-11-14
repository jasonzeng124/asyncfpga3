#!/usr/bin/env bash
# T99b: item 11 (p8mo seed 1, recipe sdf 1e51be7e) FAST_MIN with t83 monitors (hold sweep completion).
cd /home/user/asyncfpga3/audit/t91; R=/root/wt-r90 bash build_lev.sh p8mo 1 > /root/t90/build_p8mo_1.log 2>&1
cd ../t90; export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py MON_KERNEL=/root/t65/p8mo_1/xorshift_kernel_bench.v
HWD=p8mo_1 GLS_SDF_FIELD=min bash gate.sh xorshift mon_fastmin
python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/p8mo_1_mon_fastmin.log 2 > /root/t90/p8mo_1_mon_fastmin_oracle.txt 2>&1
echo DONE > /root/t99b.done
