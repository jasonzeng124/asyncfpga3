#!/usr/bin/env bash
# T102: research 619ac3c2: fxf3 seed 4 (sdf b1e3c2b0) hold_trace -612 ps at ulink_n_trueResult_10 though the gate passes.
# Own build + FAST_MIN with own latch monitor (own 17 vectors) + own long vectors (t91/xs_long.hex).
cd /home/user/asyncfpga3/audit/t91
SZ=../research/data/xorshift_sizes_T3s50_fr2_bench.vh R=/root/wt-r91 bash build_lev.sh xf3 4 > /root/t90/build_xf3_4.log 2>&1
cd ../t90; export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py MON_KERNEL=/root/t65/xf3_4/xorshift_kernel_bench.v
HWD=xf3_4 GLS_SDF_FIELD=min bash gate.sh xorshift mon_fastmin &
sleep 30; VEC=/home/user/asyncfpga3/audit/t91/xs_long.hex HWD=xf3_4 GLS_SDF_FIELD=min TBATCH=4000000 bash ../t91/gate_vec.sh xorshift long_fastmin; wait
python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xf3_4_mon_fastmin.log 2 > /root/t90/xf3_4_mon_fastmin_oracle.txt 2>&1
python3 ../t65/oracle_xorshift.py check ../t91/xs_long.hex /root/t65/xf3_4_long_fastmin.log 2 > /root/t90/xf3_4_long_fastmin_oracle.txt 2>&1
echo DONE > /root/t102.done
