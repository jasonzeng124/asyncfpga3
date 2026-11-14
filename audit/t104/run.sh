#!/usr/bin/env bash
# T104: item 19 board route (ipowr_1, sdf a6a2951b) FAST_MIN with 1-bit latch monitor (t104/mon_both1.py): own 17 vectors and
# a select-flipping set (e alternating 0 / k). Measures ulink_n_index_15 stage[0] setup and stage[1] hold (did stage 1 close
# before the value leaking through stage 0 arrived?).
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/ipowr_1/ipow_kernel_bench.v
HWD=ipowr_1 GLS_SDF_FIELD=min bash gate.sh ipow mon1_fastmin &
sleep 30; VEC=/home/user/asyncfpga3/audit/t104/ipow_flip.hex HWD=ipowr_1 GLS_SDF_FIELD=min bash ../t91/gate_vec.sh ipow flip_fastmin; wait
python3 ../t65/oracle_ipow.py check ../t65/ipow_17.hex /root/t65/ipowr_1_mon1_fastmin.log 2 > /root/t90/ipowr_1_mon1_fastmin_oracle.txt 2>&1
python3 ../t65/oracle_ipow.py check ../t104/ipow_flip.hex /root/t65/ipowr_1_flip_fastmin.log 2 > /root/t90/ipowr_1_flip_fastmin_oracle.txt 2>&1
echo DONE > /root/t104.done
