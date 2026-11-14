#!/usr/bin/env bash
# T105: collatz64 lever 5 seed 3 (c64nl_3, sdf 229a0f59): ulink_n_index_11 (select pipe) stage margins at FAST_MIN, own 1-bit latch monitor.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/c64nl_3/collatz64_kernel_bench.v
HWD=c64nl_3 GLS_SDF_FIELD=min bash gate.sh collatz64 mon1_fastmin
python3 ../t65/oracle_collatz64.py check ../t65/collatz64_14.hex /root/t65/c64nl_3_mon1_fastmin.log 2 > /root/t90/c64nl_3_mon1_fastmin_oracle.txt 2>&1
echo DONE > /root/t105.done
