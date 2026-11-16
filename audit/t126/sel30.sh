#!/usr/bin/env bash
# T126d: item 30 (c64sel3_10) FAST_MIN with the own select-arrival classifier (t116/mon_sel.py) on umux0..2:
# t83's MUXMON counts any select change with z_req=1 per pin (includes z_ack=1); mon_sel splits A (req=1, ack=0) from B / C.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t116/mon_sel.py MON_KERNEL=/root/t65/c64sel3_10/collatz64_kernel_bench.v MON_MUXES=umux0,umux1,umux2
HWD=c64sel3_10 GLS_SDF_FIELD=min timeout 5400 bash gate.sh collatz64 sel_fastmin
python3 ../t65/oracle_collatz64.py check ../t65/collatz64_14.hex /root/t65/c64sel3_10_sel_fastmin.log 2 > /root/t90/c64sel3_10_sel_fastmin_oracle.txt 2>&1
echo DONE > /root/t126d.done
