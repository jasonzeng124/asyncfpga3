#!/usr/bin/env bash
# T126g: item 31 (colsel3a_20) FAST_MIN with the own select-arrival classifier (t116/mon_sel.py) on umux0..2 (t83 MUXMON: umux0 select 2 ps before z_req, 96 per-pin changes with z_req=1).

# t83's MUXMON counts any select change with z_req=1 per pin (includes z_ack=1); mon_sel splits A (req=1, ack=0) from B / C.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t116/mon_sel.py MON_KERNEL=/root/t65/colsel3a_20/collatz_kernel_bench.v MON_MUXES=umux0,umux1,umux2 ZACKS=umux0=bridge_i.udut.n14__0_ack,umux2=bridge_i.bench_o_ack
HWD=colsel3a_20 GLS_SDF_FIELD=min timeout 5400 bash gate.sh collatz sel_fastmin
python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/colsel3a_20_sel_fastmin.log 2 > /root/t90/colsel3a_20_sel_fastmin_oracle.txt 2>&1
echo DONE > /root/t126g.done
