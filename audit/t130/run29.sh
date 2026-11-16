#!/usr/bin/env bash
# T130c: own z_data monitor (state A) on item 29 v2 (ipsel3m_19) umux0 / umux3, FAST_MIN (the T126j run mapped only umux1/2:
# their z_ack names; umux0.z_ack = ufork3's C-element = n17__0_ack, umux3.z_ack = out0_ack = bench_o_ack).
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t130/mon_zdata.py MON_MUXES=umux0,umux3 ZACKS=umux0=bridge_i.udut.n17__0_ack,umux3=bridge_i.bench_o_ack
MON_KERNEL=/root/t65/ipsel3m_19/ipow_kernel_bench.v HWD=ipsel3m_19 GLS_SDF_FIELD=min timeout 5400 bash gate.sh ipow zd3_fastmin
echo DONE > /root/t130c.done
