#!/usr/bin/env bash
# T130b: traced z_data monitor (t130/mon_zdata_trace.py) on item 28 (colsel3_20) umux0, FAST_MIN: which LUT input moved last
# before each of the first late output changes (select vs data), to explain the v2 control result (304/1279 tokens late).
cd /home/user/asyncfpga3/audit/t90
until [ -f /root/t130.done ]; do sleep 60; done
export PS_MON_GEN=/home/user/asyncfpga3/audit/t130/mon_zdata_trace.py ZACKS=umux0=bridge_i.udut.n14__0_ack MON_MUXES=umux0
MON_KERNEL=/root/t65/colsel3_20/collatz_kernel_bench.v HWD=colsel3_20 GLS_SDF_FIELD=min timeout 5400 bash gate.sh collatz zdt_fastmin
echo DONE > /root/t130b.done
