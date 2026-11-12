#!/usr/bin/env bash
# T86: FAST_MIN with all audit monitors on board routes: item 9 (collatz), 12 (collatz64), 7 (ipow75), 13 (ipowfm_1), 15 (colb_1), 4 (x50_1)
cd /home/user/asyncfpga3/audit/t65
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
r() { MON_KERNEL=$3 HWD=$2 GLS_SDF_FIELD=min bash run2.sh $1 mon_fastmin; }
(r collatz collatz /root/t65/gen/collatz_kernel_bench.v; r ipow ipow75 /root/t65/gen/ipow_kernel_bench.v; r collatz colb_1 /root/t65/colb_1/collatz_kernel_bench.v) &
sleep 60
(r collatz64 collatz64 /root/t65/gen/collatz64_kernel_bench.v; r ipow ipowfm_1 /root/t65/gen/ipowfm_kernel_bench.v; r xorshift x50_1 /root/t67/x50_1/xorshift_kernel_bench.v) &
wait; echo DONE > lanes88.done
