#!/usr/bin/env bash
# T64: board item #7 (collatz64 x0.75, seed 1) rebuilt, then FAST_MIN (SDF min column) full stack at 83.3 MHz
cd /home/user/asyncfpga3/audit/t45
bash build.sh s75 > /home/user/asyncfpga3/audit/t64/build7.log 2>&1
mkdir -p /root/t45/s75; D=/root/wt-r34/cells/build/hw/collatz64_bench_gen; cp $D/collatz64_bench_gen.{bit,sdf} $D/collatz64_bench_gen_routed.json $D/toolchain.txt /root/t45/s75/
GLS_SDF_FIELD=min bash run_worst.sh s75_fastmin
cp /root/t45/s75_fastmin.log /home/user/asyncfpga3/audit/t64/
echo CHAIN7DONE > /home/user/asyncfpga3/audit/t64/chain7.done
