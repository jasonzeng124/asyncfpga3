#!/usr/bin/env bash
# T53: BOARD-QUEUE #10 build command verbatim (collatz BDC_CONST_DATA=1 + per-cell sizes, seed 1), then copy the board files
set -u
cd /root/wt-r34/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
echo "T53 build $(date -u) research $(cat /root/wt-r34/PROVENANCE)"; ./verify/toolchain.sh 2>&1 | tail -3
BDC_CONST_DATA=1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3cd_bench.vh ./hw/build_bench.sh collatz
echo "exit $?"; echo "flag took effect (<< 32'h1 count): $(grep -c "<< 32'h1" build/gen/collatz_kernel_bench.v)"
D=build/hw/collatz_bench_gen; md5sum $D/collatz_bench_gen.sdf $D/collatz_bench_gen.bit $D/collatz_bench_gen_routed.json ../research/data/collatz_sizes_T3cd_bench.vh
mkdir -p /root/t53/cd; cp $D/collatz_bench_gen.{bit,sdf} $D/collatz_bench_gen_routed.json $D/toolchain.txt /root/t53/cd/ 2>/dev/null
echo BUILDDONE
