#!/usr/bin/env bash
# T45: BOARD-QUEUE #7 build commands verbatim. usage: build.sh s75|t4
set -u
C=$1; cd /root/wt-r34/cells
source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
case $C in s75) SZ=../research/data/collatz64_sizes_T4s75_bench.vh;; t4) SZ=../research/data/collatz64_sizes_T4_bench.vh;; esac
echo "T45 build $C $(date -u)"
echo "\$ NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh collatz64"
NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh collatz64
echo "exit $?"
D=build/hw/collatz64_bench_gen
md5sum $D/collatz64_bench_gen.sdf $D/collatz64_bench_gen.bit $D/collatz64_bench_gen_routed.json $SZ
echo "DONE $(date -u)"
