#!/usr/bin/env bash
# T48: BOARD-QUEUE #9 build commands verbatim. usage: build.sh cs|t3
set -u
C=$1; cd /root/wt-r34/cells
source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
case $C in cs) SZ=../research/data/collatz_sizes_T3cs_bench.vh;; t3) SZ=../research/data/collatz_sizes_T3_bench.vh;; esac
echo "T48 build $C $(date -u)"
echo "\$ verify/toolchain.sh"; ./verify/toolchain.sh 2>&1 | tail -15
echo "\$ NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh collatz"
NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh collatz
echo "exit $?"
D=build/hw/collatz_bench_gen
md5sum $D/collatz_bench_gen.sdf $D/collatz_bench_gen.bit $D/collatz_bench_gen_routed.json $SZ
echo "DONE $(date -u)"
