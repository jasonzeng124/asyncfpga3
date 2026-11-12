#!/usr/bin/env bash
# T65: item 12 select-safe T4cdb on bench seed 7, the seed where T4cd failed at FAST_MIN
set -u
R=/root/wt-r65; cd $R/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
SZ=../research/data/collatz64_sizes_T4cdb_bench.vh
echo "T65 build T4cdb seed 7 $(date -u) research $(cat $R/PROVENANCE)"
echo "\$ BDC_CONST_DATA=1 NEXTPNR_SEED=7 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh collatz64"
BDC_CONST_DATA=1 NEXTPNR_SEED=7 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh collatz64
echo "exit $?"; D=build/hw/collatz64_bench_gen; md5sum $D/collatz64_bench_gen.sdf $D/collatz64_bench_gen.bit $SZ
mkdir -p /root/t65/cdbs7; cp $D/collatz64_bench_gen.{bit,sdf} $D/collatz64_bench_gen_routed.json $D/toolchain.txt /root/t65/cdbs7/
echo BUILDDONE
