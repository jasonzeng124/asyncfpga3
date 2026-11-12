#!/usr/bin/env bash
# T65: BOARD-QUEUE #10 / #13 build commands verbatim (research 4c977781), seed 1. usage: build.sh collatz|collatz64
set -u
K=$1; R=/root/wt-r65; cd $R/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
case $K in collatz) SZ=../research/data/collatz_sizes_T3cdb_bench.vh; PAT="<< 32'h1";;
           collatz64) SZ=../research/data/collatz64_sizes_T4cdb_bench.vh; PAT="<< 64'h1";; esac
echo "T65 build $K $(date -u) research $(cat $R/PROVENANCE)"; ./verify/toolchain.sh 2>&1 | tail -3
echo "\$ BDC_CONST_DATA=1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh $K"
BDC_CONST_DATA=1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh $K
echo "exit $?"; echo "flag took effect ($PAT count): $(grep -c "$PAT" build/gen/${K}_kernel_bench.v)"
echo "kernel vs audit's fixture emit: $(cmp build/gen/${K}_kernel_bench.v /root/t65/gen/${K}_kernel_bench.v && echo IDENTICAL)"
D=build/hw/${K}_bench_gen; md5sum $D/${K}_bench_gen.sdf $D/${K}_bench_gen.bit $D/${K}_bench_gen_routed.json $SZ
mkdir -p /root/t65/$K; cp $D/${K}_bench_gen.{bit,sdf} $D/${K}_bench_gen_routed.json $D/toolchain.txt /root/t65/$K/ 2>/dev/null
echo BUILDDONE
