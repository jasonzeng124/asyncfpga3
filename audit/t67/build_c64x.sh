#!/usr/bin/env bash
# T77: collatz64 "c64fm" = T4cdb (select-safe) + BDC_CONST_DATA=1 + BDC_MERGE_OUT_LINK=ucontrol_merge0 + BDC_LINK_FASTFALL=1. usage: SEED
set -u
S=$1; R=/root/wt-r84; cd $R/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
SZ=../research/data/collatz64_sizes_T4cdb_bench.vh
echo "T71 build c64fm seed $S $(date -u) research $(cat $R/PROVENANCE)"
env BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 ${EXTRA:-} NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh collatz64
echo "exit $?"; echo "olink: $(grep -c ucontrol_merge0_olink build/gen/collatz64_kernel_bench.v) const: $(grep -c "<< 64'h1" build/gen/collatz64_kernel_bench.v)"
D=build/hw/collatz64_bench_gen; md5sum $D/collatz64_bench_gen.sdf $D/collatz64_bench_gen.bit $SZ
O=/root/t65/${TAGO:-c64fm}_$S; mkdir -p $O; cp $D/collatz64_bench_gen.{bit,sdf,fasm} $D/collatz64_bench_gen_routed.json $D/toolchain.txt $O/; cp build/gen/collatz64_kernel_bench.v $O/
echo BUILDDONE
