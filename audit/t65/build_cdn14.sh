#!/usr/bin/env bash
# T65: DIAGNOSIS TEST: held T4cd with ulink_n14__1 / SDELAY back at T4 (19 / 2) (BDC_CONST_DATA=1, T4cd_bench) bench route seed 7 -- research: FAST_MIN FAIL 12/14
set -u
R=/root/wt-r65; cd $R/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
SZ=/home/user/asyncfpga3/audit/t65/sizes_T4cd_n14r_bench.vh
echo "T65 build T4cd seed 7 $(date -u) research $(cat $R/PROVENANCE)"
echo "\$ BDC_CONST_DATA=1 NEXTPNR_SEED=7 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh collatz64"
BDC_CONST_DATA=1 NEXTPNR_SEED=7 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh collatz64
echo "exit $?"; D=build/hw/collatz64_bench_gen; md5sum $D/collatz64_bench_gen.sdf $D/collatz64_bench_gen.bit $SZ
mkdir -p /root/t65/cdn14; cp $D/collatz64_bench_gen.{bit,sdf} $D/collatz64_bench_gen_routed.json $D/toolchain.txt /root/t65/cdn14/
echo BUILDDONE
