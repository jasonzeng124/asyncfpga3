#!/usr/bin/env bash
# T60 base: BQ#12 second command (item 4 x0.5 route, no second latch, seed 1), then copy the board files
set -u
cd /root/wt-r34/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
echo "T60 build $(date -u) $(cat /root/wt-r34/PROVENANCE)"; ./verify/toolchain.sh 2>&1 | tail -3
NEXTPNR_SEED=3 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_bench.vh ./hw/build_bench.sh xorshift
echo "exit $?"; echo "knobs absent (olink count, expect 0): $(grep -c ucontrol_merge0_olink build/gen/xorshift_kernel_bench.v)"
D=build/hw/xorshift_bench_gen; md5sum $D/xorshift_bench_gen.sdf $D/xorshift_bench_gen.bit $D/xorshift_bench_gen_routed.json ../research/data/xorshift_sizes_T3s50_bench.vh
mkdir -p /root/t60/s50s3; cp $D/xorshift_bench_gen.{bit,sdf} $D/xorshift_bench_gen_routed.json $D/toolchain.txt /root/t60/s50s3/ 2>/dev/null
echo BUILDDONE
