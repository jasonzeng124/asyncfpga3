#!/usr/bin/env bash
# T60: BOARD-QUEUE #12 build command verbatim (xorshift x0.5 + second latch, seed 1), then copy the board files
set -u
cd /root/wt-r34/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
echo "T60 build $(date -u) $(cat /root/wt-r34/PROVENANCE)"; ./verify/toolchain.sh 2>&1 | tail -3
BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=3 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_bench.vh ./hw/build_bench.sh xorshift
echo "exit $?"; echo "knobs took effect (ucontrol_merge0_olink count): $(grep -c ucontrol_merge0_olink build/gen/xorshift_kernel_bench.v)"
D=build/hw/xorshift_bench_gen; md5sum $D/xorshift_bench_gen.sdf $D/xorshift_bench_gen.bit $D/xorshift_bench_gen_routed.json ../research/data/xorshift_sizes_T3s50_bench.vh
mkdir -p /root/t60/p8s3; cp $D/xorshift_bench_gen.{bit,sdf} $D/xorshift_bench_gen_routed.json $D/toolchain.txt /root/t60/p8s3/ 2>/dev/null
echo BUILDDONE
