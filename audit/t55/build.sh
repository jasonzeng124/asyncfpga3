#!/usr/bin/env bash
# T55: BOARD-QUEUE #11 build command verbatim (ipow BDC_CONST_DATA=1 + T9cdd sizes, seed 1), then copy the board files
set -u
cd /root/wt-r34/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
echo "T55 build $(date -u) $(cat /root/wt-r34/PROVENANCE)"; ./verify/toolchain.sh 2>&1 | tail -3
BDC_CONST_DATA=1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/ipow_dsp1_sizes_T9cdd_bench.vh ./hw/build_bench.sh ipow
echo "exit $?"; echo "flag took effect (>>> 32'h1 count): $(grep -c ">>> 32'h1" build/gen/ipow_kernel_bench.v)"
D=build/hw/ipow_bench_gen; md5sum $D/ipow_bench_gen.sdf $D/ipow_bench_gen.bit $D/ipow_bench_gen_routed.json
mkdir -p /root/t55/cd; cp $D/ipow_bench_gen.{bit,sdf} $D/ipow_bench_gen_routed.json /root/t55/cd/; echo BUILDDONE
