#!/usr/bin/env bash
# T46: BOARD-QUEUE #8 build, exactly as written. usage: build.sh SIZES_VH TAG
cd /root/wt-r35/cells
source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
echo "T46 build $2 $(date -u)"
verify/toolchain.sh 2>&1 | tail -2
echo "\$ NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$1 ./hw/build_bench.sh ipow"
NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$1 /usr/bin/time -v ./hw/build_bench.sh ipow
echo "exit $?"
md5sum build/hw/ipow_bench_gen/ipow_bench_gen.sdf build/hw/ipow_bench_gen/ipow_bench_gen.bit build/hw/ipow_bench_gen/ipow_bench_gen_routed.json
echo BUILD_DONE
