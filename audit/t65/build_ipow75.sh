#!/usr/bin/env bash
# T65/T64 follow-up: board item 7 (ipow x0.75, T9s75_bench, seed 1; BOARD-QUEUE sdf 95a362ff) for a FAST_MIN run
set -u
R=/root/wt-r65; cd $R/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
SZ=../research/data/ipow_dsp1_sizes_T9s75_bench.vh
echo "T65 build ipow s75 seed 1 $(date -u) research $(cat $R/PROVENANCE)"
NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh ipow
echo "exit $?"; D=build/hw/ipow_bench_gen; md5sum $D/ipow_bench_gen.sdf $D/ipow_bench_gen.bit $SZ
mkdir -p /root/t65/ipow75; cp $D/ipow_bench_gen.{bit,sdf} $D/ipow_bench_gen_routed.json $D/toolchain.txt /root/t65/ipow75/
echo BUILDDONE
