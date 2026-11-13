#!/usr/bin/env bash
# T67: ipowfm (ipow x0.75 sizes + BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1, BD_DSP=1). usage: build_ipowfm.sh SEED
set -u
S=$1; R=/root/wt-r84; cd $R/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
SZ=../research/data/ipow_dsp1_sizes_T9s75_bench.vh
echo "T67 build ipowfm seed $S $(date -u) research $(cat $R/PROVENANCE)"
env BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 ${EXTRA:-} NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh ipow
echo "exit $?"; echo "olink: $(grep -c ucontrol_merge0_olink build/gen/ipow_kernel_bench.v)"
D=build/hw/ipow_bench_gen; md5sum $D/ipow_bench_gen.sdf $D/ipow_bench_gen.bit $SZ
O=/root/t65/${TAGO:-ipowfm}_$S; mkdir -p $O; cp $D/ipow_bench_gen.{bit,sdf,fasm} $D/ipow_bench_gen_routed.json $D/toolchain.txt $O/; cp build/gen/ipow_kernel_bench.v $O/
echo BUILDDONE
