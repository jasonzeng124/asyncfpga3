#!/usr/bin/env bash
# T84: xorshift levers 3 (l3) and 5 (l5) of research's 15 ns lead (bb155ecf). usage: build_lev.sh l3|l5 SEED
set -u
V=$1; S=$2; R=/root/wt-r84; cd $R/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
SZ=../research/data/xorshift_sizes_T3s50_bench.vh
case $V in x50) KN="";; l3) KN="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0";; l5) KN="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_NO_LINK=ulink_n30__1";; pmr) KN="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0";; pmf) KN="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1";; esac
echo "T67 build $V seed $S $(date -u) research $(cat $R/PROVENANCE)"
echo "\$ $KN NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh xorshift"
env $KN NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh xorshift
echo "exit $?"; echo "olink count: $(grep -c ucontrol_merge0_olink build/gen/xorshift_kernel_bench.v)"
D=build/hw/xorshift_bench_gen; md5sum $D/xorshift_bench_gen.sdf $D/xorshift_bench_gen.bit $SZ
O=/root/t67/${V}_$S; mkdir -p $O; cp $D/xorshift_bench_gen.{bit,sdf} $D/xorshift_bench_gen_routed.json $D/toolchain.txt $O/; cp $D/*.fasm $O/ 2>/dev/null; cp build/gen/xorshift_kernel_bench.v $O/
echo BUILDDONE
