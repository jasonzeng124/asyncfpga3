#!/usr/bin/env bash
# T76: xorshift T3-size builds (step 5 check). usage: build_t3.sh t3|t3pmf SEED
set -u
V=$1; S=$2; R=/root/wt-r67; cd $R/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
SZ=../research/data/xorshift_sizes_T3_bench.vh
case $V in t3|x50) KN="";; pmf|t3pmf) KN="BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1";; esac
echo "T67 build $V seed $S $(date -u) research $(cat $R/PROVENANCE)"
echo "\$ $KN NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh xorshift"
env $KN NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh xorshift
echo "exit $?"; echo "olink count: $(grep -c ucontrol_merge0_olink build/gen/xorshift_kernel_bench.v)"
D=build/hw/xorshift_bench_gen; md5sum $D/xorshift_bench_gen.sdf $D/xorshift_bench_gen.bit $SZ
O=/root/t67/${V}_$S; mkdir -p $O; cp $D/xorshift_bench_gen.{bit,sdf} $D/xorshift_bench_gen_routed.json $D/toolchain.txt $O/; cp $D/*.fasm $O/ 2>/dev/null; cp build/gen/xorshift_kernel_bench.v $O/
echo BUILDDONE
