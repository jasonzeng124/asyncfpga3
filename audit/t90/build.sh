#!/usr/bin/env bash
# T90: pre-audit of research lever 5 on collatz64/collatz (research 6e62b264..3d04e32a).
# c64r = T4cdb + CONST_DATA + MERGE_OUT_LINK + LINK_FASTFALL + MERGE_RES_LINK (board item 21 recipe, as T88);
# c64nl = c64r + BDC_NO_LINK=ulink_n30__1.  colr = item 20 recipe (T87); colnl = colr + BDC_NO_LINK=ulink_n28__1.
# usage: build.sh c64r|c64nl|colr|colnl SEED
set -u
V=$1; S=$2; R=${R:-/root/wt-r90}; cd $R/cells; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
BASE="BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0"
case $V in
  c64r)  K=collatz64; SZ=../research/data/collatz64_sizes_T4cdb_bench.vh; KN="$BASE";;
  c64nl) K=collatz64; SZ=../research/data/collatz64_sizes_T4cdb_bench.vh; KN="$BASE BDC_NO_LINK=ulink_n30__1";;
  colr)  K=collatz;   SZ=../research/data/collatz_sizes_T3cdb_bench.vh;   KN="$BASE";;
  colnl) K=collatz;   SZ=../research/data/collatz_sizes_T3cdb_bench.vh;   KN="$BASE BDC_NO_LINK=ulink_n28__1";;
esac
echo "T90 build $V seed $S $(date -u) research $(git -C $R rev-parse --short HEAD)"
echo "\$ $KN NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh $K"
env $KN NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$SZ ./hw/build_bench.sh $K
echo "exit $?"
G=build/gen/${K}_kernel_bench.v
echo "olink: $(grep -c ucontrol_merge0_olink $G) rlink: $(grep -c 'ucontrol_merge0_rlink (' $G) n30__1: $(grep -c 'ulink_n30__1 ' $G) n28__1: $(grep -c 'ulink_n28__1 ' $G)"
D=build/hw/${K}_bench_gen; md5sum $D/${K}_bench_gen.sdf $D/${K}_bench_gen.bit $SZ
O=/root/t65/${V}_$S; mkdir -p $O; cp $D/${K}_bench_gen.{bit,sdf,fasm} $D/${K}_bench_gen_routed.json $D/toolchain.txt $O/ 2>/dev/null; cp $G $O/
echo BUILDDONE
