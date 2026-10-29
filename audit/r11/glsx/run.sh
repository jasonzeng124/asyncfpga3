#!/bin/bash
# usage: run.sh <checkout> <tag>
set -e
src=$1/cells/gls; tag=$2; W=~/r11work/glsx; mkdir -p $W; D=$(dirname $(readlink -f $0)); R8=$D/../../r8/glsx
for tb in $R8/tb_x.v $R8/tb_saf.v $R8/tb_pulse.v $D/tb_mpw.v; do
  n=$(basename $tb .v)
  for mode in def fid; do
    def=""; [ $mode = fid ] && def="-DGLS_FID"
    iverilog -gspecify $def -I$src -o $W/$n-$tag-$mode.vvp $tb $src/prims.v > $D/log/$n-$tag-$mode.compile 2>&1
    vvp -n $W/$n-$tag-$mode.vvp +META_VERBOSE=1 > $D/log/$n-$tag-$mode.out 2>&1
  done
done
