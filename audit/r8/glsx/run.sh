#!/bin/bash
# usage: run.sh <checkout> <tag>; compiles tb_saf/tb_x/tb_pulse default and -DGLS_FID
set -e
src=$1/cells/gls; tag=$2; W=~/r8work/glsx; D=$(dirname $(readlink -f $0))
for tb in tb_saf tb_x tb_pulse; do
  for mode in def fid; do
    def=""; [ $mode = fid ] && def="-DGLS_FID"
    iverilog -gspecify $def -I$src -o $W/$tb-$tag-$mode.vvp $D/$tb.v $src/prims.v > $D/log/$tb-$tag-$mode.compile 2>&1
    vvp -n $W/$tb-$tag-$mode.vvp > $D/log/$tb-$tag-$mode.out 2>&1
  done
done
