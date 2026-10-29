#!/bin/bash
# Auditor r15: rebuild the 8 ro_many_top routes per ring128_summary.md "Commands", in a tar copy of ~/wt-r15.
source ~/audit-tc/openxc7/export.sh >/dev/null 2>&1
export TC=~/audit-tc XRAY_DB=~/audit-tc/openxc7/share/nextpnr/prjxray-db/zynq7
W=~/r15work/wt-ring; cd $W/cells
for s in "" 1 2 3 4 5 6 7; do
  date; echo "== seed ${s:-default}"
  if [ -n "$s" ]; then export NEXTPNR_SEED=$s; else unset NEXTPNR_SEED; fi
  BD_NO_TIGHTEN=1 BD_RLOC=none hw/build_hw.sh ro_many_top > ~/r15work/ring_build_${s:-default}.log 2>&1; echo "BUILD EXIT $?"
  tail -3 ~/r15work/ring_build_${s:-default}.log
  D=~/r15work/ro_many_seeds/${s:-default}; mkdir -p $D
  cp build/hw/ro_many_top/ro_many_top_routed.json build/hw/ro_many_top/ro_many_top.sdf $D/
  md5sum $D/* build/hw/ro_many_top/ro_many_top.bit
done
date
