#!/usr/bin/env bash
# T24: own rebuild of runt_top (research README: `cd cells && BD_RLOC=none NEXTPNR_FREQ=50 hw/build_hw.sh runt_top` at acf6957f)
set -u
source /root/audit-tc/openxc7/export.sh
cd /root/wt-r14/cells && { echo "research $(git rev-parse HEAD)"; BD_RLOC=none NEXTPNR_FREQ=50 ./hw/build_hw.sh runt_top; echo "build exit $?"
  md5sum build/hw/runt_top/runt_top.bit build/hw/runt_top/runt_top.sdf build/hw/runt_top/runt_top.fasm build/hw/runt_top/runt_top_routed.json; } > /root/t24/build.log 2>&1
cp /root/t24/build.log /home/user/asyncfpga3/audit/t24/build.log; echo ALLDONE >> /home/user/asyncfpga3/audit/t24/build.log
