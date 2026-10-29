#!/bin/bash
# Auditor r8: rebuild BQ#3 recipe at NEXTPNR_SEED=3 from a clean copy of ~/wt-r8 (no git), then xray SDF.
source ~/audit-tc/openxc7/export.sh >/dev/null 2>&1
export TC=~/audit-tc XRAY_DB=~/audit-tc/openxc7/share/nextpnr/prjxray-db/zynq7
W=~/r8work/wt-r8x; cd $W/cells
date
NEXTPNR_SEED=3 BD_SIZES=../research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 BDC_LINK_FASTFALL=1 ./hw/build_hw.sh gcd_hw
echo "BUILD EXIT $?"
HW=$W/cells/build/hw/gcd_hw
PYTHONPATH=$TC/openxc7-src/prjxray python3 $W/cells/gls/fid/xray_delay.py --routed $HW/gcd_hw_routed.json --sdf $HW/gcd_hw.sdf --out $HW/gcd_hw_xray.sdf
echo "XRAY EXIT $?"
md5sum $HW/gcd_hw.sdf $HW/gcd_hw_xray.sdf $HW/gcd_hw_routed.json $HW/gcd_hw.bit $HW/gcd_hw.fasm
date
