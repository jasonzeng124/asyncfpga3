#!/bin/bash
# BQ#2 seed 6 build (BOARD-QUEUE #2 command + NEXTPNR_SEED=6 as seeds_fid.py sets it)
source /root/audit-tc/openxc7/export.sh
cd /root/wt-r22/cells
export NEXTPNR_SEED=6
BD_SIZES=../research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw
rc=$?; echo "build_hw rc=$rc"
HW=/root/wt-r22/cells/build/hw/gcd_hw
XRAY_DB=/root/audit-tc/xray/prjxray-db/zynq7 PYTHONPATH=/root/audit-tc/openxc7-src/prjxray python3 /root/wt-r22/cells/gls/fid/xray_delay.py --routed $HW/gcd_hw_routed.json --sdf $HW/gcd_hw.sdf --out $HW/gcd_hw_xray.sdf
echo "xray rc=$?"
md5sum $HW/gcd_hw.sdf $HW/gcd_hw_xray.sdf $HW/gcd_hw_routed.json $HW/gcd_hw.bit
