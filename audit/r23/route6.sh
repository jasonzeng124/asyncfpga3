#!/usr/bin/env bash
# Route BQ#2 (R5 sizes, pads, v4) with NEXTPNR_SEED=6 in the clean research worktree; xray SDF; md5s.
set -u
source /root/audit-tc/openxc7/export.sh
cd /root/wt-r14/cells
NEXTPNR_SEED=6 BD_SIZES=../research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw
echo "build exit $?"
md5sum build/hw/gcd_hw/gcd_hw.bit build/hw/gcd_hw/gcd_hw_routed.json build/hw/gcd_hw/gcd_hw.sdf
cd /root/wt-r14/cells
PYTHONPATH=/root/audit-tc/openxc7-src/prjxray python3 gls/fid/xray_delay.py --routed build/hw/gcd_hw/gcd_hw_routed.json --sdf build/hw/gcd_hw/gcd_hw.sdf --out build/hw/gcd_hw/gcd_hw_xray.sdf
echo "xray exit $? db $(git -C /root/dev2/lib/xray/prjxray-db rev-parse --short HEAD 2>/dev/null)"
md5sum build/hw/gcd_hw/gcd_hw_xray.sdf
