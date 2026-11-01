#!/usr/bin/env bash
# T10: BOARD-QUEUE #4 (gcd_ps, P1 sizes) route at the default seed d, from research bfa659b4 (wt-r14, clean), own run.
set -u
source /root/audit-tc/openxc7/export.sh
cd /root/wt-r14 && echo "HEAD $(git rev-parse HEAD) dirty=$(git status --short | wc -l)"
cd cells
unset NEXTPNR_SEED NEXTPNR_FREQ
BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 BD_SIZES=../research/data/gcd_ps/gcd_ps_sizes_P1.vh ./hw/build_hw.sh gcd_ps
echo "build exit $?"
O=build/hw/gcd_ps
md5sum $O/gcd_ps.fasm $O/gcd_ps.sdf $O/gcd_ps.bit $O/gcd_ps_routed.json
PYTHONPATH=/root/audit-tc/openxc7-src/prjxray python3 gls/fid/xray_delay.py --routed $O/gcd_ps_routed.json --sdf $O/gcd_ps.sdf --out $O/gcd_ps_xray.sdf
echo "xray exit $?"; md5sum $O/gcd_ps_xray.sdf
cmp -l $O/gcd_ps.bit /root/t10/f.bit | head -20; echo "cmp differing bytes: $(cmp -l $O/gcd_ps.bit /root/t10/f.bit | wc -l)"
echo ROUTE_DONE
