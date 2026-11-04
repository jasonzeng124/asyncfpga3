#!/usr/bin/env bash
# T18: route BQ#3 (R5 sizes, pads, v4, BDC_LINK_FASTFALL=1) with NEXTPNR_SEED=$1 in the research worktree, own xray SDF,
# md5s, copy to /root/t18/bq3s$1; then the cell-type check (band 0.288, CARRY4/SELMUX2_1/SLICE_FFX = 1) on 16 vectors
# with the audit's own r23/run_point2.sh.  usage: route_cell.sh SEED
set -u
S=$1; L=/root/t18/route_bq3_$S.log
source /root/audit-tc/openxc7/export.sh
{ cd /root/wt-r14/cells && echo "research $(git rev-parse HEAD)"
  NEXTPNR_SEED=$S BD_SIZES=../research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 BDC_LINK_FASTFALL=1 ./hw/build_hw.sh gcd_hw
  echo "build exit $?"
  PYTHONPATH=/root/audit-tc/openxc7-src/prjxray python3 gls/fid/xray_delay.py --routed build/hw/gcd_hw/gcd_hw_routed.json --sdf build/hw/gcd_hw/gcd_hw.sdf --out build/hw/gcd_hw/gcd_hw_xray.sdf
  md5sum build/hw/gcd_hw/gcd_hw.bit build/hw/gcd_hw/gcd_hw.sdf build/hw/gcd_hw/gcd_hw_xray.sdf
  rm -rf /root/t18/bq3s$S; mkdir -p /root/t18/bq3s$S; cp -r build/hw/gcd_hw /root/t18/bq3s$S/
} > $L 2>&1
cp $L /home/user/asyncfpga3/audit/t18/
HW=/root/t18/bq3s$S/gcd_hw /home/user/asyncfpga3/audit/r23/run_point2.sh bq3_${S}_cellcheck 0 0 all GLS_SDF_BAND=0.288 GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1
cp /root/r23work/bq3_${S}_cellcheck.log /home/user/asyncfpga3/audit/t18/
echo ALLDONE >> /home/user/asyncfpga3/audit/t18/bq3_${S}_cellcheck.log
