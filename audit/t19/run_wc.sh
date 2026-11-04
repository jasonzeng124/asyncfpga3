#!/usr/bin/env bash
# T19: research's combined worst case on BQ#2 seed 6 (own route /root/bq2s6_hw, bit 716bc601, xray 1f7f03ea):
# LUT + wire band 0.288; CARRY4/SELMUX2_1/SLICE_FFX at SLOW_MAX; bd_delay chain LUTs at 0.21 (own src-line selection,
# t19/chains_bq2s6_021.band); M scatter = region 0.02 + wire 0.126 (mode wire, draw seed ${SSEED:-1}).  Own r23/run_point2.sh + lapcheck.
set -u
TAG=bq2_6_wc_s${SSEED:-1}
HW=/root/bq2s6_hw/gcd_hw /home/user/asyncfpga3/audit/r23/run_point2.sh $TAG 0.02 0.126 all GLS_SDF_BAND=0.288 \
  GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1 GLS_SDF_BAND_INST=@/root/t19/chains_bq2s6_021.band GLS_SCATTER_SEED=${SSEED:-1}
echo "research $(git -C /root/wt-r14 rev-parse HEAD)" >> /root/r23work/$TAG.log
python3 -I /home/user/asyncfpga3/audit/tools/lapcheck.py /root/r23work/$TAG >> /root/r23work/$TAG.log 2>&1
mv /root/r23work/$TAG.log /home/user/asyncfpga3/audit/t19/; rm -f /home/user/asyncfpga3/audit/r23/$TAG.log; rm -rf /root/r23work/$TAG
echo ALLDONE >> /home/user/asyncfpga3/audit/t19/$TAG.log
