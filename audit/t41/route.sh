#!/usr/bin/env bash
# T41: own route of isprime_b (rule-E-6 pads, BD_DSP=1 BD_RLOC_ARB=1), nextpnr seed 30
set -u
source /root/audit-tc/openxc7/export.sh
cd /root/wt-r34
echo "start $(date -u)"; nextpnr-xilinx --version 2>&1 | head -1
BD_DSP=1 BD_RLOC_ARB=1 timeout 7000 python3 bdc/fusion_bench.py --mlir cloud/fixtures/frontend/isprime/comp/handshake_transformed.mlir \
  --sizes research/data/isprime_dsp1_rulee6_sizes.vh --route --nextpnr-seeds 30 --output /root/t41/isp_b
echo "fusion_bench exit $?  $(date -u)"
md5sum /root/t41/isp_b/seed30/pnr/soak.sdf /root/t41/isp_b/seed30/pnr/soak.fasm /root/t41/isp_b/seed30/pnr/soak_routed.json research/data/isprime_dsp1_rulee6_sizes.vh
echo ALLDONE
