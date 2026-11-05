#!/usr/bin/env bash
# T25: own reconstruction of item 4's collatz T3 route, seed 1 (command from research JOURNAL 21:30 + fusion_bench's
# --mlir help; the item-4 queue script itself is not committed).
set -u
source /root/audit-tc/openxc7/export.sh
cd /root/wt-r14 && { echo "research $(git rev-parse HEAD)"
  BD_DSP=1 timeout 7000 python3 bdc/fusion_bench.py --mlir cloud/fixtures/frontend/collatz/comp/handshake_transformed.mlir \
    --sizes research/data/collatz_sizes_T3.vh --route --nextpnr-seeds 1 --output /root/t25/collatz; echo "fusion_bench exit $?"
  find /root/t25/collatz -name "soak*.sdf" -o -name "soak.fasm" -o -name "soak_routed.json" | xargs -r md5sum; } > /root/t25/route.log 2>&1
cp /root/t25/route.log /home/user/asyncfpga3/audit/t25/; echo ALLDONE >> /home/user/asyncfpga3/audit/t25/route.log
