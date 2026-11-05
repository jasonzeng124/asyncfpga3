#!/usr/bin/env bash
# T25: own route of a frontend kernel K (fixture cloud/fixtures/frontend/$K) with sizes research/data/$SZ.vh, NEXTPNR seed $SEED,
# output /root/t25/$TAG (fusion_bench --mlir ... --route, BD_DSP=1).
set -u
source /root/audit-tc/openxc7/export.sh
cd /root/wt-r14 && { echo "research $(git rev-parse HEAD)"
  BD_DSP=1 timeout 7000 python3 bdc/fusion_bench.py --mlir cloud/fixtures/frontend/${K:-xorshift}/comp/handshake_transformed.mlir \
    --sizes research/data/${SZ}.vh --route --nextpnr-seeds ${SEED:-1} --output /root/t25/${TAG}; echo "fusion_bench exit $?"
  find /root/t25/${TAG} -name "soak*.sdf" -o -name "soak.fasm" -o -name "soak_routed.json" | xargs -r md5sum; } > /root/t25/${TAG}_route.log 2>&1
cp /root/t25/${TAG}_route.log /home/user/asyncfpga3/audit/t25/; echo ALLDONE >> /home/user/asyncfpga3/audit/t25/${TAG}_route.log
