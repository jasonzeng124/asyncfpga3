#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
while pgrep -f queue3.sh >/dev/null; do sleep 20; done
mkdir -p ~/bq2s8 && cp /root/wt-r14/cells/build/hw/gcd_hw/gcd_hw_routed.json /root/wt-r14/cells/build/hw/gcd_hw/gcd_hw*.sdf ~/bq2s8/
SEED=4 ./route.sh > route4.log 2>&1
FIELD=max ./run_point2.sh s4_max 0 0 all
