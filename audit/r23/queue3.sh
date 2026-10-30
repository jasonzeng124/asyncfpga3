#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
while pgrep -f queue2.sh >/dev/null; do sleep 20; done
SEED=8 ./route.sh > route8.log 2>&1
./run_point2.sh s8_2x 0.32 0.252 all
