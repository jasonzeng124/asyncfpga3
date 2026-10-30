#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
while pgrep -f queue4.sh >/dev/null; do sleep 20; done
SEED=7 ./route.sh > route7.log 2>&1
./run_point2.sh s7_2x 0.32 0.252 all
