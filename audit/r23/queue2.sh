#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
while kill -0 6328 2>/dev/null; do sleep 20; done
./run_point.sh fix_uori3 0.32 0.252 7,8,12 GLS_SCALE_INST=$(cat scale_uori3.txt)
./run_point.sh placebo_uori4 0.32 0.252 7,8,12 GLS_SCALE_INST=$(cat scale_uori4.txt)
