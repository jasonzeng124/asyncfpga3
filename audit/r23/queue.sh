#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
while pgrep -f "run_point.sh s2x " >/dev/null; do sleep 20; done
./run_point.sh fix_uori3 0.32 0.252 7,8,12 GLS_SCALE_INST=urig.udut.uori3.udly.:2.033
./run_point.sh placebo_uori4 0.32 0.252 7,8,12 GLS_SCALE_INST=urig.udut.uori4.udly.:2.033
./run_point.sh s1x 0.16 0.126 7,8,12,6
