#!/usr/bin/env bash
# T186: 2 GLS at a time (4 at once ran out of memory), each corner: v10 and v13local side by side
cd /home/user/asyncfpga3/audit/t186
for c in "fastmin min" "advA_ns band 0.20 0.31 1.0 0" "advC_ns band 0.20 0.20 1.0 0" "worst band" "slowmax max"; do
  ONE="$c" ./one.sh v10 & sleep 120; ONE="$c" ./one.sh v13local & wait
done
echo QDONE >> v10_gls.log; echo QDONE >> v13local_gls.log
