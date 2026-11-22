#!/usr/bin/env bash
# T182 queue (restart after the tb_ps TEND overflow): 2 GLS at a time.
cd /home/user/asyncfpga3/audit/t182
./split.sh unpadded split_c1_r0 1.0 0.0 & ./split.sh padded split_c1_r0 1.0 0.0 & wait
for c in "fastmin min" "advA_ns band 0.20 0.31 1.0 0" "advC_ns band 0.20 0.20 1.0 0" "worst band" "slowmax max"; do
  ONE="$c" ./one.sh unpadded & ONE="$c" ./one.sh padded & wait
done
echo ALLDONE >> split.log
