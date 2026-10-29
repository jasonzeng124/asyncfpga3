#!/bin/bash
# Auditor r17 extra scatter draws on seed 9 (detached; GEN_ONLY: fasm2net output reused from g_band0 -- same .bit, deterministic)
A=/home/user/asyncfpga3/audit/r17
run() { tag=$1; mkdir -p ~/r17work/s9_$tag; [ -d ~/r17work/s9_$tag/fid ] || cp -r ~/r17work/g_band0/fid ~/r17work/s9_$tag/;
        GEN_ONLY=1 NJ=2 TEND=$5 python3 $A/driver.py $tag $2 $3 $4; }
run x1d1 0.16 0.126 1 150000
for d in 2 3 4 5 6 7; do run x2d${d}s 0.32 0.252 $d 30000; done
for d in 2 3 4; do run x1d${d}s 0.16 0.126 $d 30000; done
echo "$(date +%T) BATCH DONE" >> $A/driver.log
