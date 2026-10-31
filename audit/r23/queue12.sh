#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
SEED=5 ./route.sh > route5b.log 2>&1
FIELD=min ./run_point2.sh s5_min 0 0 all
