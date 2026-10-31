#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
SEED=5 ./route.sh > route5.log 2>&1
FIELD=max ./run_point2.sh s5_max 0 0 all
