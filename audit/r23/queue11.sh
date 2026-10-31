#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
SEED=8 ./route.sh > route8b.log 2>&1
FIELD=max ./run_point2.sh s8_max 0 0 all
