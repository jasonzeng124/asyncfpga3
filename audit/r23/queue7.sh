#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
SEED=9 ./route.sh > route9.log 2>&1
FIELD=max ./run_point2.sh s9_max 0 0 all
