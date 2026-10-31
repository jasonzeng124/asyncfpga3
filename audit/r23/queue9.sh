#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
SEED=3 ./route.sh > route3.log 2>&1
FIELD=max ./run_point2.sh s3_max 0 0 all
