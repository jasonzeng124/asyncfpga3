#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
SEED=9 ./route_bq1s.sh > /root/r23work/route_bq1_9.log 2>&1; cp /root/r23work/route_bq1_9.log .
FIELD=max ./run_point2.sh bq1_9_max 0 0 all
