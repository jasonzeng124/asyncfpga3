#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
SEED=9 ./route_bq3.sh > /root/r23work/route_bq3_9.log 2>&1; cp /root/r23work/route_bq3_9.log .
./run_point2.sh bq3_9_logn15 0.24 0.189 all GLS_SCATTER_LOGN=1
