#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
SEED=6 ./route.sh > /root/r23work/route6c.log 2>&1; cp /root/r23work/route6c.log .
./run_point2.sh bq2_6_logn15 0.24 0.189 all GLS_SCATTER_LOGN=1
