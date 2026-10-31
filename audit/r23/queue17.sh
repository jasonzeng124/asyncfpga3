#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
./route_bq1.sh > /root/r23work/route_bq1_d2.log 2>&1; cp /root/r23work/route_bq1_d2.log .
./run_point2.sh bq1_d_1x 0.16 0.126 all
