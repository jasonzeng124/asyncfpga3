#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
while pgrep -f queue12.sh >/dev/null; do sleep 30; done
./route_bq1.sh > /root/r23work/route_bq1.log 2>&1; cp /root/r23work/route_bq1.log .
FIELD=max ./run_point2.sh bq1_d_max 0 0 all
