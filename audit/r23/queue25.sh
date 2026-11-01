#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
./route_bq1.sh > /root/r23work/route_bq1_e.log 2>&1; cp /root/r23work/route_bq1_e.log .
./run_point2.sh bq1_d_logn15_d2 0.24 0.189 all GLS_SCATTER_LOGN=1 GLS_SCATTER_SEED=2
python3 -I ../tools/lapcheck.py /root/r23work/bq1_d_logn15_d2 > lapcheck_bq1_d_logn15_d2.txt 2>&1
