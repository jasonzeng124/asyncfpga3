#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
SEED=6 ./route.sh > /root/r23work/route6d.log 2>&1; cp /root/r23work/route6d.log .
TEND=30000 ./run_point2.sh bq2_6_logn175 0.28 0.2205 all GLS_SCATTER_LOGN=1
python3 -I ../tools/lapcheck.py /root/r23work/bq2_6_logn175 > lapcheck_bq2_6_logn175.txt 2>&1
