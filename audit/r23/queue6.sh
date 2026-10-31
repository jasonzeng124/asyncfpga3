#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
SEED=6 ./route.sh > route6b.log 2>&1
TEND=30000 ./run_point2.sh s6_2x_d2 0.32 0.252 all GLS_SCATTER_SEED=2
