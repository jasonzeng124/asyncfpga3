#!/usr/bin/env bash
R=/home/user/asyncfpga3/audit/r19/run_point.sh
export TEND=20000
$R s1375 0.22 0.17325 2,13,6
$R s125 0.20 0.1575 2,13,6
$R s2x_logn 0.32 0.252 2,13,6 GLS_SCATTER_LOGN=1
$R s13125 0.21 0.165375 2,13,6
export TEND=30000
$R s1x 0.16 0.126 all
echo ALLDONE > /home/user/asyncfpga3/audit/r19/bisect.done
