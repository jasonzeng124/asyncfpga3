#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/r23
until grep -q "^EXIT" /root/formal_build_f40e003a.log 2>/dev/null; do sleep 60; done
FIELD=min ./run_point2.sh bq1_d_min 0 0 all
