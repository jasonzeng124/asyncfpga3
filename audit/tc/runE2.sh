#!/bin/bash
source ~/auditlogs/export_dev2.sh
cd /home/user/asyncfpga3/audit/tc
export XRC_FBSCALE=1
run() { python3 -I rulee_x.py /home/user/wt-rb1/cells $2 $1 > rulee_fbs_$1.tsv 2> rulee_fbs_$1.err; }
(run d /home/user/wt-rb1/cells/build/hw/gcd_hw; run 4 /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/rt/t4/cells/build/hw/gcd_hw) &
(run bq2 /home/user/wt-bq23/cells/build/hw/gcd_hw; run bq3 /home/user/wt-bq23b/cells/build/hw/gcd_hw) &
wait
