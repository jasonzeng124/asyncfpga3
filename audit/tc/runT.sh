#!/bin/bash
# corner SDFs (scratchpad, not the repo) + tighten.py (rules A, F, H, I) on each
# tighten.py is a scratch copy of 19a93c1 verify/ whose only change lists every passing rule F line ([:3] -> [:999] at line 2017)
source ~/auditlogs/export_dev2.sh
cd /home/user/asyncfpga3/audit/tc
declare -A R=([d]=/home/user/wt-rb1/cells/build/hw/gcd_hw [bq2]=/home/user/wt-bq23/cells/build/hw/gcd_hw [bq3]=/home/user/wt-bq23b/cells/build/hw/gcd_hw [4]=/tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/rt/t4/cells/build/hw/gcd_hw)
for s in d bq2 bq3 4; do python3 -I corner_sdf.py ${R[$s]} /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/csdf2/$s > /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/csdf2/$s.log 2>&1; done
tl() { (cd /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/cellsF && python3 verify/tighten.py $2 --osc dhk --osc invhk > /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/tl2/$1.log 2>&1); }
job() { s=$1; mkdir -p /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/tl2; cp /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/tl/${s}_sdf.log /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/tl2/ 2>/dev/null; [ -s /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/tl2/${s}_sdf.log ] || tl ${s}_sdf ${R[$s]}/gcd_hw.sdf; for c in fmin fmax smin smax; do tl ${s}_$c /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/csdf2/$s/$c/gcd_hw.sdf; done; }
(job d; job bq2) &
(job bq3; job 4) &
wait
for s in d bq2 bq3 4; do python3 -I tparse.py $s /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/tl2/${s}_sdf.log /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/tl2/${s}_fmin.log /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/tl2/${s}_fmax.log /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/tl2/${s}_smin.log /tmp/claude-0/-home-user-asyncfpga3/51f58590-4ae3-5ee9-a557-58439d00deba/scratchpad/tl2/${s}_smax.log > tighten_corners2_$s.tsv; done
echo done
