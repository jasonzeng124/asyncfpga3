#!/usr/bin/env bash
# T90 lanes: builds (two worktrees, sequential within each) then period runs.
cd /home/user/asyncfpga3/audit/t90; mkdir -p /root/t90
( for b in "c64nl 1" "c64r 1" "c64nl 3" "c64r 3"; do set -- $b; bash build.sh $1 $2 > /root/t90/build_$1_$2.log 2>&1; bash run_per.sh collatz64 $1_$2 & done; wait ) &
( for b in "colnl 3" "colr 3" "colnl 1" "colr 1"; do set -- $b; R=/root/wt-r90b bash build.sh $1 $2 > /root/t90/build_$1_$2.log 2>&1; bash run_per.sh collatz $1_$2 & done; wait ) &
wait; echo DONE > /root/t90/lanes1.done
