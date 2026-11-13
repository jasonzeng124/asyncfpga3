#!/usr/bin/env bash
# T90c: collatz lever 5 (colnl) vs colr on seeds 2, 4-8 (own paired 8-route comparison). Builds alternate worktrees; periods 3 lanes.
cd /home/user/asyncfpga3/audit/t90
( for s in 2 5 7; do for v in colnl colr; do R=/root/wt-r90 bash build.sh $v $s > /root/t90/build_${v}_$s.log 2>&1; done; done ) &
( for s in 4 6 8; do for v in colnl colr; do R=/root/wt-r90b bash build.sh $v $s > /root/t90/build_${v}_$s.log 2>&1; done; done ) &
wait
run() { for s in "$@"; do for v in colnl colr; do bash run_per.sh collatz ${v}_$s; done; done; }
run 2 5 & sleep 20; run 4 6 & sleep 20; run 7 8 & wait
echo DONE > /root/t90/lanes5.done
