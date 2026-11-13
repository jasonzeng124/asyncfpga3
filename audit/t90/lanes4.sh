#!/usr/bin/env bash
# T90b: collatz64 lever 5 vs base on seeds 2, 4-8 (own paired 8-route comparison). Builds in wt-r90b, periods after lanes3.
cd /home/user/asyncfpga3/audit/t90
for s in 2 4 5 6 7 8; do for v in c64nl c64r; do R=/root/wt-r90b bash build.sh $v $s > /root/t90/build_${v}_$s.log 2>&1; done; done
while [ ! -f /root/t90/lanes3.done ]; do sleep 30; done
run() { for s in "$@"; do for v in c64nl c64r; do bash run_per.sh collatz64 ${v}_$s; done; done; }
run 2 5 8 & sleep 20; run 4 6 & sleep 20; run 7 & wait
echo DONE > /root/t90/lanes4.done
