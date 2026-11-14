#!/usr/bin/env bash
# T92: pre-audit "colsz" = collatz lever 5 + research/data/collatz_sizes_T3cdb_nl_bench.vh (research 5e1738a1), own builds at
# wt-r91 (research 9cff46ca). Control: colnl_1 rebuilt there must give sdf 9063dc11 (default flow unchanged).
cd /home/user/asyncfpga3/audit/t90
R=/root/wt-r91 bash build.sh colnl 1 > /root/t90/build_colnl_1_r91.log 2>&1
for s in 1 2 3 4 5 6 7 8; do SZ=../research/data/collatz_sizes_T3cdb_nl_bench.vh R=/root/wt-r91 bash build.sh colsz $s > /root/t90/build_colsz_$s.log 2>&1; done
echo DONE > /root/t92build.done
