#!/usr/bin/env bash
# T128 negative control 2: item 31 route with +10000 ps on ulink_n11's latch output arcs into uselect0 (4 arcs), GLS
# FAST_MIN with own oracle; then own bundle.py on its bake. (+3000: static -1441, gate PASS 13/13.)
cd /home/user/asyncfpga3/audit/t90
HWD=cs3aneg2_20 GLS_SDF_FIELD=min timeout 4000 bash gate.sh collatz neg_fastmin
python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/cs3aneg2_20_neg_fastmin.log 2 > /root/t90/cs3aneg2_20_oracle.txt 2>&1
cd .. && python3 t128/bundle.py /root/t65/work_cs3aneg2_20_neg_fastmin /root/t65/cs3aneg2_20/collatz_bench_gen_routed.json 'ulink_n_falseResult_9\.many\.stage\[0\]' 'udut\.ulink_n(11|10__3|19__4|26)(\.many\.stage\[1\]\.u)?$' > /root/t90/cs3aneg2_20_bundle.txt 2>&1
echo DONE > /root/t128n.done
