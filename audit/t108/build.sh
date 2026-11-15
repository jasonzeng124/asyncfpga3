#!/usr/bin/env bash
# T108: research 16d4fb20 speculative incrementer xs_10 (= item 23 xf4_10 + BDC_SPEC_INC=uaddi0:4:6); recipe sdf 41a915c2.
cd /home/user/asyncfpga3/audit/t91
git -C /root/wt-r91 fetch -q origin; git -C /root/wt-r91 checkout -q --detach origin/claude/research
SZ=../research/data/xorshift_sizes_T3s50_fr3_bench.vh R=/root/wt-r91 bash build_lev.sh xs 10 > /root/t90/build_xs_10.log 2>&1
python3 ../t67/scan_ff_own.py /root/t65/xs_10/*.fasm > /root/t90/ff_xs_10.txt 2>&1
echo DONE > /root/t108b.done
