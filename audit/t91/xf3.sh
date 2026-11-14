#!/usr/bin/env bash
# T100: pre-audit xf3 seed 1 (research db2a8157): xf2 + BDC_FORK_OUT_LINK=n11__0,n30__0, sizes fr2; own build at research HEAD worktree.
cd /home/user/asyncfpga3/audit/t91
git -C /root/wt-r91 fetch -q origin 2>/dev/null; git -C /root/wt-r91 checkout -q --detach origin/claude/research
SZ=../research/data/xorshift_sizes_T3s50_fr2_bench.vh R=/root/wt-r91 bash build_lev.sh xf3 1 > /root/t90/build_xf3_1.log 2>&1
cd ../t90; V=../t65/xorshift_17.hex; export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py MON_KERNEL=/root/t65/xf3_1/xorshift_kernel_bench.v
bash run_per.sh xorshift xf3_1 2>/dev/null &
for c in mon_fastmin:min mon_worst:band; do HWD=xf3_1 GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
  python3 ../t65/oracle_xorshift.py check $V /root/t65/xf3_1_${c%%:*}.log 2 > /root/t90/xf3_1_${c%%:*}_oracle.txt 2>&1; done; wait
echo DONE > /root/t100.done
