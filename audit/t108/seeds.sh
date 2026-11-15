#!/usr/bin/env bash
# T108b: speculative incrementer on the thin farm seeds (research 2d44e1f0: SELECT worst +150 seed 1, +159 seed 12; their
# rows cover nominal/worst only). Own build + own select-race monitor (t108/mon_spec.py) at FAST_MIN, worst, SLOW_MAX.
cd /home/user/asyncfpga3/audit/t91
git -C /root/wt-r91 fetch -q origin; git -C /root/wt-r91 checkout -q --detach origin/claude/research
for s in 1 12; do SZ=../research/data/xorshift_sizes_T3s50_fr3_bench.vh R=/root/wt-r91 bash build_lev.sh xs $s > /root/t90/build_xs_$s.log 2>&1; done
cd ../t90; export PS_MON_GEN=/home/user/asyncfpga3/audit/t108/mon_spec.py
for s in 1 12; do export MON_KERNEL=/root/t65/xs_$s/xorshift_kernel_bench.v
  for c in spec_fastmin:min spec_worst:band spec_slowmax:max; do
    ( HWD=xs_$s GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
      python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xs_${s}_${c%%:*}.log 2 > /root/t90/xs_${s}_${c%%:*}_oracle.txt 2>&1 ) & sleep 30
  done; wait; done
echo DONE > /root/t108c.done
