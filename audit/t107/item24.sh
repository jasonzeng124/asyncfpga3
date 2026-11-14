#!/usr/bin/env bash
# T107: BOARD-QUEUE item 24 (#25, research 0b983ea2): c64nl seed 17 (recipe sdf 3a370768) + item 21 recipe (c64r) on seed 17.
cd /home/user/asyncfpga3/audit/t90
git -C /root/wt-r91 fetch -q origin; git -C /root/wt-r91 checkout -q --detach origin/claude/research
R=/root/wt-r91 bash build.sh c64nl 17 > /root/t90/build_c64nl_17.log 2>&1
R=/root/wt-r90b bash build.sh c64r 17 > /root/t90/build_c64r_17.log 2>&1
python3 ../t67/scan_ff_own.py /root/t65/c64nl_17/*.fasm > /root/t90/ff_c64nl_17.txt 2>&1
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/c64nl_17/collatz64_kernel_bench.v
( bash run_per.sh collatz64 c64nl_17; bash run_per.sh collatz64 c64r_17 ) &
sleep 20; ( for c in mon1_fastmin:min mon1_slowmax:max; do HWD=c64nl_17 GLS_SDF_FIELD=${c##*:} bash gate.sh collatz64 ${c%%:*}
  python3 ../t65/oracle_collatz64.py check ../t65/collatz64_14.hex /root/t65/c64nl_17_${c%%:*}.log 2 > /root/t90/c64nl_17_${c%%:*}_oracle.txt 2>&1; done ) &
sleep 20; HWD=c64nl_17 GLS_SDF_FIELD=band bash gate.sh collatz64 mon1_worst
python3 ../t65/oracle_collatz64.py check ../t65/collatz64_14.hex /root/t65/c64nl_17_mon1_worst.log 2 > /root/t90/c64nl_17_mon1_worst_oracle.txt 2>&1
wait; echo DONE > /root/t107.done
