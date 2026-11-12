#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
for h in l5_1 pmf_1; do HWD=$h bash run2.sh xorshift mon5_worst & sleep 30; HWD=$h GLS_SDF_FIELD=min bash run2.sh xorshift mon5_fastmin; wait; done
echo DONE > lanes86.done
