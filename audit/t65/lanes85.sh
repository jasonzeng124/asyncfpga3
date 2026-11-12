#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
(PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py HWD=l5_1 bash run2.sh xorshift mon_worst; HWD=l5_1 GLS_SDF_FIELD=max bash run2.sh xorshift slowmax) &
sleep 30; PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py HWD=l5_1 GLS_SDF_FIELD=min bash run2.sh xorshift mon_fastmin
wait; echo DONE > lanes85.done
