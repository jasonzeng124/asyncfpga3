#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py
HWD=pmf_1 bash run2.sh xorshift mon_worst &
sleep 30; HWD=pmf_1 GLS_SDF_FIELD=min bash run2.sh xorshift mon_fastmin &
wait; echo DONE > lanes83.done
