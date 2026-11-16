#!/usr/bin/env bash
# T126b: dynamic rule H (t109/mon_h.py) on item 31 (colsel3a_20) at FAST_MIN: is the static -31 ps row at
# ulink_n_falseResult_9 stage[1] (OR-join) live? (Item 19's same row was an OR-join artefact, T109.)
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_THRESH=500 H_JSON=/home/user/asyncfpga3/audit/t126/h_colsel3a_20_fastmin.json
HWD=colsel3a_20 GLS_SDF_FIELD=min timeout 5400 bash gate.sh collatz h_fastmin
python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/colsel3a_20_h_fastmin.log 2 > /root/t90/colsel3a_20_h_fastmin_oracle.txt 2>&1
echo DONE > /root/t126h.done
