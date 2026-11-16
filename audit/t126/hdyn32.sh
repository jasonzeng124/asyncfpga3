#!/usr/bin/env bash
# T126b: dynamic rule H (t109/mon_h.py) on item 32 (c64sel3p_22) at FAST_MIN: is the static -573 ps row at
# ulink_n_falseResult_9 stage[1] (OR-join) live? (Item 26 same row was an OR-join artefact, T109.)
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_THRESH=500 H_JSON=/home/user/asyncfpga3/audit/t126/h_c64sel3p_22_fastmin.json
HWD=c64sel3p_22 GLS_SDF_FIELD=min timeout 5400 bash gate.sh collatz64 h_fastmin
python3 ../t65/oracle_collatz64.py check ../t65/collatz64_14.hex /root/t65/c64sel3p_22_h_fastmin.log 2 > /root/t90/c64sel3p_22_h_fastmin_oracle.txt 2>&1
echo DONE > /root/t126i.done
