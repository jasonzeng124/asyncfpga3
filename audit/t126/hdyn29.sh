#!/usr/bin/env bash
# T126b: dynamic rule H (t109/mon_h.py) on item 29 (ipsel3_19) at FAST_MIN: is the static -215 ps row at
# ulink_n_trueResult_10 stage[1] (OR-join) live? (Item 19's same row was an OR-join artefact, T109.)
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_THRESH=500 H_JSON=/home/user/asyncfpga3/audit/t126/h_ipsel3_19_fastmin.json
HWD=ipsel3_19 GLS_SDF_FIELD=min timeout 5400 bash gate.sh ipow h_fastmin
python3 ../t65/oracle_ipow.py check ../t65/ipow_17.hex /root/t65/ipsel3_19_h_fastmin.log 2 > /root/t90/ipsel3_19_h_fastmin_oracle.txt 2>&1
echo DONE > /root/t126b.done
