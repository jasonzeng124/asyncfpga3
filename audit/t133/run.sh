#!/usr/bin/env bash
# T133: own replay of research d284c335a / e795556b2 (rule E's steer control): item 28's route (own colsel3_20, sdf d86bdde5),
# +8000 ps on the two INTERCONNECT arcs ucmpi2.uz_n36/O6 -> ucond_br7.u$LUT5/A3, $LUT6/A3 (the loop steer's condition),
# own copy /root/t65/c28steer_20 (t125/inject.py). FAST_MIN gate WITHOUT META_INIT (own harness has none), with t131/mon_x.py
# on the steer's join output (ucond_br7_req n3443), its false output (n_falseResult_9_u_req n3441) and the condition net
# (ucmpi2 cmp output n3501): does it stall, and is there X? Self-stop at 80 us (clean: all 13 batches by ~60 us).
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t131/mon_x.py MON_X_NETS=n3443,n3441,n3501 MON_X_N=40 MON_X_STOP=80000000
HWD=c28steer_20 GLS_SDF_FIELD=min timeout 2400 bash gate.sh collatz steer_fastmin
python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/c28steer_20_steer_fastmin.log 2 > /root/t90/c28steer_20_oracle.txt 2>&1
echo DONE > /root/t133.done
