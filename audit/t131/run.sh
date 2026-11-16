#!/usr/bin/env bash
# T131: own check of research bd57aa13b's correction on the audit's T118 replay (colsel0inj_24 = fcsel0 s24 with +3000 ps
# select -> umux1.uj0/uj1 A5): log the first changes (incl. X) of umux1's join select pins (w15020 / w15026), umux1.either
# (n3696), its z_req (n4580) at FAST_MIN; the run stalls (T118), so a 15 min limit.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t131/mon_x.py MON_X_NETS=w15020,w15026,n3696,n4580 MON_X_N=10
HWD=colsel0inj_24 GLS_SDF_FIELD=min timeout 900 bash gate.sh collatz xtr_fastmin
echo DONE > /root/t131.done
