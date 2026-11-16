#!/usr/bin/env bash
# T133b: the T133 steer injection with a defined start-up emulated at the injected pins (ucond_br7.u LUT5/LUT6 A3 = w17106 /
# w17112) forced to 0, then to 1, until 10 us (the real condition, X until 1.652 us at its driver, reaches the pin ~9.65 us).
cd /home/user/asyncfpga3/audit/t90
for v in 0 1; do
  export PS_MON_GEN=/home/user/asyncfpga3/audit/t133/mon_force.py MON_X_NETS=n3443,n3441,n3501 MON_X_N=40 MON_X_STOP=80000000 FORCE_NETS=w17106,w17112 FORCE_VAL=$v FORCE_UNTIL=10000000
  HWD=c28steer_20 GLS_SDF_FIELD=min timeout 2400 bash gate.sh collatz steerf${v}_fastmin
  python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/c28steer_20_steerf${v}_fastmin.log 2 > /root/t90/c28steer_20_f${v}_oracle.txt 2>&1
done
echo DONE > /root/t133b.done
