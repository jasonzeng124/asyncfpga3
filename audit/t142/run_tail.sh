#!/usr/bin/env bash
# T142b: item 35 SLOW_MAX on the two long-rounds vectors the first run never reached (harness time limit at 705 us).
set -u
A=/home/user/asyncfpga3/audit; L=/root/t142.log; K=xorshift; H=xdx55a_21; V=$A/t142/xorshift_long_tail.hex
cd $A/t90; export PS_MON_GEN=$A/t104/mon_both1.py
HWD=$H GLS_SDF_FIELD=max VECF=$V timeout 7200 bash ../t142/gate.sh $K lrt_slowmax
python3 ../t65/oracle_xorshift.py check $V /root/t65/${H}_lrt_slowmax.log 2 > /root/t90/${H}_lrt_slowmax_oracle.txt 2>&1
echo "T142b $H lrt_slowmax (vectors 6-7): $(grep agreement /root/t90/${H}_lrt_slowmax_oracle.txt); steer viol $(grep -c 'STEERMON VIOLATION' /root/t65/${H}_lrt_slowmax.log)" >> $L
echo DONE > /root/t142b.done
