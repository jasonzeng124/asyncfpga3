#!/usr/bin/env bash
# T138 resume after a container restart: SLOW_MAX run and the fit (FAST_MIN done before the restart).
set -u
A=/home/user/asyncfpga3/audit; L=/root/t138.log; K=collatz; H=aug_collatz
cd $A/t90
HWD=$H GLS_SDF_FIELD=max FCLK=10000 TBATCH=3000000 timeout 7200 bash ../t138/gate_clk.sh $K slowmax
python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/${H}_slowmax.log 2 > /root/t90/${H}_slowmax_oracle.txt 2>&1
echo "slowmax: $(grep agreement /root/t90/${H}_slowmax_oracle.txt)" >> $L
python3 $A/t138/fit.py /root/t90/${H}_fastmin_oracle.txt /root/t90/${H}_slowmax_oracle.txt >> $L 2>&1
echo DONE >> $L; echo DONE > /root/t138.done
