#!/usr/bin/env bash
# T124c: dynamic check of the item 26 (c64eq_25) input-boundary race (own static -313 ps at FAST_MIN, bit pair[40]):
# GLS FAST_MIN with t124/mon_inhold.py (8 tightest bits) + own oracle.
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t124/mon_inhold.py IH_JSON=/home/user/asyncfpga3/audit/t124/ih_c64eq_25_fastmin.json IH_BITS=8
HWD=c64eq_25 GLS_SDF_FIELD=min timeout 5400 bash gate.sh collatz64 ih_fastmin
python3 ../t65/oracle_collatz64.py check ../t65/collatz64_14.hex /root/t65/c64eq_25_ih_fastmin.log 2 > /root/t90/c64eq_25_ih_fastmin_oracle.txt 2>&1
echo DONE > /root/t124c.done
