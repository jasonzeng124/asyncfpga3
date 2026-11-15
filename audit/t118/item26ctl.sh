#!/usr/bin/env bash
# T119 CONTROL (no slowed arc; every arc at 0.74 x FAST_MIN) for the replay formal C 490bb556's item 26 witness (kappa 0.26, corner 0 = fast): every arc at (1-k)*FAST_MIN, the
# ulink_n13 ctl -> pair[6] LUT5 A2 interconnect at (1+k)*FAST_MAX (1152 ps -> 1452) and that LUT's A2 arc at (1+k) x its
# fast max (approximated as FAST_MIN x 1152/993). Own route c64eq_25 (fasm aded8a8b = formal's). Vectors 27, 703, 77031.
# Own oracle + t104 monitors. Formal's run: want [111, 170, 350], got [175, 42, 158].
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/c64eqctl_25/collatz64_kernel_bench.v
V=/home/user/asyncfpga3/audit/t118/vec_c64_w.hex
VEC=$V HWD=c64eqctl_25 GLS_SDF_FIELD=min timeout 3600 bash ../t91/gate_vec.sh collatz64 w26
python3 ../t65/oracle_collatz64.py check $V /root/t65/c64eqctl_25_w26.log 2 > /root/t90/c64eqctl_25_w26_oracle.txt 2>&1
echo DONE > /root/t119c.done
