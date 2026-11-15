#!/usr/bin/env bash
# T120: replay of formal C10's fcsel0 seed 24 witness (kappa 0.22; falseResult_3 stage[0] ctl -> lat.pair[16] LUT5 A4 slow
# at (1+k) x FAST_MAX 1109 ps, its LUT arc likewise; kernel arcs at (1-k) x FAST_MIN; harness at FAST_MIN). Own route
# colsel0_24 (sdf bb5fbbdb = formal's). Vectors 27 / 703 / 77031; formal: want 111 / 170 / 350, got 111 / 99 / 350.
# Then the control (same scaling, no slowed arc).
cd /home/user/asyncfpga3/audit/t90
V=/home/user/asyncfpga3/audit/t118/vec_c64_w.hex
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py
for h in cs0rep_24 cs0ctl_24; do export MON_KERNEL=/root/t65/$h/collatz_kernel_bench.v
  VEC=$V HWD=$h GLS_SDF_FIELD=min timeout 3600 bash ../t91/gate_vec.sh collatz w22
  python3 ../t65/oracle_collatz.py check $V /root/t65/${h}_w22.log 2 > /root/t90/${h}_w22_oracle.txt 2>&1; done
echo DONE > /root/t120.done
