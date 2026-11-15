#!/usr/bin/env bash
# T108: xs_10 (research 16d4fb20 speculative incrementer): own mean-iteration latency (256 vs 2048 rounds) and GLS at
# 3 corners with own oracle + own speculative-select monitor (t108/mon_spec.py, chains t104 latch/steer/mux monitors).
cd /home/user/asyncfpga3/audit/t90
export PS_MON_GEN=/home/user/asyncfpga3/audit/t108/mon_spec.py MON_KERNEL=/root/t65/xs_10/xorshift_kernel_bench.v
bash ../t100/run_per_xs.sh xs_10 &
sleep 20
for c in spec_fastmin:min spec_worst:band spec_slowmax:max; do
  ( HWD=xs_10 GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
    python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xs_10_${c%%:*}.log 2 > /root/t90/xs_10_${c%%:*}_oracle.txt 2>&1 ) &
  sleep 30
done
wait; echo DONE > /root/t108.done
