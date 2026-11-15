#!/usr/bin/env bash
# T111: own negative control for research's proposed select-rule replacement (18137d36): the historical collatz64 T4cd seed 7
# FAST_MIN failure (research rebuild nc64_7, sdf 98809562, BDC_CONST_DATA=1, T4cd sizes; failing vector n=871).
# Do own rule H (static, OR-join) and own dynamic rule H monitor flag it?
set -u
cd /home/user/asyncfpga3/audit/t90
R=/root/wt-r91 bash build.sh nc64 7 > /root/t90/build_nc64_7.log 2>&1
V=/home/user/asyncfpga3/audit/t111/vec_c64_871.hex
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/nc64_7/collatz64_kernel_bench.v
for c in mon1_fastmin:min mon1_worst:band; do
  ( VEC=$V HWD=nc64_7 GLS_SDF_FIELD=${c##*:} bash ../t91/gate_vec.sh collatz64 ${c%%:*}
    python3 ../t65/oracle_collatz64.py check $V /root/t65/nc64_7_${c%%:*}.log 2 > /root/t90/nc64_7_${c%%:*}_oracle.txt 2>&1 ) & sleep 30
done; wait
RJ=/root/t65/nc64_7/collatz64_bench_gen_routed.json
for c in fastmin worst; do JSON=../t111/h_nc64_7_$c.json PATHS=0 python3 ../t109/rule_h.py /root/t65/work_nc64_7_mon1_$c $RJ > ../t111/rule_h_nc64_7_$c.txt 2>&1; done
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_JSON=/home/user/asyncfpga3/audit/t111/h_nc64_7_fastmin.json H_THRESH=500
VEC=$V HWD=nc64_7 GLS_SDF_FIELD=min bash ../t91/gate_vec.sh collatz64 h_fastmin
python3 ../t65/oracle_collatz64.py check $V /root/t65/nc64_7_h_fastmin.log 2 > /root/t90/nc64_7_h_fastmin_oracle.txt 2>&1
echo DONE > /root/t111.done
