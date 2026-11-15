#!/usr/bin/env bash
# T111b: own positive control: pc64_7 (nc64_7 with ulink_n14__1 / SDELAY back at 19 / 2; research sdf acc06847). Own oracle
# with the failing vector n=871 at FAST_MIN + own dynamic rule H monitor (rows < 500 ps static, from the fastmin work dir).
set -u
cd /home/user/asyncfpga3/audit/t90
R=/root/wt-r91 bash build.sh pc64 7 > /root/t90/build_pc64_7.log 2>&1
V=/home/user/asyncfpga3/audit/t111/vec_c64_871.hex
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/pc64_7/collatz64_kernel_bench.v
VEC=$V HWD=pc64_7 GLS_SDF_FIELD=min bash ../t91/gate_vec.sh collatz64 mon1_fastmin
python3 ../t65/oracle_collatz64.py check $V /root/t65/pc64_7_mon1_fastmin.log 2 > /root/t90/pc64_7_mon1_fastmin_oracle.txt 2>&1
JSON=../t111/h_pc64_7_fastmin.json PATHS=0 python3 ../t109/rule_h.py /root/t65/work_pc64_7_mon1_fastmin /root/t65/pc64_7/collatz64_bench_gen_routed.json > ../t111/rule_h_pc64_7_fastmin.txt 2>&1
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_JSON=/home/user/asyncfpga3/audit/t111/h_pc64_7_fastmin.json H_THRESH=500
VEC=$V HWD=pc64_7 GLS_SDF_FIELD=min bash ../t91/gate_vec.sh collatz64 h_fastmin
python3 ../t65/oracle_collatz64.py check $V /root/t65/pc64_7_h_fastmin.log 2 > /root/t90/pc64_7_h_fastmin_oracle.txt 2>&1
echo DONE > /root/t111b.done
