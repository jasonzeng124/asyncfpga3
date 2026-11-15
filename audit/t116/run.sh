#!/usr/bin/env bash
# T116 (pre-audit): research's select-links-at-0 collatz (fcsel0 recipe: item 25 structure, pre_eq2, nl6s0 sizes) on seed 24,
# paired with coleq6_24 (same, nl6 sizes = fceq2). Own period; GLS 3 corners with own oracle + t104 monitors (incl. mux
# select monitor); FAST_MIN with research's select-flipping hold vector; own static rule H; own dynamic rule H at FAST_MIN.
set -u
R=/root/wt-r91; F=$R/build/frontend/collatz/comp/handshake_transformed.mlir
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
cp $F /root/t116_frontend_orig.mlir
cd /home/user/asyncfpga3/audit/t90
cp $R/research/data/fifteen/collatz_preeq2.mlir $F
R=$R bash build.sh colsel0 24 > /root/t90/build_colsel0_24.log 2>&1
R=$R bash build.sh coleq6 24 > /root/t90/build_coleq6_24.log 2>&1
cp /root/t116_frontend_orig.mlir $F; md5sum $F > /root/t116_mlir.log
for v in colsel0_24 coleq6_24; do python3 ../t67/scan_ff_own.py /root/t65/$v/*.fasm > /root/t90/ff_$v.txt 2>&1; done
bash run_per.sh collatz colsel0_24; bash run_per.sh collatz coleq6_24
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/colsel0_24/collatz_kernel_bench.v
for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
  HWD=colsel0_24 GLS_SDF_FIELD=${c##*:} bash gate.sh collatz ${c%%:*}
  python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/colsel0_24_${c%%:*}.log 2 > /root/t90/colsel0_24_${c%%:*}_oracle.txt 2>&1
done
V=/home/user/asyncfpga3/audit/t116/vec_collatz_hold.hex
VEC=$V HWD=colsel0_24 GLS_SDF_FIELD=min bash ../t91/gate_vec.sh collatz hv_fastmin
python3 ../t65/oracle_collatz.py check $V /root/t65/colsel0_24_hv_fastmin.log 2 > /root/t90/colsel0_24_hv_fastmin_oracle.txt 2>&1
RJ=/root/t65/colsel0_24/collatz_bench_gen_routed.json
for c in fastmin worst slowmax; do JSON=../t116/h_$c.json PATHS=0 python3 ../t109/rule_h.py /root/t65/work_colsel0_24_mon1_$c $RJ > ../t116/rule_h_$c.txt 2>&1; done
export PS_MON_GEN=/home/user/asyncfpga3/audit/t109/mon_h.py H_JSON=/home/user/asyncfpga3/audit/t116/h_fastmin.json H_THRESH=500
VEC=$V HWD=colsel0_24 GLS_SDF_FIELD=min bash ../t91/gate_vec.sh collatz h_fastmin
python3 ../t65/oracle_collatz.py check $V /root/t65/colsel0_24_h_fastmin.log 2 > /root/t90/colsel0_24_h_fastmin_oracle.txt 2>&1
echo DONE > /root/t116.done
