#!/usr/bin/env bash
# T117: BOARD-QUEUE item 28 (#29, research 606ca779): collatz pre_eq2 + nl6s3m (select links at 3, N10__4_UACK 0), seed 20,
# recipe sdf d86bdde5, 25.81 ns. Own build, FF scan, period; GLS 3 corners (own oracle + t104 monitors incl. mux / steer);
# select-arrival lateness monitor (t116/mon_sel.py) at FAST_MIN and worst; own static rule H; own rule E (t93 wrapper).
set -u
R=/root/wt-r91; F=$R/build/frontend/collatz/comp/handshake_transformed.mlir
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
cp $F /root/t117_frontend_orig.mlir
cd /home/user/asyncfpga3/audit/t90
cp $R/research/data/fifteen/collatz_preeq2.mlir $F
R=$R bash build.sh colsel3 20 > /root/t90/build_colsel3_20.log 2>&1
cp /root/t117_frontend_orig.mlir $F
echo "usinkeq2 $(grep -c usinkeq2 /root/t65/colsel3_20/collatz_kernel_bench.v)" > /root/t117.log
python3 ../t67/scan_ff_own.py /root/t65/colsel3_20/*.fasm > /root/t90/ff_colsel3_20.txt 2>&1
until [ -f /root/t116c.done ]; do sleep 30; done
bash run_per.sh collatz colsel3_20
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/colsel3_20/collatz_kernel_bench.v
for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
  HWD=colsel3_20 GLS_SDF_FIELD=${c##*:} bash gate.sh collatz ${c%%:*}
  python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/colsel3_20_${c%%:*}.log 2 > /root/t90/colsel3_20_${c%%:*}_oracle.txt 2>&1
done
RJ=/root/t65/colsel3_20/collatz_bench_gen_routed.json
for c in fastmin worst slowmax; do JSON=../t117/h_$c.json PATHS=0 python3 ../t109/rule_h.py /root/t65/work_colsel3_20_mon1_$c $RJ > ../t117/rule_h_$c.txt 2>&1; done
echo DONE > /root/t117.done
