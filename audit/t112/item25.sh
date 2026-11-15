#!/usr/bin/env bash
# T112: BOARD-QUEUE item 25 (#26, research 89290bc7): collatz + pre_eq2 (exit test n == 2) + nl4 pads, board seed 24,
# recipe sdf e001dc27, 35.92 ns; paired baseline col4 (item 22 structure, nl4 sizes, no rewrite) on seed 24.
set -u
R=/root/wt-r91; F=$R/build/frontend/collatz/comp/handshake_transformed.mlir
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
cp $F /root/t112_frontend_orig.mlir
python3 $R/research/tools/fifteen/pre_eq2.py $F /root/t112_preeq2_own.mlir > /root/t112_preeq2.log 2>&1
md5sum $F /root/t112_preeq2_own.mlir $R/research/data/fifteen/collatz_preeq2.mlir >> /root/t112_preeq2.log
cd /home/user/asyncfpga3/audit/t90
R=$R bash build.sh col4 24 > /root/t90/build_col4_24.log 2>&1
cp $R/research/data/fifteen/collatz_preeq2.mlir $F
R=$R bash build.sh coleq 24 > /root/t90/build_coleq_24.log 2>&1
cp /root/t112_frontend_orig.mlir $F
echo "usinkeq2 $(grep -c usinkeq2 /root/t65/coleq_24/collatz_kernel_bench.v)" >> /root/t112_preeq2.log
for v in coleq_24 col4_24; do python3 ../t67/scan_ff_own.py /root/t65/$v/*.fasm > /root/t90/ff_$v.txt 2>&1; done
( bash run_per.sh collatz coleq_24; bash run_per.sh collatz col4_24 ) &
sleep 20
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/coleq_24/collatz_kernel_bench.v
for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
  ( HWD=coleq_24 GLS_SDF_FIELD=${c##*:} bash gate.sh collatz ${c%%:*}
    python3 ../t65/oracle_collatz.py check ../t65/collatz_13.hex /root/t65/coleq_24_${c%%:*}.log 2 > /root/t90/coleq_24_${c%%:*}_oracle.txt 2>&1 ) & sleep 30
done
wait; echo DONE > /root/t112.done
