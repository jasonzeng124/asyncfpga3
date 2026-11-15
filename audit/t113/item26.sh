#!/usr/bin/env bash
# T113: BOARD-QUEUE item 26 (#27, research d70797c4): collatz64 + pre_eq2 + h2 pads, board seed 25,
# recipe sdf 6982a9d5, 36.27 ns; paired baseline c64h (item 24 structure, h sizes, no rewrite) on seed 25.
set -u
R=/root/wt-r91; F=$R/build/frontend/collatz64/comp/handshake_transformed.mlir
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
cp $F /root/t113_frontend_orig.mlir
python3 $R/research/tools/fifteen/pre_eq2.py $F /root/t113_preeq2_own.mlir > /root/t113_preeq2.log 2>&1
md5sum $F /root/t113_preeq2_own.mlir $R/research/data/fifteen/collatz64_preeq2.mlir >> /root/t113_preeq2.log
cd /home/user/asyncfpga3/audit/t90
R=$R bash build.sh c64h 25 > /root/t90/build_c64h_25.log 2>&1
cp $R/research/data/fifteen/collatz64_preeq2.mlir $F
R=$R bash build.sh c64eq 25 > /root/t90/build_c64eq_25.log 2>&1
cp /root/t113_frontend_orig.mlir $F
echo "usinkeq2 $(grep -c usinkeq2 /root/t65/c64eq_25/collatz64_kernel_bench.v)" >> /root/t113_preeq2.log
for v in c64eq_25 c64h_25; do python3 ../t67/scan_ff_own.py /root/t65/$v/*.fasm > /root/t90/ff_$v.txt 2>&1; done
( bash run_per.sh collatz64 c64eq_25; bash run_per.sh collatz64 c64h_25 ) &
sleep 20
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/c64eq_25/collatz64_kernel_bench.v
for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
  ( HWD=c64eq_25 GLS_SDF_FIELD=${c##*:} bash gate.sh collatz64 ${c%%:*}
    python3 ../t65/oracle_collatz64.py check ../t65/collatz64_14.hex /root/t65/c64eq_25_${c%%:*}.log 2 > /root/t90/c64eq_25_${c%%:*}_oracle.txt 2>&1 ) & sleep 30
done
wait; echo DONE > /root/t113.done
