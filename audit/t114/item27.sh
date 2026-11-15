#!/usr/bin/env bash
# T114: BOARD-QUEUE item 27 (#28, research 3fed89de): xorshift lever 8 (pre_dec) + fr4 sizes, board seed 2, recipe sdf
# a9bdac53, latency 417. Paired baseline xf5_2 (item 23 knobs, fr4 sizes, no rewrite). Own latency (256 vs 2048 rounds),
# 3-corner GLS with own oracle + t104 monitors (after T113b's GLS has finished, for memory).
set -u
R=/root/wt-r91; F=$R/build/frontend/xorshift/comp/handshake_transformed.mlir
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
cp $F /root/t114_frontend_orig.mlir; md5sum $F > /root/t114.log
cd /home/user/asyncfpga3/audit/t91
SZ=../research/data/xorshift_sizes_T3s50_fr4_bench.vh R=$R bash build_lev.sh xf5 2 > /root/t90/build_xf5_2.log 2>&1
cp $R/research/data/fifteen/xorshift_predec.mlir $F
SZ=../research/data/xorshift_sizes_T3s50_fr4_bench.vh R=$R bash build_lev.sh xd 2 > /root/t90/build_xd_2.log 2>&1
cp /root/t114_frontend_orig.mlir $F; md5sum $F >> /root/t114.log
echo "uforkdec0 $(grep -c 'uforkdec0 (' /root/t65/xd_2/xorshift_kernel_bench.v)" >> /root/t114.log
for v in xf5_2 xd_2; do python3 ../t67/scan_ff_own.py /root/t65/$v/*.fasm > /root/t90/ff_$v.txt 2>&1; done
cd ../t90
until [ -f /root/t113b.done ]; do sleep 30; done
bash ../t100/run_per_xs.sh xf5_2 & sleep 20
bash ../t100/run_per_xs.sh xd_2 & sleep 20
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/xd_2/xorshift_kernel_bench.v
for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
  ( HWD=xd_2 GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
    python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xd_2_${c%%:*}.log 2 > /root/t90/xd_2_${c%%:*}_oracle.txt 2>&1 ) & sleep 30
done
wait; echo DONE > /root/t114.done
