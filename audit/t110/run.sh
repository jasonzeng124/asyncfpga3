#!/usr/bin/env bash
# T110: research lever 8 (5321c5a0 pre_dec MLIR; 32dec7eb "xd_10 ... latency 414 vs xf5_10 499, -3.98 ns/iter", route 5e759620).
# Own: (1) pre_dec.py re-applied to the worktree's frontend MLIR must equal the committed file (md5); (2) own builds
# xf5_10 (baseline: item 23 knobs, fr4 sizes) and xd_10 (committed pre_dec MLIR swapped into the worktree's frontend output,
# original restored after); (3) FF scans; (4) own mean-iteration latency 256 vs 2048 rounds; (5) GLS xd_10 at 3 corners,
# own oracle + t104 monitors.
set -u
R=/root/wt-r91; F=$R/build/frontend/xorshift/comp/handshake_transformed.mlir
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
cp $F /root/t110_frontend_orig.mlir
python3 $R/research/tools/fifteen/pre_dec.py $F /root/t110_predec_own.mlir > /root/t110_predec.log 2>&1
md5sum $F /root/t110_predec_own.mlir $R/research/data/fifteen/xorshift_predec.mlir >> /root/t110_predec.log
cd /home/user/asyncfpga3/audit/t91
SZ=../research/data/xorshift_sizes_T3s50_fr4_bench.vh R=$R bash build_lev.sh xf5 10 > /root/t90/build_xf5_10.log 2>&1
cp $R/research/data/fifteen/xorshift_predec.mlir $F
SZ=../research/data/xorshift_sizes_T3s50_fr4_bench.vh R=$R bash build_lev.sh xd 10 > /root/t90/build_xd_10.log 2>&1
cp /root/t110_frontend_orig.mlir $F
for v in xf5_10 xd_10; do python3 ../t67/scan_ff_own.py /root/t65/$v/*.fasm > /root/t90/ff_$v.txt 2>&1; done
cd ../t90
bash ../t100/run_per_xs.sh xf5_10 & sleep 20
bash ../t100/run_per_xs.sh xd_10 & sleep 20
wait
export PS_MON_GEN=/home/user/asyncfpga3/audit/t104/mon_both1.py MON_KERNEL=/root/t65/xd_10/xorshift_kernel_bench.v
for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
  ( HWD=xd_10 GLS_SDF_FIELD=${c##*:} bash gate.sh xorshift ${c%%:*}
    python3 ../t65/oracle_xorshift.py check ../t65/xorshift_17.hex /root/t65/xd_10_${c%%:*}.log 2 > /root/t90/xd_10_${c%%:*}_oracle.txt 2>&1 ) & sleep 30
done
wait; echo DONE > /root/t110.done
