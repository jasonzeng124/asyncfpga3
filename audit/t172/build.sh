#!/usr/bin/env bash
# T172: research's trimmed lfsrfind s1 (FOR-FORMAL dbf7af1fa; exit1 task 8, flow v9, rule-clean before and after trim).
# Own rebuild at dbf7af1fa with the patched toolchain /root/audit-tc2, the != fixture, sizes_built.vh, seed 1 (expect sdf 129ff3ee).
set -u
A=/home/user/asyncfpga3/audit; W=/root/wt-t172; L=/root/t172.log; K=lfsrfind
echo "T172 build $(date -u)" > $L
git -C /home/user/asyncfpga3 worktree remove --force $W 2>/dev/null; git -C /home/user/asyncfpga3 worktree add -q --detach $W dbf7af1fa
mkdir -p $W/build; cp -r $W/cloud/fixtures/frontend $W/build/; cp $W/cloud/fixtures/frontend_exitcond/$K/comp/*.mlir $W/build/frontend/$K/comp/
source /root/audit-tc2/openxc7/export.sh >/dev/null 2>&1
( cd $W/cells && TC=/root/audit-tc2 BDC_AUTO=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$A/t172/sizes_built.vh NEXTPNR_SEED=1 PNR_TIMEOUT=3600 ./hw/build_bench.sh $K ) > /root/t172_build.log 2>&1
echo "build rc=$?" >> $L
D=$W/cells/build/hw/${K}_bench_gen
echo "sdf $(md5sum < $D/${K}_bench_gen.sdf | cut -c1-8) (research 129ff3ee); fasm $(md5sum < $D/${K}_bench_gen.fasm | cut -c1-8)" >> $L
echo DONE >> $L
