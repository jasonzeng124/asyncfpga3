#!/usr/bin/env bash
# T95: own check of research 40e531f7 (ipow item 19 umux3 rule-A miss is a false path): rebuild ipowr_1 (expect sdf a6a2951b),
# then FAST_MIN and worst+scatter with the t83 monitors (mux select -> z_req margin at umux3), own 17 vectors and oracle.
cd /home/user/asyncfpga3/audit/t94
EXTRA=BDC_MERGE_RES_LINK=ucontrol_merge0 TAGO=ipowr bash build_ipowx.sh 1 > /root/t90/build_ipowr_1.log 2>&1
cd ../t90; export PS_MON_GEN=/home/user/asyncfpga3/audit/t83/mon_both.py MON_KERNEL=/root/t65/ipowr_1/ipow_kernel_bench.v
for c in mon_fastmin:min mon_worst:band; do HWD=ipowr_1 GLS_SDF_FIELD=${c##*:} bash gate.sh ipow ${c%%:*}; done
echo DONE > /root/t95.done
