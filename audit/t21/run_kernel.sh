#!/usr/bin/env bash
# T21: an August bench build (owner's files) on the full stack with my own xray SDF, research's ps7_bench host
# (/root/wt-r14 at the research head of the day), the board's FIXED vectors.  usage: run_kernel.sh DESIGN FIELD VECHEX
set -u
D=$1; FIELD=$2; VEC=$3; TAG=${D}_$FIELD
source /root/audit-tc/openxc7/export.sh
export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray:${PYTHONPATH:-} XRAY_DB=/root/dev2/lib/xray/prjxray-db/zynq7
HW=/root/t21/hw/$D; W=/root/t21/$TAG; L=/root/t21/$TAG.log
if [ ! -s $HW/${D}_xray.sdf ]; then
  (cd /root/wt-r14/cells && python3 gls/fid/xray_delay.py --routed $HW/${D}_routed.json --sdf $HW/$D.sdf --out $HW/${D}_xray.sdf > $HW/xray.log 2>&1)
fi
export GLS_SDF=$HW/${D}_xray.sdf GLS_SDF_FIELD=$FIELD GLS_MODEL=fid PS_DESIGN=$D PS_HOST=ps7_bench.v
{ echo "research $(cd /root/wt-r14 && git rev-parse HEAD) field $FIELD"; md5sum $HW/$D.bit $GLS_SDF $VEC
  /root/wt-r14/cells/gls/ps/build_ps.sh $HW $W "" bit || { echo BUILD_FAIL; exit 1; }
  cd $W && vvp gate.vvp | grep -E "ANNOTATE_DONE|WARNING|ERROR" | head -5
  vvp run_baked.vvp +VECFILE=$VEC +NRUNS=2 | grep -E "^BENCH" | head -60
} > $L 2>&1
rm -rf $W; echo DONE >> $L; cp $L /home/user/asyncfpga3/audit/t21/$TAG.log
