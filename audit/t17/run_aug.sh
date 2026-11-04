#!/usr/bin/env bash
# T17: the August gcd_bench_gen (owner's build, research/board/aug) on the full stack, research's bench host
# (research 22fe1811+ in /root/wt-r14), the board's 24 gcd_cost vectors.  usage: run_aug.sh TAG FIELD
set -u
TAG=$1; FIELD=$2
source /root/audit-tc/openxc7/export.sh
export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray:${PYTHONPATH:-} XRAY_DB=/root/dev2/lib/xray/prjxray-db/zynq7
HW=/root/t17/hw/gcd_bench_gen; W=/root/t17/$TAG; L=/root/t17/$TAG.log
export GLS_SDF=$HW/gcd_bench_gen_xray.sdf GLS_SDF_FIELD=$FIELD GLS_MODEL=fid PS_DESIGN=gcd_bench_gen PS_HOST=ps7_bench.v
{ echo "research $(cd /root/wt-r14 && git rev-parse HEAD) field $FIELD"; md5sum $HW/gcd_bench_gen.bit $GLS_SDF
  /root/wt-r14/cells/gls/ps/build_ps.sh $HW $W "" bit || { echo BUILD_FAIL; exit 1; }
  cd $W && vvp gate.vvp | grep -E "ANNOTATE_DONE|WARNING|ERROR" | head -5
  vvp run_baked.vvp +VECFILE=/root/t17/gcdcost_vec.hex +NRUNS=2 | grep -E "^BENCH" | head -60
} > $L 2>&1
rm -f $W/*.vvp; echo DONE >> $L; cp $L /home/user/asyncfpga3/audit/t17/$TAG.log
