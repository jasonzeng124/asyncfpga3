#!/usr/bin/env bash
# T21: restart-tolerant variant of run_kernel.sh: keeps the built work dir, runs the vectors in chunks of 4
# (one vvp per chunk, output kept per chunk) and skips chunks already finished.  usage: run_kernel_resume.sh DESIGN FIELD VECHEX
set -u
D=$1; FIELD=$2; VEC=$3; TAG=${D}_$FIELD
source /root/audit-tc/openxc7/export.sh
export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray:${PYTHONPATH:-} XRAY_DB=/root/dev2/lib/xray/prjxray-db/zynq7
HW=/root/t21/hw/$D; W=/root/t21/$TAG; C=/root/t21/${TAG}_chunks; L=/root/t21/$TAG.log
export GLS_SDF=$HW/${D}_xray.sdf GLS_SDF_FIELD=$FIELD GLS_MODEL=fid PS_DESIGN=$D PS_HOST=ps7_bench.v
mkdir -p $C
if [ ! -s $W/run_baked.vvp ] || [ ! -s $C/built ]; then
  rm -rf $W; { echo "research $(cd /root/wt-r14 && git rev-parse HEAD) field $FIELD"; md5sum $HW/$D.bit $GLS_SDF $VEC
    /root/wt-r14/cells/gls/ps/build_ps.sh $HW $W "" bit || { echo BUILD_FAIL; exit 1; }
    cd $W && vvp gate.vvp | grep -E "ANNOTATE_DONE|WARNING|ERROR" | head -5; } > $C/header 2>&1
  grep -q BUILD_FAIL $C/header && exit 1; echo ok > $C/built
fi
split -l 4 -d $VEC $C/vec_ 2>/dev/null || true
for v in $C/vec_[0-9][0-9]; do
  [ -s $v.out ] && grep -q "^BENCHSUMMARY" $v.out && continue
  (cd $W && vvp run_baked.vvp +VECFILE=$v +NRUNS=2 | grep -E "^BENCH" > $v.tmp) && mv $v.tmp $v.out
done
{ cat $C/header; cat $C/vec_[0-9][0-9].out; echo DONE; } > $L
cp $L /home/user/asyncfpga3/audit/t21/$TAG.log
