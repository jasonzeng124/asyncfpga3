#!/usr/bin/env bash
# run_point.sh TAG REGION WIRE [VECS] [extra env K=V ...] ; builds+runs BQ#2 seed-6 full stack at band 0.38
set -u
TAG=$1; REG=$2; WIRE=$3; VECS=${4:-all}; shift 4 || shift $#
source /root/audit-tc/openxc7/export.sh
HW=${HW:-/root/wt-r14/cells/build/hw/gcd_hw}
W=/root/r23work/$TAG; L=/root/r23work/$TAG.log; FINAL=/home/user/asyncfpga3/audit/r23/$TAG.log
mkdir -p /root/r23work
export GLS_SDF=$HW/gcd_hw_xray.sdf GLS_SDF_FIELD=${FIELD:-band} GLS_MODEL=fid PYTHONPATH=/root/audit-tc/openxc7-src/prjxray:$PYTHONPATH
export XRAY_DB=/root/dev2/lib/xray/prjxray-db/zynq7
if [ "$REG" != 0 ]; then export GLS_SCATTER_REGION=$REG GLS_SCATTER=$WIRE GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=1; fi
for kv in "$@"; do export "$kv"; done
{ env | grep '^GLS_' | sort
  /root/wt-r14/cells/gls/fid/build_fid.sh $HW $W bit || { echo BUILD_FAIL; exit 1; }
  md5sum $W/netlist_baked.v
  cd $W; mkdir -p sweep
  if [ "$VECS" = all ]; then VL=$(seq 0 15); else VL=${VECS//,/ }; fi
  for v in $VL; do vvp run_baked.vvp "+VEC=$v" "+TEND=${TEND:-150000}" "+QUIET=200000" > sweep/v$v.log 2>&1
     echo "vec $v: $(grep -m1 RESULT sweep/v$v.log) | $(grep -m1 SUMMARY sweep/v$v.log)"; done
  rm -f run_baked.vvp gate.vvp
} > $L 2>&1
echo DONE >> $L
cp $L $FINAL
