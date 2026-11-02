#!/usr/bin/env bash
# T12: gcd_ps full stack (VEC=file overrides the vector file) (bit-decoded netlist, prjxray SDF, fid, PS7 model) on MY rebuild (/root/bq4ref = BQ#4 seed d),
# research's harness at research ee8d8869 (/root/wt-r14), MY vectors and MY oracle. usage: run_ps.sh TAG [env K=V ...]
set -u
TAG=$1; shift
source /root/audit-tc/openxc7/export.sh
export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray:${PYTHONPATH:-} XRAY_DB=/root/dev2/lib/xray/prjxray-db/zynq7
export GLS_SDF=/root/bq4ref/gcd_ps_xray.sdf GLS_SDF_FIELD=band GLS_MODEL=fid PS_BUNDLE=1
for kv in "$@"; do export "$kv"; done
W=/root/t12/$TAG; L=/root/t12/$TAG.log; A=/home/user/asyncfpga3/audit/t12
mkdir -p /root/t12
{ env | grep '^GLS_\|^PS_' | sort; echo "research $(cd /root/wt-r14 && git rev-parse HEAD)"
  md5sum /root/bq4ref/gcd_ps.bit /root/bq4ref/gcd_ps_xray.sdf /root/bq4ref/gcd_ps_routed.json
  /root/wt-r14/cells/gls/ps/build_ps.sh /root/bq4ref $W ${VEC:-$A/own_vec24.hex} bit || { echo BUILD_FAIL; exit 1; }
  cd $W && vvp gate.vvp | grep -E "ANNOTATE_DONE|WARNING|ERROR" | head -5
  vvp run_baked.vvp +PSVEC=ps_vec.hex | grep -E "^PS|BUNDLE|bundle" | head -400
} > $L 2>&1
python3 $A/check_psres.py $L >> $L
rm -f $W/*.vvp; echo DONE >> $L; cp $L $A/$TAG.log
