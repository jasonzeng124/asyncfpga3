#!/usr/bin/env bash
# T40: full-stack GLS of the x0.5 xorshift bench route (my own build) at research's "combined worst case":
# chains at band 0.21, CARRY4/SELMUX2_1/SLICE_FFX at SLOW_MAX (band 1), rest band 0.288, M scatter region 0.02 +
# wire 0.126 (mode wire, draw 1). usage: run_worst.sh TAG [extra env assignments are taken from caller]
set -u
TAG=${1:-s50_worst}
R=/root/wt-r34; HW=/root/t40/s50; W=/root/t40/work_$TAG; L=/root/t40/$TAG.log
VEC=/root/t40/xorshift17.hex
source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray XRAY_DB=/root/dev2/lib/xray/prjxray-db/zynq7
export GLS_SDF=$HW/xorshift_bench_gen_xray.sdf GLS_MODEL=fid PS_DESIGN=xorshift_bench_gen PS_HOST=ps7_bench.v
export GLS_SDF_FIELD=${GLS_SDF_FIELD:-band}
if [ "$GLS_SDF_FIELD" = band ]; then
  export GLS_SDF_BAND=0.288 GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1
  python3 $R/research/tools/band_inst_list.py $HW/xorshift_bench_gen_routed.json '\.chain\.g\[\d+\]\.u$' 0.21 /root/t40/chains.band
  export GLS_SDF_BAND_INST=@/root/t40/chains.band
  export GLS_SCATTER_REGION=0.02 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=1
fi
{ echo "T40 $TAG  $(date -u)"; env | grep -E '^(GLS_|PS_|PYTHONPATH|XRAY_DB)' | sort
  md5sum $HW/xorshift_bench_gen.bit $HW/xorshift_bench_gen.sdf $GLS_SDF $HW/xorshift_bench_gen_routed.json $VEC
  $R/cells/gls/ps/build_ps.sh $HW $W "" bit || { echo BUILD_FAIL; exit 1; }
  cd $W && vvp gate.vvp | grep -E "ANNOTATE_DONE|WARNING|ERROR" | head -5
  rm -f gate.vvp
  echo "\$ vvp run_baked.vvp +MODE=1 +VECFILE=$VEC +NRUNS=2 +TBATCH=1000000"
  /usr/bin/time -v vvp run_baked.vvp +MODE=1 +VECFILE=$VEC +NRUNS=2 +TBATCH=1000000 2>&1 | grep -vE "^\s+(Average|Socket|Signals|Page|Swaps|File|Major|Minor|Volun|Invol|Exit|Percent|System|User|Command)"
} > $L 2>&1
echo DONE >> $L
