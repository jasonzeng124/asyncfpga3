#!/usr/bin/env bash
# T46: full-stack GLS of the x0.75 ipow bench route (my own build) at the "combined worst case":
# chains at band 0.21, CARRY4/SELMUX2_1/SLICE_FFX at band 1 (SLOW_MAX), rest band 0.288, M scatter region 0.02 +
# wire 0.126 (mode wire, draw 1); host ps7_bench.v at FCLK_PS=12000 (83.3 MHz). Adapted from audit/t40/run_worst.sh.
set -u
TAG=${1:-s75_worst}
R=/root/wt-r34; HW=/root/t55/cd; W=/root/t55/work_$TAG; L=/root/t55/$TAG.log
VEC=/root/t55/ipow17.hex
source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray XRAY_DB=/root/dev2/lib/xray/prjxray-db/zynq7
export GLS_SDF=$HW/ipow_bench_gen_xray.sdf GLS_MODEL=fid PS_DESIGN=ipow_bench_gen PS_HOST=ps7_bench.v
export GLS_SDF_FIELD=band GLS_SDF_BAND=0.288 GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1
export GLS_SDF_BAND_INST=@/root/t55/chains.band
export GLS_SCATTER_REGION=0.02 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=1
{ echo "T46 $TAG  $(date -u)"
  if [ ! -s $GLS_SDF ]; then
    echo "\$ python3 $R/cells/gls/fid/xray_delay.py --routed ... --sdf ... --out $GLS_SDF"
    python3 $R/cells/gls/fid/xray_delay.py --routed $HW/ipow_bench_gen_routed.json --sdf $HW/ipow_bench_gen.sdf \
        --out $GLS_SDF 2>&1 | tail -15 || { echo XRAY_FAIL; exit 1; }
  fi
  python3 $R/research/tools/band_inst_list.py $HW/ipow_bench_gen_routed.json '\.chain\.g\[\d+\]\.u$' 0.21 /root/t55/chains.band
  head -1 /root/t55/chains.band
  env | grep -E '^(GLS_|PS_|PYTHONPATH|XRAY_DB)' | sort
  md5sum $HW/ipow_bench_gen.bit $HW/ipow_bench_gen.sdf $GLS_SDF $HW/ipow_bench_gen_routed.json $VEC /root/t55/chains.band
  $R/cells/gls/ps/build_ps.sh $HW $W "" bit || { echo BUILD_FAIL; exit 1; }
  cd $W && vvp gate.vvp | grep -E "ANNOTATE_DONE|WARNING|ERROR" | head -5
  rm -f gate.vvp
  echo "\$ vvp run_baked.vvp +FCLK_PS=12000 +MODE=1 +VECFILE=$VEC +NRUNS=2 +TBATCH=1000000"
  /usr/bin/time -v vvp run_baked.vvp +FCLK_PS=12000 +MODE=1 +VECFILE=$VEC +NRUNS=2 +TBATCH=1000000 2>&1 | grep -vE "^\s+(Average|Socket|Signals|Page|Swaps|File|Major|Minor|Volun|Invol|Exit|Percent|System|User|Command)"
} > $L 2>&1
echo DONE >> $L
