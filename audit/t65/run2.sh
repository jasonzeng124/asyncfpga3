#!/usr/bin/env bash
# T65: full-stack GLS of a board route (own build, own prjxray SDF). usage: run.sh collatz|collatz64 TAG (GLS_SDF_FIELD=band|min|max)
# case: chains band 0.21, CARRY4/SELMUX2_1/SLICE_FFX band 1 (SLOW_MAX), rest band 0.288, M scatter region 0.02 +
# wire 0.126 (mode wire, draw 1). Host clock 83.3 MHz (+FCLK_PS=12000 = board CLK 0x00100C00). Adapted from T40.
set -u
K=$1; TAG=$2
R=/root/wt-r65; HW=/root/t65/${HWD:-$K}; W=/root/t65/work_${HWD:-$K}_$TAG; L=/root/t65/${HWD:-$K}_$TAG.log
VEC=$(ls /home/user/asyncfpga3/audit/t65/${K}_1?.hex); D=${K}_bench_gen
source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray XRAY_DB=/root/dev2/lib/xray/prjxray-db/zynq7
export GLS_SDF=$HW/${D}_xray_${GLS_SDF_FIELD:-band}.sdf GLS_MODEL=fid PS_DESIGN=$D PS_HOST=ps7_bench.v
export GLS_SDF_FIELD=${GLS_SDF_FIELD:-band}
if [ "$GLS_SDF_FIELD" = band ]; then
  export GLS_SDF_BAND=0.288 GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1
  python3 $R/research/tools/band_inst_list.py $HW/${D}_routed.json '\.chain\.g\[\d+\]\.u$' 0.21 /root/t65/${HWD:-$K}_chains.band
  export GLS_SDF_BAND_INST=@/root/t65/${HWD:-$K}_chains.band
  export GLS_SCATTER_REGION=0.02 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=1
fi
{ echo "T65 $TAG  $(date -u)"; env | grep -E '^(GLS_|PS_|PYTHONPATH|XRAY_DB)' | sort
  [ -f $GLS_SDF ] || { echo "\$ python3 $R/cells/gls/fid/xray_delay.py --routed $HW/${D}_routed.json --sdf $HW/$D.sdf --out $GLS_SDF"
    python3 $R/cells/gls/fid/xray_delay.py --routed $HW/${D}_routed.json --sdf $HW/$D.sdf --out $GLS_SDF 2>&1 | tail -5; }
  md5sum $HW/$D.bit $HW/$D.sdf $GLS_SDF $HW/${D}_routed.json $VEC
  [ -f /root/t65/${HWD:-$K}_chains.band ] && echo "chain-band cells: $(grep -c . /root/t65/${HWD:-$K}_chains.band)"
  echo "\$ $R/cells/gls/ps/build_ps.sh $HW $W \"\" bit"
  /usr/bin/time -v $R/cells/gls/ps/build_ps.sh $HW $W "" bit 2>&1 | grep -vE "^\s+(Average|Socket|Signals|Page|Swaps|File|Major|Minor|Volun|Invol|Exit|Percent|System|User|Command)" || { echo BUILD_FAIL; exit 1; }
  [ -f $W/run_baked.vvp ] || { echo BUILD_FAIL; exit 1; }
  cd $W && vvp gate.vvp | grep -E "ANNOTATE_DONE|WARNING|ERROR" | head -5
  rm -f gate.vvp
  echo "\$ vvp run_baked.vvp +FCLK_PS=12000 +MODE=1 +VECFILE=$VEC +NRUNS=2 +TBATCH=${TBATCH:-1000000}"
  /usr/bin/time -v vvp run_baked.vvp +FCLK_PS=12000 +MODE=1 +VECFILE=$VEC +NRUNS=2 +TBATCH=${TBATCH:-1000000} 2>&1 | grep -vE "^\s+(Average|Socket|Signals|Page|Swaps|File|Major|Minor|Volun|Invol|Exit|Percent|System|User|Command)"
  rm -f run_baked.vvp
} > $L 2>&1
echo DONE >> $L
