#!/usr/bin/env bash
# T90: period per step at research's itercost corner (as t67/run_col.sh: chains 0.21, CARRY4/F7F8/FF band 1, rest 0.288,
# NO scatter), 83.3 MHz host; P = d(latmin)*fclk/d(steps) by t67/period_col.py. usage: run_per.sh collatz|collatz64 RUN
set -u
K=$1; RUN=$2; R=/root/wt-r90; HW=/root/t65/$RUN; W=/root/t90/work_per_$RUN; L=/root/t90/per_$RUN.log; D=${K}_bench_gen
case $K in collatz) VEC=/home/user/asyncfpga3/audit/t90/col_period.hex;; collatz64) VEC=/home/user/asyncfpga3/audit/t90/c64_period.hex;; esac
mkdir -p /root/t90; source /root/audit-tc/openxc7/export.sh >/dev/null 2>&1
export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray XRAY_DB=${XRAY_DB:-/root/dev2/lib/xray/prjxray-db/zynq7}
export GLS_SDF=$HW/${D}_xray.sdf GLS_MODEL=fid PS_DESIGN=$D PS_HOST=ps7_bench.v GLS_SDF_FIELD=band
export GLS_SDF_BAND=0.288 GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1
python3 $R/research/tools/band_inst_list.py $HW/${D}_routed.json '\.chain\.g\[\d+\]\.u$' 0.21 $HW/chains.band >/dev/null
export GLS_SDF_BAND_INST=@$HW/chains.band
{ echo "T90 per $RUN $(date -u)"; env | grep -E '^(GLS_|PS_)' | sort
  [ -f $GLS_SDF ] || python3 $R/cells/gls/fid/xray_delay.py --routed $HW/${D}_routed.json --sdf $HW/$D.sdf --out $GLS_SDF 2>&1 | tail -2
  md5sum $HW/$D.bit $HW/$D.sdf $GLS_SDF $VEC; echo "chain-band cells: $(grep -c . $HW/chains.band)"
  $R/cells/gls/ps/build_ps.sh $HW $W "" bit 2>&1 | grep -E "VERDICT|ERROR|rror" | head -5
  [ -f $W/run_baked.vvp ] || { echo BUILD_FAIL; exit 1; }
  cd $W && rm -f gate.vvp && vvp run_baked.vvp +FCLK_PS=12000 +MODE=1 +VECFILE=$VEC +NRUNS=2 +TBATCH=1000000 2>&1 | grep -E "BENCHRES|FAIL|PASS"
  rm -f run_baked.vvp
} > $L 2>&1
echo DONE >> $L
python3 /home/user/asyncfpga3/audit/t67/period_col.py $L >> $L
