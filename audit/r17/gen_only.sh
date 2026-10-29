#!/bin/bash
# usage: gen_only.sh WORK REGION WIRE DRAW : build_fid.sh's fasm2net + gen.py steps only (no iverilog), seed-9 route, band column
source ~/audit-tc/openxc7/export.sh >/dev/null 2>&1
export TC=~/audit-tc PYTHONPATH=~/audit-tc/openxc7-src/prjxray
HW=~/r17work/wt-s9/cells/build/hw/gcd_hw; G=~/r17work/wt-s9/cells/gls; W=$1; mkdir -p $W
export GLS_SDF=$HW/gcd_hw_xray.sdf GLS_SDF_FIELD=band GLS_MODEL=fid
if [ "$2" != 0 ]; then export GLS_SCATTER_REGION=$2 GLS_SCATTER=$3 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=$4; fi
if [ ! -f $W/fid/fasm_routed.json ]; then
python3 $G/fid/fasm2net.py --bit $HW/gcd_hw.bit --out $W/fid --names $HW/gcd_hw_routed.json --sdf $GLS_SDF; fi
cp $W/fid/fasm_routed.json $W/routed.json; cp $W/fid/fasm.sdf $W/routed.sdf
cd $W && GLS_WORK=$W python3 $G/gen.py && GLS_WORK=$W python3 $G/gen_chan.py && GLS_WORK=$W python3 $G/gen_signals.py
