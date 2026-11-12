#!/usr/bin/env bash
# T70: FAST_MIN + M scatter stress on select-unsafe board seeds (items 7, 13, 4), draws 1 and 2
cd /home/user/asyncfpga3/audit/t65
lane() { while [ $# -gt 0 ]; do HWD=$2 FMS_SEED=$3 GLS_SDF_FIELD=min bash run3.sh $1 fms$3; shift 3; done; }
lane ipow ipow75 1  ipow ipowfm_1 1  xorshift x50_1 1 &
lane ipow ipow75 2  ipow ipowfm_1 2  xorshift x50_1 2 &
wait; echo DONE > lanes70.done
