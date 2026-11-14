#!/usr/bin/env bash
# T97: counter trace on fxf2 seed 1 FAST_MIN, rounds = 4 (92d68ca2): i+1 (n29), loop-back pipe output (n_trueResult_6), counter link (n7).
cd /home/user/asyncfpga3/audit/t90
export TRACE="n29_data:32:n29_req,n30__1_data:32:n30__1_req,n11__1_data:32:n11__1_req,n31_data:1:n31_req,n_trueResult_6_data:32:n_trueResult_6_req" TRACE_T0=0 TRACE_T1=999999999
export PS_MON_GEN=/home/user/asyncfpga3/audit/t94/mon_val.py VEC=/home/user/asyncfpga3/audit/t97/vec_f5.hex HWD=xf2_1 GLS_SDF_FIELD=min
bash ../t91/gate_vec.sh xorshift trace2_fastmin
echo DONE > /root/t97tr2.done
