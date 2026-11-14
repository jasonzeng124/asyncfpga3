#!/usr/bin/env bash
# T97: counter trace on fxf2 seed 1 FAST_MIN, rounds = 4 (92d68ca2): i+1 (n29), loop-back pipe output (n_trueResult_6), counter link (n7).
cd /home/user/asyncfpga3/audit/t90
export TRACE="n29_data:32:n29_req" TRACE_EDGES="n29_data[1],n29_data[2],ulink_n_trueResult_6.many.dat[33],ulink_n_trueResult_6.many.dat[34],n_trueResult_6_data[1],n_trueResult_6_data[2],n_trueResult_6_req,n_trueResult_6_ack,n_trueResult_6_u_req,n7_data[1],n7_data[2]" TRACE_T0=2040000 TRACE_T1=2090000
export PS_MON_GEN=/home/user/asyncfpga3/audit/t94/mon_val.py VEC=/home/user/asyncfpga3/audit/t97/vec_f5.hex HWD=xf2_1 GLS_SDF_FIELD=min
bash ../t91/gate_vec.sh xorshift trace3_fastmin
echo DONE > /root/t97tr3.done
