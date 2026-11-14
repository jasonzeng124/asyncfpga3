#!/usr/bin/env bash
# T94: entry trace for colnl_4 SLOW_MAX batch 4; vvp killed after 18 min wall (window is reached by then) so the log flushes.
cd /home/user/asyncfpga3/audit/t90
export TRACE="n_falseResult_3_data:32:n_falseResult_3_req,n14__0_data:1:n14__0_req" TRACE_EDGES="bridge_i.op0_to_core[8],bridge_i.op0[8],n_falseResult_3_data[8],bridge_i.op0_to_core[6]"
export TRACE_T0=13000000 TRACE_T1=14700000 PS_MON_GEN=/home/user/asyncfpga3/audit/t94/mon_val.py VEC=/home/user/asyncfpga3/audit/t94/vec5.hex HWD=colnl_4 GLS_SDF_FIELD=max
( sleep 1080; pkill -f "run_baked.vvp.*vec5" ) &
bash ../t91/gate_vec.sh collatz trace4_slowmax
echo DONE > /root/t94_trace4.done
