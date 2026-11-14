#!/usr/bin/env bash
# T94: entry trace for colnl_4 SLOW_MAX batch 4; vvp killed after 18 min wall (window is reached by then) so the log flushes.
cd /home/user/asyncfpga3/audit/t90
export TRACE="n_data:32:n_req,n_falseResult_3_data:32:n_falseResult_3_req,n9_data:32:n9_req,n14__0_data:1:n14__0_req,n_falseResult_9_data:32:n_falseResult_9_req"
export TRACE_T0=13300000 TRACE_T1=14700000 PS_MON_GEN=/home/user/asyncfpga3/audit/t94/mon_val.py VEC=/home/user/asyncfpga3/audit/t94/vec5.hex HWD=colnl_4 GLS_SDF_FIELD=max
( sleep 1080; pkill -f "run_baked.vvp.*vec5" ) &
bash ../t91/gate_vec.sh collatz trace3_slowmax
echo DONE > /root/t94_trace3.done
