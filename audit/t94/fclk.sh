#!/usr/bin/env bash
# T94: (a) colnl_4 SLOW_MAX at host clock 41.7 MHz (FCLK_PS=24000): if it passes, the 83.3 MHz failure is the clocked
# harness; (b) edge trace of bridge_i.bench_op0[8] at 83.3 MHz.
cd /home/user/asyncfpga3/audit/t90; V=$(ls ../t65/collatz_1?.hex)
( FCLK=24000 HWD=colnl_4 GLS_SDF_FIELD=max bash ../t94/gate_fclk.sh collatz slowmax_f24
  python3 ../t65/oracle_collatz.py check $V /root/t65/colnl_4_slowmax_f24.log 2 > /root/t90/colnl_4_slowmax_f24_oracle.txt 2>&1 ) &
sleep 30
( export TRACE="n_falseResult_3_data:32:n_falseResult_3_req" TRACE_EDGES="bridge_i.bench_op0[8],bridge_i.bench_op0[6],bridge_i.op0[8],bridge_i.bench_busy"
  export TRACE_T0=13000000 TRACE_T1=14700000 PS_MON_GEN=/home/user/asyncfpga3/audit/t94/mon_val.py VEC=/home/user/asyncfpga3/audit/t94/vec5.hex HWD=colnl_4 GLS_SDF_FIELD=max
  ( sleep 1080; pkill -f "run_baked.vvp.*vec5" ) & bash ../t91/gate_vec.sh collatz trace5_slowmax ) &
wait; echo DONE > /root/t94_fclk.done
