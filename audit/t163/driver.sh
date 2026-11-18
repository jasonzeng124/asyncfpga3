#!/usr/bin/env bash
# sequential: one flow at a time
cd /root/agentD
for job in "wt_rw collatz 6" "wt_norw collatz 6" "wt_norw xorshift 8" "wt_norw collatz 2" "wt_norw xorshift 1"; do
  set -- $job; ./run_one.sh $1 $2 $3 > logs/$1_$2_$3.log 2>&1
done
