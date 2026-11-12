#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t67
bash build_t3.sh t3 2 > build_t3_2.log 2>&1
bash build_t3.sh t3pmf 2 > build_t3pmf_2.log 2>&1 &
bash run.sh t3_2
wait; bash run.sh t3pmf_2
echo DONE > lanes76.done
