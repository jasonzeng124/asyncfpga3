#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t67
bash build_pmr.sh pmr 1 > build_pmr_1.log 2>&1
bash run.sh pmr_1 &
bash build_pmr.sh pmr 3 > build_pmr_3.log 2>&1
bash run.sh pmr_3
wait; echo DONE > lanes81.done
