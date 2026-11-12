#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t67
EXTRA="BDC_MERGE_RES_LINK=ucontrol_merge0" TAGO=colr bash build_colx.sh 1 > build_colr_1.log 2>&1
bash run_col.sh colr_1 & bash run_col.sh colb_1; wait
echo DONE > lanes87.done
