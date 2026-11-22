#!/bin/bash
# so_launch.sh -- AUTO_SEARCH_OVERBUILD test: quadrec s3 resumed from /tmp/bot/runs/so_state (kd's state at the end of
# its finish phase), v13 + AUTO_SEARCH_KEEPDEPTH + AUTO_SEARCH_OVERBUILD=4 + AUTO_SEARCH_MAXIT=1 + AUTO_CKPT, names kd_*
cd /tmp/bot/repo
export RUNS=/tmp/bot/runs/so2; mkdir -p $RUNS
env CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 \
  AUTO_PROVED_RW=cache AUTO_OVERBUILD=3 AUTO_OVERBUILD_LATE=4 TRIM_STAGEFIX=1 AUTO_RACE_KEEP=1 \
  AUTO_PROVED_RW_CACHE=research/data/autorw/cache_v11.tsv AUTO_LATE_AFTER_SEARCH=1 AUTO_GUARD_E=0.90,1.10 \
  AUTO_RACE_KAPPA=0.13 BDC_MEM_FASTFALL=2 AUTO_TRIM_PORTS=1 AUTO_CKPT=1 AUTO_SEARCH_KEEPDEPTH=1 \
  AUTO_SEARCH_OVERBUILD=4 AUTO_SEARCH_MAXIT=1 AUTO_RESUME=/tmp/bot/runs/so2_state AUTO_TRIM_ONLY=1 SUITE_TAG=kd \
  research/tools/suite/suite_one.sh quadrec 3 4 4 > $RUNS/quadrec_3.log 2>&1
echo "so2 done $(date -u +%H:%M)" >> $RUNS/quadrec_3.log
