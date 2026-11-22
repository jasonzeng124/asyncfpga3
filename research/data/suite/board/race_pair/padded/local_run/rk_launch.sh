#!/bin/bash
# rk_launch.sh FLOW K S -- flow v10's or v11's environment (as their farm parts) + AUTO_RACE_KAPPA=0.13, SUITE_TAG=rk10 / rk11
F=$1; K=$2; S=$3
cd /tmp/bot/repo
export RUNS=/tmp/bot/runs/rk; mkdir -p $RUNS
if [ "$F" = v10 ]; then
  env CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 \
    AUTO_PROVED_RW=cache AUTO_RACE_KAPPA=0.13 SUITE_TAG=rk10 research/tools/suite/suite_one.sh "$K" "$S" 4 4 > $RUNS/${K}_${S}_v10.log 2>&1
else
  env CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 CA_BENCHCAP=1 AUTO_TRIM=1 AUTO_TRIM_SCOPE=cycle AUTO_RACE_Z=4.5 \
    AUTO_PROVED_RW=cache AUTO_OVERBUILD=3 AUTO_OVERBUILD_LATE=4 TRIM_STAGEFIX=1 AUTO_RACE_KEEP=1 \
    AUTO_PROVED_RW_CACHE=research/data/autorw/cache_v11.tsv AUTO_RACE_KAPPA=0.13 SUITE_TAG=rk11 \
    research/tools/suite/suite_one.sh "$K" "$S" 4 4 > $RUNS/${K}_${S}_v11.log 2>&1
fi
