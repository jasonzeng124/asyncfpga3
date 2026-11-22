#!/usr/bin/env bash
# the sizing rule on one route at three delay-model points: the box's worst vertex (chains 0.20, rest 0.31), the other
# vertex (both 0.20), and both bands at the board fit (0.222)
cd /tmp/bot/repo; D=/tmp/bot/runs/ca/su_xorshift_1_4; W=/tmp/bot/boxtest
run() { local name=$1 rest=$2 chain=$3
  PYTHONHASHSEED=1 CA_FAST=1 BD_SKEW_STEER_SELF=1 CA_JOINAWARE=1 BD_SKEW_AND_JOIN=1 CA_SIZERULE=1 \
    python3 research/tools/corner_audit.py $D/seed1 --prefix bridge_i.udut. --band $rest \
      --inst-rx "\.chain\.g\[\d+\]\.u\$:$chain" --out $W/$name > $W/$name.log 2>&1; echo "$name done $?" >> $W/status; }
run v31 0.31 0.20 & run v20 0.20 0.20 & run fit 0.222 0.222 & wait
