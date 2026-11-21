#!/bin/bash
# guardx.sh K -- the sizing rule on flow v10's K s1 route as built, rule E/J guard 0.90 / 1.10 instead of 0.97 / 1.03
K=$1; cd /tmp/bot/repo
case $K in collatz64) HW=/tmp/bot/runs/bq10c64/hw/bq_collatz64_1; RD=/tmp/bot/runs/bq10c64/r/bq_collatz64_1;;
  *) HW=/tmp/bot/runs/bq10/hw/bq10_${K}_1; RD=/tmp/bot/runs/bq10/r/bq10_${K}_1;; esac
CA=/tmp/bot/carryx/${K}_G10; rm -rf $CA; mkdir -p $CA/seed1/pnr
ln -sf $RD/xray.sdf $CA/seed1/pnr/soak_xray.sdf; ln -sf $HW/${K}_bench_gen_routed.untrimmed.json $CA/seed1/pnr/soak_routed.json
cp research/data/suite/board/${K}_v10_s1_sizes.vh $CA/seed1/pnr/sizes.vh
for c in 0.20 0.31; do
  BD_SKEW_MUXN=1 BD_SKEW_E_JOIN_DEPTH=1 PYTHONHASHSEED=1 CA_FAST=1 BD_RAM_GUARD_PS=400 BD_SKEW_STEER_SELF=1 CA_JOINAWARE=1 \
  BD_SKEW_AND_JOIN=1 CA_SIZERULE=1 CA_BENCHCAP=1 python3 research/tools/corner_audit.py $CA/seed1 --prefix bridge_i.udut. \
    --band $c --inst-rx '\.chain\.g\[\d+\]\.u$:0.20' --guard-lo 0.90 --guard-hi 1.10 --out $CA/rule_$c > $CA/ca_$c.txt 2>&1 &
done; wait
python3 research/tools/auto/merge_rules.py $CA/rule $CA/rule_0.20 $CA/rule_0.31 > /dev/null 2>&1; echo "$K done"
