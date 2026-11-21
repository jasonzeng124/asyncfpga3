#!/bin/bash
# guard_est.sh -- for every census route (/tmp/bot/steertol/K: the rule's inputs for flow v10's shipped iteration as built):
# the rule at the 10 % E / J guard (both bands, merged), so guard_est.py can price what grows on the critical cycle
cd /tmp/bot/repo; O=/tmp/bot/steertol
one() { local K=$1 c=$2 CA=$O/$1
  BD_SKEW_MUXN=1 BD_SKEW_E_JOIN_DEPTH=1 PYTHONHASHSEED=1 CA_FAST=1 BD_RAM_GUARD_PS=400 BD_SKEW_STEER_SELF=1 CA_JOINAWARE=1 \
  BD_SKEW_AND_JOIN=1 CA_SIZERULE=1 CA_BENCHCAP=1 python3 research/tools/corner_audit.py $CA/seed1 --prefix bridge_i.udut. \
    --band $c --inst-rx '\.chain\.g\[\d+\]\.u$:0.20' --guard-lo 0.90 --guard-hi 1.10 --out $CA/ruleG_$c > $CA/caG_$c.txt 2>&1; }
for d in $O/*/; do K=$(basename $d); [ -d $d/seed1 ] || continue; [ -f $d/ruleG/sizes.vh ] && continue
  for c in 0.20 0.31; do one $K $c & while [ "$(jobs -rp | wc -l)" -ge ${SJ:-4} ]; do sleep 3; done; done
done; wait
for d in $O/*/; do [ -d $d/rule_0.20 ] && [ ! -f $d/rule/sizes.vh ] && python3 research/tools/auto/merge_rules.py $d/rule $d/rule_0.20 $d/rule_0.31 > /dev/null 2>&1
  [ -d $d/ruleG_0.20 ] && python3 research/tools/auto/merge_rules.py $d/ruleG $d/ruleG_0.20 $d/ruleG_0.31 > /dev/null 2>&1; done
echo DONE > $O/guard_est.done
