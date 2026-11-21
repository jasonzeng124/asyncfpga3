#!/bin/bash
# env-stall sweep (UNTRUSTED). per corner, per gate-delay setting, per env move, per D.
cd /tmp/claude-0/r1
A=${A:-12}; B=${B:-18}
for c in ${CS:-1 0}; do for pos in mid 0 1; do
  if [ $pos = mid ]; then ADVJ='{}'; else ADVJ="{\"pos\":$pos}"; fi
  ref=adv/r_${A}_${B}_c${c}_p${pos}_none_0.pkl
  ADV="$ADVJ" ENVD='{}' OUT=$ref python3 simenv.py $c $A $B > /dev/null
  for key in req_rise req_fall pack_rise pack_fall oack_rise oack_fall rst all; do for D in 5000 50000 500000; do
    f=adv/r_${A}_${B}_c${c}_p${pos}_${key}_${D}.pkl
    ADV="$ADVJ" ENVD="{\"$key\":$D}" OUT=$f timeout 600 python3 simenv.py $c $A $B > /dev/null
    python3 envchk.py $ref $f
  done; done
  python3 envchk.py $ref $ref
done; done
