#!/bin/bash
# race-2 adversary. usage: adv2.sh c A B kappa
c=$1; A=$2; B=$3; k=$4
ADV=$(python3 -c "import json;s=json.load(open('/tmp/claude-0/race/sets2_c$c.json'));s['kappa']=$k;print(json.dumps(s))")
OUT=/tmp/claude-0/race/runs/r2_${A}_${B}_c${c}_k${k}.pkl ADV="$ADV" python3 /tmp/claude-0/race/simk.py $c $A $B > /dev/null
