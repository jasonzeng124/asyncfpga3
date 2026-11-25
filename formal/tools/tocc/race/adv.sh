#!/bin/bash
# usage: adv.sh c A B kappa mode(mid|adv|rev) tag
c=$1; A=$2; B=$3; k=$4; m=$5; tag=$6
S=/tmp/claude-0/race/sets_c$c.json
case $m in
 mid) ADV='{}';;
 adv) ADV=$(python3 -c "import json;s=json.load(open('$S'));print(json.dumps(dict(hiG=s['hiG'],loG=s['loG'],kappa=$k)))");;
 rev) ADV=$(python3 -c "import json;s=json.load(open('$S'));print(json.dumps(dict(hiG=s['loG'],loG=s['hiG'],kappa=$k)))");;
esac
OUT=/tmp/claude-0/race/runs/r_${A}_${B}_c${c}_${m}_k${k}${tag}.pkl ADV="$ADV" python3 /tmp/claude-0/race/simk.py $c $A $B > /dev/null && echo /tmp/claude-0/race/runs/r_${A}_${B}_c${c}_${m}_k${k}${tag}.pkl
