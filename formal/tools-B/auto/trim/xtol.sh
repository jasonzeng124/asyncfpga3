#!/usr/bin/env bash
# tools-B/auto/trim/xtol.sh RUNDIR K  (shard B, UNTRUSTED simulation): the path-error tolerance of a route's weakest steer race
# at research's bands (chains 0.20 / rest 0.31, CARRY 1.0, no scatter): xsweep.py with that steer's condition cone +x and
# its request walk -x; prints the first x with storage pulses and the first x that is not a pass.
D=$1; K=$2; H=$(cd "$(dirname "$0")/.." && pwd)
[ -f $D/steersafe.txt ] || python3 $H/steersafe.py $D/w/m --auto > $D/steersafe.txt 2>&1
st=$(head -1 $D/steersafe.txt | awk '{print $1}' | sed 's/\$LUT[56]$//; s/\./\\./g')
python3 $H/steersafe.py $D/w/m --auto --only "$st" --classes $D/adv_w.json > /dev/null 2>&1
out=$(XBANDS=0.20,0.31 timeout 3000 python3 $H/trim/xsweep.py $D $K $D/adv_w.json 2>&1 | grep "x=")
fp=$(echo "$out" | grep -v "pulses 0$" | head -1 | grep -o "x=[0-9.]*"); ff=$(echo "$out" | grep -v "RESULT OK" | head -1 | grep -o "x=[0-9.]*: [A-Z]*")
echo "$D | weakest steer $st ($(head -1 $D/steersafe.txt | grep -o 'kappa_lo -\?[0-9.]*$')) | first pulses ${fp:-none to 0.25} | first failure ${ff:-none to 0.25}"
