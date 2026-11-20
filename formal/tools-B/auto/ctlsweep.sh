#!/usr/bin/env bash
# tools-B/auto/ctlsweep.sh RUNDIR K  (shard B, UNTRUSTED simulation): RUNDIR = a suite/task.sh output (w/m decoded,
# exp.txt, pairs.txt). Takes the latch-fed steer with the smallest ctl-launched slack (steersafe.py --auto), builds its
# race-only adversary (ctlrace.py) and runs simx at kappa 0, 0.03, 0.06, 0.10, 0.15, 0.20 (KDEN 100), corners 0 / 1,
# until the first non-OK. One line: route, steer, slack, first failure.
set -uo pipefail
D=$1; K=$2; H=$(cd "$(dirname "$0")" && pwd); M=$D/w/m
[ -f $D/steersafe.txt ] || python3 $H/steersafe.py $M --auto > $D/steersafe.txt 2>&1
row=$(grep "latch, condition" $D/steersafe.txt | grep -o '^[^ ]*\|ctl-launched slack [-+0-9]* / [-+0-9]*' | paste - - | awk '{print $4+0, $1, $4, $6}' | sort -g | head -1)
[ -n "$row" ] || { echo "$D: no latch-fed steer"; exit 0; }
set -- $row; ST=$2; s0=$3; s1=$4; base=$(echo $ST | sed 's/\$LUT[56]$//; s/\./\\./g')
python3 $H/ctlrace.py $M "$base" $D/ctl_adv.json > $D/ctl_adv.txt 2>&1
P=$(cat $D/pairs.txt); W=$(python3 -c "print(','.join(str(int(l.split()[0],16)) for l in open('$D/exp.txt') if l.strip() and not l.startswith('//')))")
first="none up to 0.20"
for k in 0 0.03 0.06 0.10 0.15 0.20; do r=""
  for c in 0 1; do
    KDEN=100 timeout 1500 $M/simx $M/net.simx --periodic --maxev 300000000 --kernel $K --want $W --pairs $P --corner $c --kappa $k \
      --classes $D/ctl_adv.json --cdefault M --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq --tmax 400000000 \
      --hostdelay 12000 --w 20 > $D/ctl_o.txt 2>&1
    v=$(grep -o 'RESULT [A-Z]*\|MAXEV cap' $D/ctl_o.txt | head -1 | sed 's/RESULT //; s/MAXEV cap/NO-VERDICT/'); r="$r c$c:${v:-NONE}/$(grep -o 'pulses < 200 ps: [0-9]*' $D/ctl_o.txt | grep -o '[0-9]*$')"
  done
  case "$r" in *MISMATCH*|*NO-VERDICT*|*NONE*|*HANG*|*FAIL*) first="kappa $k ($r)"; break;; esac
done
echo "$D | steer $ST ctl slack $s0 / $s1 ps | first failure: $first"
