#!/usr/bin/env bash
# tools-B/auto/weaksweep.sh RUNDIR K [STEER]  (shard B, UNTRUSTED simulation): the race-only adversary of a route's WEAKEST steer
# (any kind: steersafe.py --auto's first row): its condition cone slow, its request walk fast (steersafe --classes),
# simx kappa 0, 0.03, 0.06, 0.10, 0.15, 0.20 at corners 0 / 1 until the first wrong answer / run with no verdict.
set -uo pipefail
# SIMX_EXTRA (2026-11-21): extra simx arguments, e.g. a memory kernel decoded by shard C's memtask.sh:
#   ln -s v/pairs.txt v/exp.txt into its OUT dir; SIMX_EXTRA="--mem OUT/v/mem.txt --tmax 1900000000"
D=$1; K=$2; H=$(cd "$(dirname "$0")" && pwd); M=$D/w/m
bash $H/ensure_m.sh $D > /dev/null   # simx, net.simx, gclass.txt where draws.py left none
[ -f $D/steersafe.txt ] || python3 $H/steersafe.py $M --auto > $D/steersafe.txt 2>&1
row=$(if [ -n "${3:-}" ]; then grep "^$3" $D/steersafe.txt | sort -t_ -k1 | head -1; else head -1 $D/steersafe.txt; fi)   # 3rd arg (2026-11-21): a named steer
 ST=$(echo "$row" | awk '{print $1}'); re=$(echo $ST | sed 's/\$LUT[56]$//; s/\./\\./g')
python3 $H/steersafe.py $M --auto --only "$re" --classes $D/weak_adv.json > /dev/null 2>&1
P=$(cat $D/pairs.txt); W=$(python3 -c "print(','.join(str(int(l.split()[0],16)) for l in open('$D/exp.txt') if l.strip() and not l.startswith('//')))")
first="none up to 0.20"
for k in 0 0.03 0.06 0.10 0.15 0.20; do r=""
  for c in 0 1; do
    KDEN=100 timeout 1500 $M/simx $M/net.simx --periodic --maxev 300000000 --kernel $K --want "$W" --pairs $P --corner $c --kappa $k \
      --classes $D/weak_adv.json --cdefault M --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq --tmax 400000000 \
      --hostdelay 12000 --w 20 ${DRAW_DOUT:+--dout $DRAW_DOUT} ${SIMX_EXTRA:-} > $D/weak_o.txt 2>&1
    v=$(grep -o 'RESULT [A-Z]*\|MAXEV cap' $D/weak_o.txt | head -1 | sed 's/RESULT //; s/MAXEV cap/NO-VERDICT/'); r="$r c$c:${v:-NONE}/$(grep -o 'pulses < 200 ps: [0-9]*' $D/weak_o.txt | grep -o '[0-9]*$')"
  done
  case "$r" in *MISMATCH*|*NO-VERDICT*|*NONE*) first="kappa $k ($r)"; break;; esac
done
echo "$D | weakest $ST $(echo "$row" | grep -o 'kappa_lo -\?[0-9.]*$') | adversary first failure: $first"
