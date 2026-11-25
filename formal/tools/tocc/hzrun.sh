#!/bin/bash
cd /tmp/claude-0/tocc
run() {  # c pairlist
  c=$1; shift
  for pr in "$@"; do a=${pr%,*}; b=${pr#*,}
    for adv in '{}' '{"pos":0}' '{"pos":1}' '{"rand":1}' '{"rand":2}' '{"rand":3}'; do
      tag=$(echo "$adv" | tr -dc 'a-z0-9')
      f=hz/h_c${c}_${a}_${b}_${tag:-mid}.pkl
      ADV="$adv" OUT=$f timeout 600 python3 simx.py $c $a $b > /dev/null 2>&1
      python3 hazchk.py $f >> hz/res_c$c.txt 2>&1
    done
  done
}
P="12,18 18,12 17,5 5,17 7,7 8,12 0,7 7,0 40,24 3,1000 255,1 1071,462"
run 0 $P &
run 1 $P
wait
echo done > hz/done
