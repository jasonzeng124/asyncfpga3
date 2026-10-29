#!/bin/bash
# usage: sweep.sh <workdir> <outname> [vectors...]; -j2, TEND 150000, QUIET 200000
W=$1; N=$2; shift 2; V=${@:-$(seq 0 15)}
mkdir -p $W/$N; cd $W
for v in $V; do
  while [ "$(jobs -rp | wc -l)" -ge 2 ]; do sleep 2; done
  ( vvp run_baked.vvp +VEC=$v +TEND=150000 +QUIET=200000 > $N/v$v.log 2>&1 ) &
done
wait
for v in $V; do
  printf "vector %2d  %s  viol=%s\n" $v "$(grep -m1 -E 'RESULT|LAPS|TIMEOUT|livelock|wedge' $N/v$v.log || echo NOVERDICT)" "$(grep -c 'VIOLATION' $N/v$v.log)"
done
