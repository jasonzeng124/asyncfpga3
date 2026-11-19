#!/usr/bin/env bash
# board items 38-41 under today's gate: x in a run's SIG fails, RAMB18 events fail, GATE_RUNTS=fail (pulse < 1 ns fails)
cd /tmp/bot/repo; RUNS=/tmp/bot/runs; G=research/data/eventgraph/gate; O=/tmp/bot/bqre/results.txt
one() {
  local K=$1 S=$2 V=$3 c=$4
  local N=bqa_${K}_$S
  local D=${K}_bench_gen
  local W=/tmp/bot/bqre/$N/${c/:/_}
  mkdir -p $W; cp $RUNS/r/$N/xray.sdf $W/
  local r; r=$(GATE_RUNTS=fail research/tools/eventgraph/bench_gate.sh $RUNS/hw/$N $D $W $G/$V.hex $G/$V.exp $c 2>&1 | tail -1)
  echo "$K s$S $c :: $r" >> $O
}
for spec in "ipow 2 ipow17" "collatz 6 col18" "collatz64 5 c6419" "xorshift 8 xor19"; do
  set -- $spec
  for c in worst draw:$((40000 + 100 * $2 + 1)) draw:$((40000 + 100 * $2 + 2)) draw:$((40000 + 100 * $2 + 3)); do
    one $1 $2 $3 $c & while [ "$(jobs -rp | wc -l)" -ge 6 ]; do sleep 5; done
  done
done
wait; echo DONE >> $O
