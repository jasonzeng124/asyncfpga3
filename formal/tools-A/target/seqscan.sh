#!/usr/bin/env bash
# Sequential-environment scan of the decoded target (sim.py, untrusted): random rig-vector sequences,
# broad data release, corners/positions/scatter. One line per run.  usage: seqscan.sh NET BND N SEED
NET=$1; BND=$2; N=$3; S=$4
HERE=$(cd "$(dirname "$0")" && pwd)
V=(0,5 7,0 0xC,0x12 0x30,0x12 1,1 0x11,5 0x798F20,0x12B87CA0 0x42F,0x1CE 0x10E,0xC0 0x10000,0x1000 0x18697,0x18697 0x1E240,0xC0A14 0x7FFFFFFF,2 0xF4240,0xF423F 0x24,0x3C 0x400,0x300)
RANDOM=$S
for i in $(seq 1 $N); do
  seq=""; for k in 1 2 3; do seq="$seq ${V[$((RANDOM % 16))]}"; done
  c=$(echo "0 0.5 1" | tr ' ' '\n' | sed -n "$((RANDOM % 3 + 1))p"); p=$(echo "0 0.5 1" | tr ' ' '\n' | sed -n "$((RANDOM % 3 + 1))p")
  sc=$(echo "0 0.1 0.2" | tr ' ' '\n' | sed -n "$((RANDOM % 3 + 1))p"); sd=$RANDOM; dout=$((500 + RANDOM % 3000))
  r=$(python3 "$HERE/sim.py" "$NET" "$BND" --pairs $seq --datachange broad --corner $c --pos $p --scatter $sc --seed $sd --dout $dout --tmax 400000000 2>&1 | grep RESULT)
  echo "run $i: pairs [$seq ] c=$c pos=$p scatter=$sc seed=$sd dout=$dout :: $r"
done
