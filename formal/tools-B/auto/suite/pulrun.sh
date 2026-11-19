#!/bin/bash
# tools-B/auto/suite/pulrun.sh (shard B, UNTRUSTED simulation): K SEED SIZES SDF8 OUT DRAWS... : rebuild, decode, pulses.py on udut.umux* LUT outputs for each draw
set -uo pipefail
K=$1; S=$2; Z=$3; M=$4; O=$5; shift 5; F=$(cd "$(dirname "$0")/../../.." && pwd); R=${RS:-/home/user/rs}
[ -f $O/w/m/net.json ] || RS=$R JOBS=4 bash $F/tools-B/auto/suite/task.sh $K $S $Z $M $O 1 > /dev/null 2>&1
head -1 $O/summary.txt
cd $O; V=kernels/$K/vec.hex; [ -f $R/$V ] || V=research/data/suite/vec/$K.hex; PAIRS=$(awk 'NF>=2{printf "0x%s,0x%s ", $1, $2}' $R/$V)
[ -x r/simx ] || python3 $F/tools-B/auto/xdraws.py exp.txt w/m/net.json w/m/bnd.json r --kernel $K --pairs $PAIRS --draws 1 --seed0 $1 --jobs 1 --routed w/m/routed.json > /dev/null 2>&1
ln -sf ../w/m/net.json r/net.json; ln -sf ../w/m/routed.json r/routed.json
for d in "$@"; do python3 $F/tools-B/auto/pulses.py r 'udut\.umux[0-9]+\.' exp.txt --kernel $K --pairs $PAIRS --seed $d | grep -v '^# flips' | head -6; done
