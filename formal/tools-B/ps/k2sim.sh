#!/usr/bin/env bash
# Shard B (UNTRUSTED): for each node named, kstar2's adversarial map (P_end fast, P_start and loop slow), then simb.py
# at several κ; reports the node's flip count vs baseline and the run's result. usage: k2sim.sh NET BND DUMP OUTDIR NODE...
set -u
NET=$1; BND=$2; DUMP=$3; OUT=$4; shift 4; HERE=$(cd "$(dirname "$0")" && pwd); TB=$HERE/../target; mkdir -p "$OUT"
for NODE in "$@"; do
  DUMPNODE=$NODE DUMPOUT=$OUT/pm_$NODE.json python3 -I "$HERE/kstar2.py" "$NET" "$DUMP" 0.5 1.0 > /dev/null
  gi=$(python3 -c "import json;print(json.load(open('$OUT/pm_$NODE.json.arcs.json'))['node'])")
  base=$(python3 -c "import json;print(len(json.load(open('$DUMP'))['nodes'].get('$gi',[0,[]])[1]))")
  line="$NODE (gate $gi) baseline flips $base:"
  for k in 0.0 0.2 0.4; do
    r=$(python3 -I "$TB/simb.py" "$NET" "$BND" --pairs 0xC,0x12 --corner 0.5 --kappa $k --datachange broad --tmax 3000000 --posmap "$OUT/pm_$NODE.json" --dump "$OUT/dx.json" 2>&1 | grep -o "RESULT [A-Z]*")
    f=$(python3 -c "import json;print(len(json.load(open('$OUT/dx.json'))['nodes'].get('$gi',[0,[]])[1]))")
    line="$line  κ=$k: $r flips $f"
  done
  echo "$line"
done
rm -f "$OUT/dx.json"
