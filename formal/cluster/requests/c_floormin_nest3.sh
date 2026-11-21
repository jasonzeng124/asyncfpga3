#!/bin/bash
#CLUSTER array=1-2 cores=2 mem=64G time=240
# Shard C: is every stage research's token floor adds to nest3 necessary? (formal/tools/live/floormin/floormin.py, live.py
# exhaustive; research's bdc as of the request, PEER).  Task 1: default flow, task 2: BDC_AUTO.
set -uo pipefail
(cd $PEER && git rev-parse HEAD) > "$OUT/peer.txt"
export LIVE_RS=$PEER LIVE_MEM_GB=60 FLOORMIN_MAXS=400000000 FLOORMIN_TIMEOUT=6600
[ "$TASK" = 2 ] && export FLOORMIN_FLOWS=auto || export FLOORMIN_FLOWS=def
python3 formal/tools/live/floormin/floormin.py "$OUT/floormin.tsv" nest3 > "$OUT/log.txt" 2>&1
echo "rc=$?" >> "$OUT/log.txt"
exit 0
