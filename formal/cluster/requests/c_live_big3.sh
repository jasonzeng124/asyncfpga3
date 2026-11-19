#!/bin/bash
#CLUSTER array=1-5 cores=2 mem=64G time=240
# Shard C: live.py (formal/tools/live/fixtures/) exhaustively on the rows sampled in the 2026-11-19 sweep (research 3c9e6de49; live.py models the load-first lowering since today),
# on research's bdc as of the request (PEER; token floor with pass-through modes). One search per task, one Python thread.
set -uo pipefail
FX=$PEER/cloud/fixtures/frontend
case $TASK in
  1) F=share_test_1; FLOW=def;  INV=1 ;;
  2) F=share_test_1; FLOW=auto; INV=1 ;;
  3) F=video_filter; FLOW=def;  INV=1 ;;
  4) F=video_filter; FLOW=auto; INV=1 ;;
  5) F=sobel;        FLOW=auto; INV=1 ;;
esac
unset $(env | grep -o '^BDC_[A-Z_]*')
[ "$FLOW" = auto ] && export BDC_AUTO=1
export LIVE_BDC_DIR=$PEER/bdc LIVE_MEM_GB=60 PYTHONDONTWRITEBYTECODE=1
(cd $PEER && git rev-parse HEAD) > "$OUT/peer.txt"
mkdir -p "$OUT/graphs"
/usr/bin/time -v timeout 13800 python3 formal/tools/live/fixtures/live.py "$FX/$F/comp/handshake_transformed.mlir" \
  --inv $INV --max-states 400000000 --json-dir "$OUT/graphs" --tag "$F.$FLOW.on.inv$INV" --out "$OUT/result.json" \
  > "$OUT/live.txt" 2> "$OUT/stderr.txt"
echo "rc=$?" >> "$OUT/live.txt"
exit 0
