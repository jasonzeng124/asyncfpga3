#!/bin/bash
#CLUSTER array=1-4 cores=2 mem=64G time=240
# Shard C: live.py (formal/tools/live/fixtures/, now modelling bdc's load-first lowering) on sobel and spmv, the two
# memory kernels research saw deadlock in the default flow in RTL (fixed, research says, by the token floor). Floor on
# and BDC_TOKEN_FLOOR=0, default flow, one invocation; research's bdc as of the request (PEER).
set -uo pipefail
FX=$PEER/cloud/fixtures/frontend
case $TASK in
  1) F=sobel; FL=on ;;
  2) F=sobel; FL=off ;;
  3) F=spmv;  FL=on ;;
  4) F=spmv;  FL=off ;;
esac
unset $(env | grep -o '^BDC_[A-Z_]*')
[ "$FL" = off ] && export BDC_TOKEN_FLOOR=0
export LIVE_BDC_DIR=$PEER/bdc LIVE_MEM_GB=60 PYTHONDONTWRITEBYTECODE=1
(cd $PEER && git rev-parse HEAD) > "$OUT/peer.txt"
mkdir -p "$OUT/graphs"
/usr/bin/time -v timeout 13800 python3 formal/tools/live/fixtures/live.py "$FX/$F/comp/handshake_transformed.mlir" \
  --inv 1 --max-states 400000000 --json-dir "$OUT/graphs" --tag "$F.def.$FL.inv1" --out "$OUT/result.json" \
  > "$OUT/live.txt" 2> "$OUT/stderr.txt"
echo "rc=$?" >> "$OUT/live.txt"
exit 0
