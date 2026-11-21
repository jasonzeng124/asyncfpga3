#!/usr/bin/env bash
# formal/tools/margin/carryring/predict.sh BITDIR OUT/   (shard C, UNTRUSTED static loop sums)
#
# Formal's own prediction of research's BOARD-QUEUE item 36 (carry_ro_top: 64 rings, L8/L16, C1/C4/C16/C32 through
# chained CARRY4, F8/F16 through MUXF7 selects) from formal's decode of the bitstream's FASM:
#   1. tools-A decode_base.py (empty XDC) -> d0.json; build_net.py twice: default arcs and RC_TREE=1 (research's
#      prjxray Elmore tree, FOR-RESEARCH A18);
#   2. loops.py: per ring, the unique decoded cycle through the ring's NAND, its own LUT/CARRY4/MUXF sites and routing;
#      period = 2 x loop, P(x, y) = LO + x R + y CF (CARRY4/MUXF arcs at y, the rest at x); next to BITDIR/predicted.tsv
#      and research's walk of BITDIR/xray.sdf.xz (segment table: where the two differ, stage by stage);
#   3. summarize.py -> OUT/summary.txt. Intermediates (FASM, d0, nets, SDF; ~60 MB) are deleted at the end (KEEP=1 keeps).
# BITDIR: research/board/carry/s1 or s2 (carry_ro_top.fasm.xz, carry_ro_top_routed.json.xz, xray.sdf.xz, predicted.tsv).
# Env: TC (prjxray-db root, default ~/dev2/lib/fpgatoolchain), RSCH (research checkout, for carry_predict.py; default
# BITDIR/../../../..), KEEP.
set -euo pipefail
D=$(cd "$1" && pwd); mkdir -p "$2"; O=$(cd "$2" && pwd)
H=$(cd "$(dirname "$0")" && pwd); A=$(cd "$H/../../../tools-A/target" && pwd)
export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
[ -d "$TC/openxc7/share/nextpnr/prjxray-db/zynq7" ] || { echo "no prjxray-db under TC=$TC" >&2; exit 1; }
RSCH=${RSCH:-$(cd "$D/../../../.." && pwd)}
W=$O/work; mkdir -p "$W"
xz -dc "$D/carry_ro_top.fasm.xz" > "$W/fromBit.fasm"
xz -dc "$D/carry_ro_top_routed.json.xz" > "$W/routed.json"
xz -dc "$D/xray.sdf.xz" > "$W/xray.sdf"
: > "$W/empty.xdc"
python3 "$A/decode_base.py" "$W/fromBit.fasm" "$W/empty.xdc" --json "$W/d0.json" 2>&1 | tail -1 | tee "$O/decode.log"
python3 "$A/build_net.py" "$W/d0.json" "$W/fromBit.fasm" - "$W/net_default.json" 2>&1 | head -1 | tee -a "$O/decode.log"
RC_TREE=1 python3 "$A/build_net.py" "$W/d0.json" "$W/fromBit.fasm" - "$W/net_rctree.json" 2>&1 | head -1 | tee -a "$O/decode.log"
(cd "$W" && md5sum fromBit.fasm net_default.json net_rctree.json) >> "$O/decode.log"
for m in rctree default; do
  RSCH=$RSCH python3 "$H/loops.py" "$W/net_$m.json" "$W/routed.json" "$D/predicted.tsv" "$W/xray.sdf" \
    --seg "$O/seg_$m.tsv" > "$O/rings_$m.tsv"
done
python3 "$H/summarize.py" "$O" "$(basename "$D")"
[ "${KEEP:-0}" = 1 ] || rm -rf "$W"
