#!/usr/bin/env bash
# route_check.sh TAG HWDIR DESIGN OUTDIR -- the RAM boundary of one memory route (research/data/suite/ifloop.md) at the
# sizing rule's two corners (chains 0.20; the rest 0.20 / 0.31; CARRY4 / F7F8 / FF / RAMB18 1.0; no scatter): every RAM x
# every request that reaches its clock (the bench's host request flops, the kernel's port slots) x pin class, from the
# decoded netlist's baked delays (ram_race_all.py), then the draws' within-die scatter Monte Carlo (race_mc.py, corner
# 0.31) on each (request, RAM) pair.  Writes OUTDIR/TAG.txt; work files in OUTDIR/bake/.  For a LOAD slot only ADDR
# toggles (the station drives wdata / we 0): its DI / WE rows are paths the logic cannot use.
set -uo pipefail
T=$1; HW=$(cd "$2" && pwd); D=$3; mkdir -p "$4"; O=$(cd "$4" && pwd); B=$O/bake; S=$(cd "$(dirname "$0")" && pwd)
echo "== $T $(md5sum < "$HW/$D.sdf" | cut -c1-8)" > "$O/$T.txt"
for c in 0.31 0.20; do
  if [ "$c" = 0.20 ] && [ -f "$B/${T}_c0.31/routed.json" ]; then
    mkdir -p "$B/${T}_c$c"; for f in xray.sdf routed.json routed.sdf; do cp "$B/${T}_c0.31/$f" "$B/${T}_c$c/"; done; fi
  "$S/decode_bake.sh" "$HW" "$D" "$B/${T}_c$c" 0.20 "$c" 1.0 || { echo "bake failed $c" >> "$O/$T.txt"; continue; }
  python3 -I "$S/ram_race_all.py" "$B/${T}_c$c" >> "$O/$T.txt"
done
grep "0.31 1.0 noscatter" "$O/$T.txt" | awk '{print $1, $2}' | sort -u | while read -r src ram; do
  python3 -I "$S/race_mc.py" "$B/${T}_c0.31" "$B/${T}_c0.31/routed.json" "$ram" "bridge_i.$src" 4000 2>&1 | grep -v "^$" >> "$O/$T.txt"
done
rm -f "$B/${T}_c0.20/routed.json" "$B/${T}_c"*/fid/*.tsv "$B/${T}_c"*/fid/fasm_routed.json
echo DONE >> "$O/$T.txt"
