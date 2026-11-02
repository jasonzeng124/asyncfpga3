#!/usr/bin/env bash
# Shard B (UNTRUSTED): per corner, gcd_ps vector (12,18): baseline dump, kstar top nodes, then kadv's adversarial map for
# NODE and a bisection of the smallest κ at which NODE flips more than in the baseline (a runt), with simb.py (current Adm).
# usage: kcorner.sh NET BND OUTDIR NODE CORNER...
set -u
NET=$1; BND=$2; OUT=$3; NODE=$4; shift 4
HERE=$(cd "$(dirname "$0")" && pwd); TB=$HERE/../target; mkdir -p "$OUT"
flips() { python3 -I -c "
import json,sys;D=json.load(open(sys.argv[1]))['nodes'];N=json.load(open(sys.argv[2]));i=[k for k,g in enumerate(N['gates']) if g['name']==sys.argv[3]][0];print(len(D.get(str(i),[0,[]])[1]))" "$@"; }
for C in "$@"; do
  python3 -I "$TB/simb.py" "$NET" "$BND" --pairs 0xC,0x12 --corner "$C" --tmax 3000000 --dump "$OUT/b$C.json" > /dev/null 2>&1
  python3 -I "$TB/kstar.py" "$NET" "$OUT/b$C.json" "$C" 1.0 | sed -n 2,4p > "$OUT/kstar$C.txt"
  python3 -I "$HERE/kadv.py" "$NET" "$OUT/b$C.json" "$C" 1.0 "$NODE" "$OUT/pm$C.json" > "$OUT/kadv$C.txt"
  base=$(flips "$OUT/b$C.json" "$NET" "$NODE")
  lo=0.0; hi=0.8
  run() { python3 -I "$TB/simb.py" "$NET" "$BND" --pairs 0xC,0x12 --corner "$C" --kappa "$1" --tmax 3000000 --posmap "$OUT/pm$C.json" --dump "$OUT/t$C.json" 2>&1 | grep -c "RESULT OK" > "$OUT/ok$C.txt"; [ "$(flips "$OUT/t$C.json" "$NET" "$NODE")" -gt "$((base + 2))" ]; }
  if run $hi; then
    for _ in 1 2 3 4 5 6 7; do mid=$(python3 -c "print(round(($lo+$hi)/2,5))"); if run $mid; then hi=$mid; else lo=$mid; fi; done
    echo "corner $C: baseline flips $base; clean at κ = $lo, runt at κ = $hi; $(cat "$OUT/kadv$C.txt" | sed -n 2p)"
  else echo "corner $C: no runt up to κ = $hi; $(sed -n 2p "$OUT/kadv$C.txt")"; fi
  echo "  kstar top: $(tr -s ' ' < "$OUT/kstar$C.txt" | cut -c1-60 | tr '\n' '|')"
  rm -f "$OUT/b$C.json" "$OUT/t$C.json"
done
