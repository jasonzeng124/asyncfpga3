#!/usr/bin/env bash
# Shard B (UNTRUSTED): H_RUNT(w) sweep on gcd_ps's binding race (A's hrunt_sweep setup: simb.py --gfilter W,0 = every
# pin whose window start and delay are >= W skips input pulses narrower than W from t = 0), vector (12,18), the node's
# kadv per-pin adversary at corner C; bisect the smallest κ at which the run is not clean (node flips more than its
# baseline, or the result is wrong). usage: hrunt.sh NET BND POSMAP NODE C W...
set -u
NET=$1; BND=$2; PM=$3; NODE=$4; C=$5; shift 5; HERE=$(cd "$(dirname "$0")" && pwd); TB=$HERE/../target
T=$(mktemp -d)
flips() { python3 -I -c "
import json,sys;D=json.load(open(sys.argv[1]))['nodes'];N=json.load(open(sys.argv[2]));i=[k for k,g in enumerate(N['gates']) if g['name']==sys.argv[3]][0];print(len(D.get(str(i),[0,[]])[1]))" "$@"; }
python3 -I "$TB/simb.py" "$NET" "$BND" --pairs 0xC,0x12 --corner "$C" --tmax 3000000 --dump "$T/b.json" > /dev/null 2>&1
base=$(flips "$T/b.json" "$NET" "$NODE")
for W in "$@"; do
  bad() { local extra=""; [ "$W" != 0 ] && extra="--gfilter $W,0"
    ok=$(python3 -I "$TB/simb.py" "$NET" "$BND" --pairs 0xC,0x12 --corner "$C" --kappa "$1" --tmax 3000000 --posmap "$PM" $extra --dump "$T/t.json" 2>&1 | grep -c "RESULT OK")
    f=$(flips "$T/t.json" "$NET" "$NODE"); [ "$ok" = 0 ] || [ "$f" -gt "$((base + 2))" ]; }
  lo=0.3; hi=0.6
  if bad $hi; then
    for _ in 1 2 3 4 5 6; do mid=$(python3 -c "print(round(($lo+$hi)/2,5))"); if bad $mid; then hi=$mid; else lo=$mid; fi; done
    echo "corner $C w = $W: clean at κ = $lo, not clean at κ = $hi"
  else echo "corner $C w = $W: clean up to κ = $hi"; fi
done
rm -rf "$T"
