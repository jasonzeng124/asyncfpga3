#!/usr/bin/env bash
# WE4g negative controls on seed d slow (each must be REJECTED: the mutated guarded pin residual).
#  NEGentry : +5000 ps on both bounds of urig.udut.umux3.uxa.u/I0 (the guarded delay line's LUT
#             input, on both copies): every copy arrives later -> ENTRY must fail for umux3.uxa pin0
#  NEGexit  : +18000 ps on the upper bound of urig.udut.umux3.uxa.u/I2 (the guard pin): the guard
#             may arrive late -> EXIT2 must fail for umux3.uxa pin0
#  NEGlabel : certificate edit: umux3.uxa pin0's ENTRY U-bound replaced by its S->D walk line
#             (a judgement of the wrong kind) -> guardOK8 must reject that pin
#  NEGnoguard: cert8.py --no-guard (no guard certificates) -> all 63 guarded pins residual
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
I=${I:-/tmp/events6/out}; O=${O:-/tmp/events8/out}; s=d; c=slow
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
mkdir -p $O/$s
python3 - $I/$s/skel_$c.bands.json $O/$s <<'PY'
import json, sys
src, od = sys.argv[1], sys.argv[2]
for tag, k, dlo, dhi in (("NEGentry", "urig.udut.umux3.uxa.u/I0", 5000, 5000),
                         ("NEGexit", "urig.udut.umux3.uxa.u/I2", 0, 18000)):
    b = json.load(open(src))
    lo, hi = b["arcs"][k]
    b["arcs"][k] = [lo + dlo, hi + dhi]
    print(f"{tag}: {k} {lo},{hi} -> {lo+dlo},{hi+dhi}")
    json.dump(b, open(f"{od}/skel_slow_{tag}.bands.json", "w"))
PY
one() { "$HERE/xe8.sh" "$1" "$2" "$3" 2>&1 | grep -v '^\[slot\]' > "$4"; }
for t in NEGentry NEGexit; do
  python3 "$HERE/cert8.py" $I/$s/skel.json $O/$s/skel_slow_$t.bands.json $O/$s/cert_$t.json > /dev/null
done
python3 "$HERE/cert8.py" $I/$s/skel.json $I/$s/skel_slow.bands.json $O/$s/cert_NEGnoguard.json --no-guard > /dev/null
python3 - $O/$s/cert_slow.json $O/$s/cert_NEGlabel.json <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
j = next(i for i, n in enumerate(c["nodes"]) if n["name"] == "urig.udut.umux3.uxa.u")
g = c["guards"][f"{j}/0"]
print(f"NEGlabel: guard {j}/0 iU {g['iU']} -> {g['iW']}")
g["iU"] = g["iW"]
json.dump(c, open(sys.argv[2], "w"))
PY
one $I/$s/skel.json $O/$s/skel_slow_NEGentry.bands.json $O/$s/cert_NEGentry.json "$HERE/xe8_d_slow_NEGentry.txt" &
one $I/$s/skel.json $O/$s/skel_slow_NEGexit.bands.json $O/$s/cert_NEGexit.json "$HERE/xe8_d_slow_NEGexit.txt"
wait
one $I/$s/skel.json $I/$s/skel_slow.bands.json $O/$s/cert_NEGlabel.json "$HERE/xe8_d_slow_NEGlabel.txt" &
one $I/$s/skel.json $I/$s/skel_slow.bands.json $O/$s/cert_NEGnoguard.json "$HERE/xe8_d_slow_NEGnoguard.txt"
wait
for t in NEGentry NEGexit NEGlabel NEGnoguard; do
  f="$HERE/xe8_d_slow_$t.txt"
  echo "$t: $(grep -c 'RESIDUAL Guard' $f) guard residual | $(grep 'RESIDUAL Guard' $f | head -2 | cut -c1-150 | tr '\n' ';') | $(tail -1 $f | cut -c1-40)"
done
