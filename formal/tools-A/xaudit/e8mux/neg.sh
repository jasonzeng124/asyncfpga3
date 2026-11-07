#!/usr/bin/env bash
# E8Mux negative controls (each must be REJECTED / fail as stated), on the NEW bands:
#  NEGmux    : seed d gb, the ONE arc ugrant$LUT5 -> ucontrol_merge3.uarb1.ua1.u (the O5 guard arc whose
#              OUTMUX hop is the finding) set back to its OLD (99b10a6d) band -> merge3.uarb1.ua1 pin0
#              must fail ENTRY again (all other arcs new)
#  NEGentry, NEGexit, NEGlabel, NEGnoguard : events8/neg8.sh's four, on seed d slow NEW bands
#  NEGinv    : a band file with one arc lo > hi -> run.sh's checkbands must refuse it (no xevents8 run)
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; X="$HERE/.."
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/e8mux}; W=${W:-$S/w}
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
o=$W/d/new; R="$HERE/results"; mkdir -p $R
python3 - $o $W/d/old <<'PY'
import json, sys
o, old = sys.argv[1], sys.argv[2]
b = json.load(open(f"{o}/skel_gb.bands.json")); ob = json.load(open(f"{old}/skel_gb.bands.json"))
net = json.load(open(f"{o}/skel.json")); m = next(iter(net["modules"].values()))
cn = "urig.udut.ucontrol_merge3.uarb1.ua1.u"
drv = {bb: c for c, x in m["cells"].items() for bb in x["connections"].get("O", [])}
ks = [f"{cn}/{p}" for p, bs in m["cells"][cn]["connections"].items() if p != "O" and "ugrant$LUT5" in drv.get(bs[0], "")]
assert len(ks) == 1, ks
k = ks[0]
print(f"NEGmux: {k} new {b['arcs'][k]} -> old {ob['arcs'][k]}")
b["arcs"][k] = ob["arcs"][k]
json.dump(b, open(f"{o}/skel_gb_NEGmux.bands.json", "w"))
for tag, k, dlo, dhi in (("NEGentry", "urig.udut.umux3.uxa.u/I0", 5000, 5000),
                         ("NEGexit", "urig.udut.umux3.uxa.u/I2", 0, 18000)):
    b = json.load(open(f"{o}/skel_slow.bands.json"))
    lo, hi = b["arcs"][k]; b["arcs"][k] = [lo + dlo, hi + dhi]
    print(f"{tag}: {k} {lo},{hi} -> {lo+dlo},{hi+dhi}")
    json.dump(b, open(f"{o}/skel_slow_{tag}.bands.json", "w"))
b = json.load(open(f"{o}/skel_slow.bands.json"))
k = sorted(b["arcs"])[0]; lo, hi = b["arcs"][k]; b["arcs"][k] = [hi + 1, hi]
print(f"NEGinv: {k} -> {b['arcs'][k]}")
json.dump(b, open(f"{o}/skel_slow_NEGinv.bands.json", "w"))
PY
ROWS="d:new:gb" BANDS=$o/skel_gb_NEGmux.bands.json TAG=_NEGmux "$HERE/run.sh"
for t in NEGentry NEGexit; do ROWS="d:new:slow" BANDS=$o/skel_slow_$t.bands.json TAG=_$t "$HERE/run.sh"; done
ROWS="d:new:slow" FLAGS=--no-guard TAG=_NEGnoguard "$HERE/run.sh"
python3 - $o/cert_slow.json $o/cert_slow_NEGlabel.json <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
j = next(i for i, n in enumerate(c["nodes"]) if n["name"] == "urig.udut.umux3.uxa.u")
g = c["guards"][f"{j}/0"]; print(f"NEGlabel: guard {j}/0 iU {g['iU']} -> {g['iW']}"); g["iU"] = g["iW"]
json.dump(c, open(sys.argv[2], "w"))
PY
"$HERE/xe.sh" $o/skel.json $o/skel_slow.bands.json $o/cert_slow_NEGlabel.json 2>&1 | grep -v '^\[slot\]' > $R/xe_d_new_slow_NEGlabel.txt
ROWS="d:new:slow" BANDS=$o/skel_slow_NEGinv.bands.json TAG=_NEGinv "$HERE/run.sh" 2>&1 | head -1
for t in gb_NEGmux slow_NEGentry slow_NEGexit slow_NEGlabel slow_NEGnoguard; do f=$R/xe_d_new_$t.txt
  echo "$t: $(grep -c 'RESIDUAL Guard' $f) guard residual | $(grep 'RESIDUAL Guard' $f | head -2 | cut -c1-150 | tr '\n' ';') | $(tail -1 $f | cut -c1-40)"; done
