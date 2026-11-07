#!/usr/bin/env bash
# Negative controls for xevents7 (seed d, slow), run after run7.sh. Each must FAIL the check:
#  NEG-fb    : +1500 ps on ucontrol_merge4.uarb1.ua2's own-feedback arc (events4/negctl.py): that
#              stage's Back pin must become a residual item with margin <= 0 (timing).
#  NEG-u3    : one r3 line that a U-bound passes THROUGH (U3) gets two arms with the same label:
#              Events7.concl must reject it (runLog not accepted -> NOT RECOGNISED).
#  NEG-nary  : the select partition is dropped (parts = []): the 3-way merge's arms are no longer
#              exclusive (SelPart is load-bearing) -> its lines are rejected.
#  NEG-narx  : the 3-way merge's exclusivity certificate gives two arms the same pattern:
#              exclOK7 must fail -> a residual Excl item.
#  NEG-gline : a guarded delay-line pin (umux3.uxa z_ack) is declared an OR (FASTRISE) line instead
#              of AND: Recog6 (chkT of the guard pin's copies) must reject the node.
#  NEG-casc  : the cascade (control_merge12): the inner arbiter's R0 exclusivity certificate gives
#              both grants the same branch: exclOK7 must fail -> a residual Excl item.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
I=${I:-/tmp/events6/out}; O=${O:-/tmp/events7/out}; XE7=${XE7:-$HERE/xe7.sh}
export PYTHONHASHSEED=0
s=d
python3 "$HERE/../events4/negctl.py" $I/$s/skel_slow.bands.json $O/$s/skel_slow_NEGfb.bands.json fb
python3 "$HERE/cert7.py" $I/$s/skel.json $O/$s/skel_slow_NEGfb.bands.json $O/$s/cert_NEGfb.json > /dev/null
$XE7 $I/$s/skel.json $O/$s/skel_slow_NEGfb.bands.json $O/$s/cert_NEGfb.json > "$HERE/xe7_d_slow_NEGfb.txt" 2>&1
python3 - $O/$s/cert_slow.json $O/$s <<'PY'
import json, sys, copy
c0 = json.load(open(sys.argv[1])); O = sys.argv[2]
names = [n["name"] for n in c0["nodes"]]
# NEG-u3: an r3 line referenced as the walk of a uW line (U through a merge)
c = copy.deepcopy(c0)
r3s = [c["log"][l["w"]] for l in c["log"] if l["k"] == "uW" and c["log"][l["w"]]["k"] == "r3"]
ln = r3s[0]; ln["arms"][1]["g"], ln["arms"][1]["b"] = ln["arms"][0]["g"], ln["arms"][0]["b"]
print("NEG-u3: r3 line at", names[ln["x"]])
json.dump(c, open(O + "/cert_NEGu3.json", "w"))
# NEG-nary
c = copy.deepcopy(c0); print("NEG-nary: parts", c["parts"], "-> []"); c["parts"] = []
json.dump(c, open(O + "/cert_NEGnary.json", "w"))
# NEG-narx
c = copy.deepcopy(c0)
k = [k for k, e in c["excl"].items() if len(e["arms"]) == 3][0]
a = c["excl"][k]["arms"]; a[1]["g"], a[1]["b"] = a[0]["g"], a[0]["b"]
print("NEG-narx:", names[int(k)])
json.dump(c, open(O + "/cert_NEGnarx.json", "w"))
# NEG-gline
c = copy.deepcopy(c0)
n = [n for n in c["nodes"] if n["name"].endswith("umux3.uxa.u")][0]
p = [p for p in n["pins"] if p["pk"] == "guard" and p.get("ncopies", 1) > 1][0]
p["op"] = not p["op"]; print("NEG-gline:", n["name"], "guard pin op ->", p["op"])
json.dump(c, open(O + "/cert_NEGgline.json", "w"))
# NEG-casc
c = copy.deepcopy(c0)
k = [k for k, e in c["excl"].items() if names[int(k)].startswith("arb:") and "control_merge12.uarb1" in names[int(k)]][0]
a = c["excl"][k]["arms"]; a[1]["b"] = a[0]["b"]
print("NEG-casc:", names[int(k)], [(x["g"], x["b"], x["dir"]) for x in a])
json.dump(c, open(O + "/cert_NEGcasc.json", "w"))
PY
for f in NEGu3 NEGnary NEGnarx NEGgline NEGcasc; do
  $XE7 $I/$s/skel.json $I/$s/skel_slow.bands.json $O/$s/cert_$f.json > "$HERE/xe7_d_slow_$f.txt" 2>&1
done
for f in NEGfb NEGu3 NEGnary NEGnarx NEGgline NEGcasc; do
  echo "== $f"; grep -E "Recog6|RECOG-FAIL|runLog|RESIDUAL (Back|Excl|Line)|VERDICT" "$HERE/xe7_d_slow_$f.txt" | head -6
done
