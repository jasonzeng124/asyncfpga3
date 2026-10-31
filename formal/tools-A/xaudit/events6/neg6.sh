#!/usr/bin/env bash
# Negative controls for xevents5 (seed d, slow), run after run6.sh:
#  NEG-fb    : +1500 ps on ucontrol_merge4.uarb1.ua2's own-feedback arc (events4/negctl.py); the
#              Lean checker must turn that stage's Back pins into residual items with margin <= 0.
#  NEG-recog : the certificate claims the feedback input of one stage is its reset input (qi := ri);
#              Recog6 must reject that node.
#  NEG-path  : one copy path of one delay line loses an element; Recog6 (chkT) must reject the node.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
O=${O:-/tmp/events6/out}; XE5=${XE5:-$HERE/xe5.sh}
export PYTHONHASHSEED=0
s=d
python3 "$HERE/../events4/negctl.py" $O/$s/skel_slow.bands.json $O/$s/skel_slow_NEGfb.bands.json fb
python3 "$HERE/cert6.py" $O/$s/skel.json $O/$s/skel_slow_NEGfb.bands.json $O/$s/cert_NEGfb.json > /dev/null
$XE5 $O/$s/skel.json $O/$s/skel_slow_NEGfb.bands.json $O/$s/cert_NEGfb.json > "$HERE/xe5_d_slow_NEGfb.txt" 2>&1
python3 - $O/$s/cert_slow.json $O/$s/cert_NEGrecog.json $O/$s/cert_NEGpath.json <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
n = next(x for x in c["nodes"] if not x["virt"] and not x["mg"])
n["qi"] = n["ri"]
print("NEG-recog:", n["name"])
json.dump(c, open(sys.argv[2], "w"))
c = json.load(open(sys.argv[1]))
for x in c["nodes"]:
    if x["virt"]:
        continue
    ps = [p for p in x["pins"] if p.get("paths") and len(p["paths"]) > 3]
    if ps:
        ps[0]["paths"][2] = ps[0]["paths"][2][:-2]
        print("NEG-path:", x["name"])
        break
json.dump(c, open(sys.argv[3], "w"))
PY
$XE5 $O/$s/skel.json $O/$s/skel_slow.bands.json $O/$s/cert_NEGrecog.json > "$HERE/xe5_d_slow_NEGrecog.txt" 2>&1
$XE5 $O/$s/skel.json $O/$s/skel_slow.bands.json $O/$s/cert_NEGpath.json > "$HERE/xe5_d_slow_NEGpath.txt" 2>&1
for f in NEGfb NEGrecog NEGpath; do echo "== $f"; grep -E "Recog6|RECOG-FAIL|VERDICT|ua2" "$HERE/xe5_d_slow_$f.txt" | head -8; done
