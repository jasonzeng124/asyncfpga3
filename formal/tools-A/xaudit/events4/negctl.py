"""negctl.py -- negative controls for ana.py (UNTRUSTED): slow one own-feedback arc, and
shorten one delay-line tap, then rerun; the analysis must flag exactly those."""
import json, sys
src, out, which = sys.argv[1], sys.argv[2], sys.argv[3]
b = json.load(open(src))
if which == "fb":
    # ucontrol_merge4.uarb1.ua2: own feedback pin I0 (classify: q pin) +1500 ps
    k = "urig.udut.ucontrol_merge4.uarb1.ua2.u/I0"
    lo, hi = b["arcs"][k]
    b["arcs"][k] = [lo + 1500, hi + 1500]
    print(f"negctl fb: {k} {lo},{hi} -> {lo+1500},{hi+1500}")
json.dump(b, open(out, "w"))
