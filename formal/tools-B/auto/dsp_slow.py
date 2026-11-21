#!/usr/bin/env python3
"""tools-B/auto/dsp_slow.py NET.json OUT.json [T]  (shard B): a simx classes file whose "I" list adds (T - 0.20) x (SLOW_MAX -
FAST_MIN) ps to every arc of every DSP48 gate (kinds dsp, dspcasc). Neither formal's nor research's draw model classes
the DSP: its arcs are drawn in the 'rest' band, U[0.20, 0.31]. With this injection on top, each DSP arc sits at least at
band T (default 1.0, i.e. SLOW_MAX; up to T + 0.11): the multiplier at its slow end, which no draw reaches."""
import json, sys
N = json.load(open(sys.argv[1])); T = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
I = []
for g in N["gates"]:
    if g["kind"] not in ("dsp", "dspcasc"): continue
    for i, a in enumerate(g["arcs"]):
        x = int(round((T - 0.20) * (a["smax"] - a["fmin"])))
        if x > 0: I.append([N["nodes"][g["out"]], i, x])
json.dump({"S": [], "F": [], "I": I}, open(sys.argv[2], "w"))
print("dsp_slow: %d DSP arcs, +%d..%d ps" % (len(I), min(x[2] for x in I), max(x[2] for x in I)), file=sys.stderr)
