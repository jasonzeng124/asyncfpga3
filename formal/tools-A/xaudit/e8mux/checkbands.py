#!/usr/bin/env python3
"""E8Mux: reject a band file (routed2x / skel.py output) with any lo > hi or negative entry.
    python3 -I checkbands.py BANDS.json ...      exit 1 on the first bad file (all bad keys listed)
The Lean reader Parse.toSteps maps lo > hi to [lo, lo] (a narrowing); this is run before every
xevents8 call of e8mux/run.sh so no such band reaches it."""
import json, sys
bad = 0
for p in sys.argv[1:]:
    j = json.load(open(p))
    n = 0
    for sec in ("cells", "arcs"):
        for k, v in j.get(sec, {}).items():
            n += 1
            if len(v) != 2 or v[0] < 0 or v[0] > v[1]:
                print("checkbands: BAD %s %s %s = %s" % (p, sec, k, v)); bad += 1
    for k in ("lut", "route", "feedback", "pad_steps"):
        v = j.get(k)
        if v is not None and (v[0] < 0 or v[0] > v[1]):
            print("checkbands: BAD %s %s = %s" % (p, k, v)); bad += 1
    print("checkbands: %s %d bands, %d bad" % (p, n, bad))
sys.exit(1 if bad else 0)
