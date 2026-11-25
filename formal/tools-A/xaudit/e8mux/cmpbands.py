#!/usr/bin/env python3
"""E8Mux: compare two band files key by key.  python3 -I cmpbands.py A.json B.json [--show N]
Prints the number of keys that differ, by section, and the largest |lo| / |hi| shift, with examples."""
import json, sys
a, b = json.load(open(sys.argv[1])), json.load(open(sys.argv[2]))
show = int(sys.argv[sys.argv.index("--show") + 1]) if "--show" in sys.argv else 5
for sec in ("cells", "arcs"):
    A, B = a.get(sec, {}), b.get(sec, {})
    ks = sorted(set(A) | set(B))
    diff = [(k, A.get(k), B.get(k)) for k in ks if A.get(k) != B.get(k)]
    print("%s: %d keys, %d only-A, %d only-B, %d differ" % (sec, len(ks), len(set(A) - set(B)),
          len(set(B) - set(A)), len(diff)))
    dd = [(B[k][0] - A[k][0], B[k][1] - A[k][1], k) for k, x, y in diff if x and y]
    if dd:
        print("  lo shift min/max %d/%d, hi shift min/max %d/%d" % (min(d[0] for d in dd), max(d[0] for d in dd),
              min(d[1] for d in dd), max(d[1] for d in dd)))
    for k, x, y in diff[:show]:
        print("  %s %s -> %s" % (k, x, y))
