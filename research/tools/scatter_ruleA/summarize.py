#!/usr/bin/env python3
"""summarize.py DIR [DIR...] -- per-draw rule-A minimum (guarded and raw) from mc.py's tighten logs."""
import sys, os, re, glob, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mc import parse

rows = []
for d in sys.argv[1:]:
    for log in glob.glob(os.path.join(d, "s*_d*_*/tighten.log")):
        m = re.search(r"s([\d.]+)_d(\d+)_(\w+)/", log)
        sc, dr, base = float(m.group(1)), int(m.group(2)), m.group(3)
        p = parse(log)
        if not p["A"]:
            continue
        A, R = sorted(p["A"]), sorted(p["Araw"])
        rows.append((base, sc, dr, A[0], sum(x < 0 for x, _ in A), R[0], sum(x < 0 for x, _ in R),
                     dict((c, x) for x, c in A).get("urig.udut.uori2")))
rows.sort()
short = lambda c: c.replace("urig.udut.", "")
print("base scale draw | A_min cell | #A<0 | Araw_min cell | #Araw<0 | uori2_A")
for b, sc, dr, a, na, r, nr, u in rows:
    print("%s %g %d | %d %s | %d | %d %s | %d | %s" % (b, sc, dr, a[0], short(a[1]), na, r[0], short(r[1]), nr, u))
agg = collections.defaultdict(list)
for b, sc, dr, a, na, r, nr, u in rows:
    agg[(b, sc)].append((a, na, r, nr))
print("\nSUMMARY")
for (b, sc), L in sorted(agg.items()):
    cells = collections.Counter(short(a[1]) for a, *_ in L)
    rcells = collections.Counter(short(r[1]) for _, _, r, _ in L if r[0] < 0)
    print("%s %gx n=%d: guarded any<0 %d/%d, raw any<0 %d/%d; A_min median %d range [%d,%d]; "
          "worst-cell counts %s; raw-negative worst cells %s"
          % (b, sc, len(L), sum(na > 0 for _, na, _, _ in L), len(L), sum(nr > 0 for *_, nr in L), len(L),
             sorted(a[0] for a, *_ in L)[len(L) // 2], min(a[0] for a, *_ in L), max(a[0] for a, *_ in L),
             dict(cells.most_common(5)), dict(rcells.most_common(5))))
