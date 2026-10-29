#!/usr/bin/env python3
"""print events of nets in a window, and a cell's pins.  usage: probe.py WORK VCD T0 T1 net|cell ..."""
import sys
sys.argv = sys.argv[:5] + sys.argv[5:]
A = sys.argv[5:]; T0, T1 = int(sys.argv[3]), int(sys.argv[4])
sys.argv = sys.argv[:3] + ["n0", "0"]
exec(open(__file__.replace("probe.py", "xtrace.py")).read().split("n, t = NET, T")[0])
rn = {v: k for k, v in names.items()}
def show(n):
    e = [(t, v) for t, v in ev.get(n, []) if T0 <= t <= T1]
    print(f"  {n:8s} {netname.get(n, '')[:50]:50s} @T0={val(n, T0)} " + " ".join(f"{t}:{v}" for t, v in e[:30]))
for a in A:
    c = a if a in cells else rn.get(a)
    if c in cells:
        typ, pd, cd = cells[c]; print(f"{c} {names.get(c)} {typ} {pd}")
        for p, w in cd.items():
            src = icb.get(w, (w, 0)); print(f" pin {p}: {w} <- {src[0]} D={src[1]}"); show(w)
            if w != src[0]: show(src[0])
    else: show(a)
