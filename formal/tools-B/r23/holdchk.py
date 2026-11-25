#!/usr/bin/env python3
"""bsub1 (UNTRUSTED): for listed latches in a simx.py run, every change of Q classified by the enable value AS READ
by Q at that moment (open/closed); a change while closed = the latch value changed during its hold. Also every
D change (as read) while closed, and the gcd result.  usage: holdchk.py RUN.pkl LATCH..."""
import sys, pickle, math
from bisect import bisect_right
sys.path.insert(0, "/tmp/claude-0/bsub1/tocc")
from classify import load
C = load(); g = C["gates"]; nm = C["names"]; idx = {n: i for i, n in enumerate(nm)}
H = pickle.load(open(sys.argv[1], "rb")); hist = H["hist"]; DS = H["DS"]; R = H["R"]
def val(n, t):
    if n not in hist: return False
    b, ts = hist[n]; return b ^ (bisect_right(ts, t) % 2 == 1)
print("%s: pair (%d,%d) c=%d out %s want %d" % (sys.argv[1].split("/")[-1], H["A"], H["B"], H["c"], H["res"], math.gcd(H["A"], H["B"])))
for L in sys.argv[2:]:
    q = idx[L]; fb, en = C["LATCH"][q]; pe, act = [x for x in en if g[q]["pins"][x[0]]["src"] in C["EXACT"]][0]
    e = g[q]["pins"][pe]["src"]; de = DS[q][pe]
    Dp = [j for j, p in enumerate(g[q]["pins"]) if p["live"] and j not in fb and j != pe and p["src"] not in C["const"]]
    qf = [t for t in hist.get(q, (0, []))[1] if t >= R]
    closed = [t for t in qf if val(e, t - de) != bool(act) and val(e, t - 1 - de) != bool(act)]
    dch = 0
    for j in Dp:
        u = g[q]["pins"][j]["src"]; dd = DS[q][j]
        for t in hist.get(u, (0, []))[1]:
            tt = t + dd
            if tt >= R and val(e, tt - de) != bool(act): dch += 1
    print("  %s en=%s(pin %d, delay %d) Q changes after reset %d, while closed %d %s; D changes read while closed %d" % (
        L, nm[e], pe, de, len(qf), len(closed), closed[:4], dch))
