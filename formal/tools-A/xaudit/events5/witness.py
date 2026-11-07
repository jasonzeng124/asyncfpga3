"""witness.py -- for the worst contig5 failure of an ana5 run, print the linetrace.py command that
reproduces it concretely (UNTRUSTED helper).  The slow side of the failing gate's best tap pair
gets SLOW_MAX, everything else FAST_MIN, and the source's low phase is set to W(src).
    python3 witness.py NET.json SKEL_NET.json BANDS(indep, full) SKEL_BANDS ANA5.json"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "events4"))
from ana5 import Contig5, stage_net, Model, Ana, live_pins  # noqa
net, skel, bands, sbands, anaj = sys.argv[1:6]
r = json.load(open(anaj))
worst = min((m for m in r["contig5"] if m.get("margin") is not None), key=lambda m: m["margin"])
M = Model(skel, sbands); A = Ana(M); C = Contig5(A)
n = M.n
g = worst["at"]
c = n.cells[g]
subs = [[p | {("arc", g, i)} for p in C.taps(c["ins"][i])[1]] for i in live_pins(n, g)]
best = min(((C.win(P, Q), P, Q) for P in subs[0] for Q in subs[1]), key=lambda t: t[0])
w, P, Q = best
lo = lambda S: sum(C.band(e)[0] for e in S); hi = lambda S: sum(C.band(e)[1] for e in S)
slow = P - Q if hi(P - Q) - lo(Q - P) >= hi(Q - P) - lo(P - Q) else Q - P
names = [f"{e[1]}/I{e[2]}" if e[0] == "arc" else e[1] for e in slow]
srcnet = n.cells[worst["src"]]["out"]
outnet = stage_net(M, worst["stage"], worst["pin"])
print(json.dumps(dict(stage=worst["stage"], margin=worst["margin"], window=w, W=worst["W"], gate=g,
                      src=srcnet, out=outnet, slow=names)))
