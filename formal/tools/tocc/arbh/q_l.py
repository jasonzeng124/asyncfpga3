import sys
c_ = sys.argv[1]; ARG2 = sys.argv[2]; sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/arbh/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
import json
an = open("/tmp/claude-0/arbh/r1an.py").read(); exec(an[an.index("ARBQ = {}"):an.index("roots = collections.defaultdict(list)")])
import json
idn = {x: i for i, x in enumerate(nm)}
def E_(s, k): return eid[(idn[s], k)]
for L in ARG2.split(","):
    Li = idn[L]; print("latch", L, "enable pins", [(nm[g[Li]["pins"][p]["src"]], v_, g[Li]["pins"][p]["win"][c]) for p, v_ in C["LATCH"][Li][1]])
    for p, v_ in C["LATCH"][Li][1]:
        u = g[Li]["pins"][p]["src"]
        print("   en", nm[u], [(k, t, valat(u, t)) for k, t in enumerate(ev[u])][:12])
    print("   D pins", [(nm[p_["src"]], p_["win"][c][2]) for j, p_ in enumerate(g[Li]["pins"]) if p_["live"] and p_["src"] != Li and j not in [p for p, v_ in C["LATCH"][Li][1]]])
    print("   flips of L after t0", [x for x in flips(Li) if x > t0][:12])
