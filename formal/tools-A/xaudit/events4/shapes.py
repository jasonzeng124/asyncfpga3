import collections, sys
from netlib import Net
from classify import Skel, gate_fn

n = Net(sys.argv[1]); s = Skel(n)

def gname(cn, live):
    t = gate_fn(n, cn, live)
    k = len(live)
    if k == 1:
        return {(0, 1): "buf", (1, 0): "inv"}.get(t, f"f{t}")
    if k == 2:
        return {(0, 0, 0, 1): "and", (0, 1, 1, 1): "or"}.get(t, f"f{t}")
    return f"f{k}:{''.join(map(str, t))}"

def sig(e):
    if e[0] == "gate":
        return (gname(e[1], e[2]),) + tuple(sig(x) for x in e[3])
    if e[0] == "node":
        k = s.kind[e[1]]["kind"]
        return k
    return e[0]

c = collections.Counter(); ex = {}
for cn, m in s.kind.items():
    if m["kind"] != "cel":
        continue
    for i in m["reqs"]:
        e = s.expr(n.cells[cn]["ins"][i])
        g = sig(e)
        c[g] += 1; ex.setdefault(g, (cn, i))
for g, k in c.most_common():
    print(k, ex[g], g)
