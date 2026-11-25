import sys
sys.argv = ["ao.py", "0", "0"]
src = open("/tmp/claude-0/r1c/ao.py").read()
src = src[:src.index("# ---------------- rounds")]
exec(src)
idn = {n: i for i, n in enumerate(nm)}
v = idn["SLICE_X0Y16.A6"]; b = idn["SLICE_X4Y43.A6"]
for k in range(len(ev[v])):
    e = eid[(v, k)]
    print("event", k, el[e][2], "tm", tm[e], "alts", [[(nm[el[p][0]], el[p][1], el[p][2]) for p in a] for a in alts[e]])
print("b events", ev[b], [ (tm[eid[(b,i)]]) for i in range(len(ev[b]))])
e = eid[(v, 1)]
print("VC[(v,1)][b] =", VCP[e, xi[b]], "sep23 b1->v1", sep23(eid[(b, 1)], e), "sep b0->v1", sep23(eid[(b,0)], e))
for p in alts[e][0]:
    print(" cause", nm[el[p][0]], el[p][1], "VC b", VCP[p, xi[b]], "sep b1->p", sep23(eid[(b,1)], p))
def trace(e, depth=0):
    if depth > 6: return
    b1 = eid[(b, 1)]
    print("  " * depth, nm[el[e][0]], el[e][1], "VCb", VCP[e, xi[b]], "sep", sep23(b1, e), "prev", prev[e] is not None and VCP[prev[e], xi[b]])
    for a in alts[e]:
        print("  " * depth, " alt:", [(nm[el[p][0]], el[p][1], int(VCP[p, xi[b]])) for p in a])
    for a in alts[e]:
        for p in a:
            if VCP[p, xi[b]] >= 2 and p != b1: trace(p, depth + 1); return
trace(eid[(idn["SLICE_X1Y19.D6"], 1)])
