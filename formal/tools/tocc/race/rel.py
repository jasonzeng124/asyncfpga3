import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[n]: n for n in EX}
def E(n, k): return eid[(N[n], k)]
def s(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
evs = [E("SLICE_X22Y87.A6",0), E("SLICE_X27Y80.A6",2), E("SLICE_X24Y77.A6",1), E("SLICE_X24Y77.A6",2), E("SLICE_X22Y87.A6",1), E("SLICE_X24Y77.A6",3)]
for k in range(len(ev[N["SLICE_X26Y85.A6"]])): evs.append(E("SLICE_X26Y85.A6",k))
for a in evs:
    for b in evs:
        if a!=b and leqP(a,b): print("  ", s(a), "<=", s(b), "sep23", sep23(a,b))
for a in evs[:2]:
    for b in evs[2:]:
        if not leqP(a,b) and not leqP(b,a): print("  UNORDERED", s(a), s(b))
