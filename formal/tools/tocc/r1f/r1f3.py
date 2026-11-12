import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1f/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[x]: x for x in range(len(nm))}
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
def E(n, k): return eid[(N[n], k)]
O = E("SLICE_X34Y92.A6", 0); X = E("SLICE_X34Y92.A6", 1)
print("Sep(open->close)", sep23(O, X))
for k in range(len(ev[N["SLICE_X34Y76.A6"]])):
    y = E("SLICE_X34Y76.A6", k)
    print(s_(y), "close<=y", bool(leqP(X, y)), "y<=close", bool(leqP(y, X)), "Sep(close->y)", sep23(X, y), "Sep(open->y)", sep23(O, y), "Sep(y->open)", sep23(y, O))
# close's cause chain
x = X; out = [x]
for _ in range(30):
    cs = set(p for a in alts[x] for p in a)
    if not cs: break
    x = max(cs, key=lambda p: et[p]); out.append(x)
print("close critical chain:", " <- ".join(s_(z) for z in out))
