# arbh2 (UNTRUSTED): (a) longest-lo (Sep) path close -> D-change cause for each latch close; (b) every event of D's two
# inputs between (close - 3 ns) and the next open, with its causal relation to the close; (c) adversary gate sets.
# usage: arbh2.py c
import sys, json
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[x]: x for x in range(len(nm))}
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
def E(n, k): return eid[(N[n], k)]
def spath(X, T):
    path = [T]; x = T
    while x != X:
        v = el[x][0]; best = None
        for alt in alts[x]:
            for p in alt:
                sp = sep23(X, p)
                if sp is not None and (best is None or sp + wlo(v, el[p][0]) > best[0]): best = (sp + wlo(v, el[p][0]), p)
        if prev[x] is not None and sep23(X, prev[x]) is not None:
            sp = sep23(X, prev[x]) + wlo(v, v)
            if best is None or sp > best[0]: best = (sp, prev[x])
        x = best[1]; path.append(x)
    return path[::-1]
def chainback(x, n=12):
    out = [x]
    for _ in range(n):
        v = el[x][0]; cands = set(p for alt in alts[x] for p in alt)
        if not cands: break
        p = max(cands, key=lambda p: et[p]); out.append(p); x = p
    return out
Dins = ["SLICE_X38Y51.A6", "SLICE_X38Y53.A6"]
CL = {1: [("SLICE_X36Y63.A6", 1), ("SLICE_X36Y68.A6", 1), ("SLICE_X36Y68.A6", 3), ("SLICE_X37Y47.A6", 1)]}
lo_nodes = set(); keyev = []
for en, kk in [("SLICE_X36Y63.A6", 1), ("SLICE_X36Y63.A6", 3), ("SLICE_X36Y68.A6", 1), ("SLICE_X36Y68.A6", 3), ("SLICE_X37Y47.A6", 1), ("SLICE_X37Y47.A6", 3)]:
    X = E(en, kk); tn = ev[N[en]][kk + 1]
    print("== close %s (next open @%d)" % (s_(X), tn))
    print("   close critical chain back: " + " <- ".join(s_(e) for e in chainback(X)))
    for w in Dins:
        for k2, t2 in enumerate(ev[N[w]]):
            if t2 < el[X][2] - 3000 or t2 > tn: continue
            y = eid[(N[w], k2)]
            print("   D input event %s: close<=it %s, it<=close %s, Sep(close->it) %s" % (s_(y), bool(leqP(X, y)), bool(leqP(y, X)), sep23(X, y)))
            if leqP(X, y):
                p = spath(X, y); keyev.append((X, y))
                print("      Sep path (%d hops): %s" % (len(p) - 1, " -> ".join(s_(e) for e in p)))
                de = VCP[:, enode[X]] > ek[X]; an = VCP[y][enode] > ek
                lo_nodes |= set(el[e][0] for e in np.nonzero(de & an)[0])
lo_nodes.add(N["SLICE_X39Y53.B6"])
json.dump(dict(loG=sorted(nm[n] for n in lo_nodes)), open("/tmp/claude-0/arbh/arbsets_c%s.json" % cc, "w"))
print("c=%s: gates on close->D-input paths: %d" % (cc, len(lo_nodes)))
