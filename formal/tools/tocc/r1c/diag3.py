import sys, os, threading
sys.argv = ["ao.py", "1", "0"]
src = open("/tmp/claude-0/r1c/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
os.environ["RELD"] = "99"
exec(open("/tmp/claude-0/r1c/relup.py").read())
sys.setrecursionlimit(100000); threading.stack_size(512 * 1024 * 1024)
r = {nm[n]: n for n in EX}
def ev_(s): n, k = s.rsplit("(", 1); return eid[(r[n], int(k[:-1]))]
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
E = ev_("SLICE_X39Y47.D6(1)"); e0 = ev_("SLICE_X27Y80.A6(2)"); B = ev_("SLICE_X30Y76.A6(2)")
def main():
    u = up_get(e0, E, 99); print("Up(e0->E)", u, "Sep23(e0->B)", sep23(e0, B), "tm e0<E", tm[e0] < tm[E])
    st = UPST[(e0, 99)]; U = st["U"]
    v = el[E][0]; print("E node in g", v in g, "env", v in envnode, "alts", [[s_(p) for p in a] for a in alts[E]], "prev", s_(prev[E]))
    for a in alts[E]:
        for p in a: print("  cause", s_(p), _term(p, e0, 99, U, whi(v, el[p][0])), "inU", p in U)
    print("  prev", _term(prev[E], e0, 99, U, whi(v, v)))
    print("form4 depth99", form4(E, B, None, 99))
    m = np.minimum(VCP[B], VCP[E]); cands = []
    for x in np.nonzero(m)[0]:
        e0_ = eid[(xs[x], int(m[x]) - 1)]
        if tm[e0_] < tm[E]: cands.append((tm[e0_], e0_))
    cands.sort(reverse=True)
    for _, c_ in cands[:0]: print("   cand", s_(c_), "sep23", sep23(c_, B), "up", up_get(c_, E, 99))
th = threading.Thread(target=main); th.start(); th.join()
def main2():
    U = UPST[(e0, 99)]["U"]; J = UPST[(e0, 99)]["J"]
    x = E
    while x != e0:
        v = el[x][0]; j = J[x]; _, ai, tags, ptag = j
        items = list(zip(alts[x][ai], tags)) + ([(prev[x], ptag)] if ptag else [])
        best = None
        for p, tg in items:
            h = whi(v, v) if p == prev[x] else whi(v, el[p][0])
            if tg[0] == "U": val = U[p] + h
            elif tg[0] == "S": val = h
            else:
                a = tg[1]; val = UPST[(a, 99)]["U"][p] - sep23(a, e0) + h
            if best is None or val > best[0]: best = (val, p, tg, h)
        val, p, tg, h = best
        mid = mid_(v, el[p][0]) if p != prev[x] else None
        print("%-32s U=%6d act=%6d | via %-30s %s hi=%d mid=%s" % (s_(x), U[x], el[x][2] - el[e0][2], s_(p), tg[0] if tg[0] != "R" else "R a=" + s_(tg[1]), h, mid))
        if tg[0] != "U": 
            if tg[0] == "R":
                a = tg[1]; print("    R: Up(a->p)=%d Sep23(a->e0)=%d act(p-a)=%d act(e0-a)=%d" % (UPST[(a, 99)]["U"][p], sep23(a, e0), el[p][2]-el[a][2], el[e0][2]-el[a][2]))
            break
        x = p
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
#th = threading.Thread(target=main2); th.start(); th.join()
def trace(e0_, x, depth_lim=6, ind=""):
    U = UPST[(e0_, 99)]["U"]; J = UPST[(e0_, 99)]["J"]
    print(ind + "== table e0=%s target %s U=%d act=%d" % (s_(e0_), s_(x), U[x], el[x][2] - el[e0_][2]))
    n = 0
    while x != e0_ and n < 60:
        n += 1
        v = el[x][0]; _, ai, tags, ptag = J[x]
        items = list(zip(alts[x][ai], tags)) + ([(prev[x], ptag)] if ptag else [])
        best = None
        for p, tg in items:
            h = whi(v, v) if p == prev[x] else whi(v, el[p][0])
            if tg[0] == "U": val = U[p] + h
            elif tg[0] == "S": val = h
            else: val = UPST[(tg[1], 99)]["U"][p] - sep23(tg[1], e0_) + h
            if best is None or val > best[0]: best = (val, p, tg)
        val, p, tg = best
        print(ind + "%-30s U=%6d act=%6d via %s %s%s" % (s_(x), U[x], el[x][2] - el[e0_][2], s_(p), tg[0], "" if p != prev[x] else " (prev)"))
        if tg[0] == "R":
            a = tg[1]; print(ind + "   R a=%s Up(a->p)=%d Sep23(a->e0)=%d act(p-a)=%d act(e0-a)=%d" % (s_(a), UPST[(a, 99)]["U"][p], sep23(a, e0_), el[p][2]-el[a][2], el[e0_][2]-el[a][2]))
            if depth_lim > 0: trace(a, p, depth_lim - 1, ind + "  ")
            return
        if tg[0] == "S": return
        x = p
th = threading.Thread(target=lambda: trace(ev_("SLICE_X36Y69.A6(2)"), ev_("SLICE_X37Y55.C6(2)"))); th.start(); th.join()
