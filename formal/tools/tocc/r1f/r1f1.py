# r1f1 (UNTRUSTED): latches X35Y91.B6, X34Y91.C5 (enable X34Y92.A6): for each enable close, D's value, D-input events
# from the open to the next open with relation to open/close, Sep, hold margin, flip kappa.  usage: r1f1.py c
import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1f/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[x]: x for x in range(len(nm))}
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
def chainback(x, stop, n=40):
    out = [x]
    for _ in range(n):
        if x == stop: break
        cands = set(p for alt in alts[x] for p in alt)
        if prev[x] is not None: cands.add(prev[x])
        cands = [p for p in cands if leqP(stop, p) or p == stop] or list(cands)
        if not cands: break
        p = max(cands, key=lambda p: et[p]); out.append(p); x = p
    return out
for qn in ("SLICE_X35Y91.B6", "SLICE_X34Y91.C5"):
    Q = N[qn]; fb, ens = C["LATCH"][Q]; pins = g[Q]["pins"]
    enp = [p for p, a in ens if pins[p]["src"] in EX and pins[p]["src"] in hist and len(ev[pins[p]["src"]])]
    print("== %s enables %s" % (qn, [(nm[pins[p]["src"]], a, pins[p]["win"][c]) for p, a in ens]))
    pe, act = [(p, a) for p, a in ens if nm[pins[p]["src"]] == "SLICE_X34Y92.A6"][0]
    e = pins[pe]["src"]; elo, ehi, emd = pins[pe]["win"][c]
    Dp = [i for i, p in enumerate(pins) if p["live"] and i not in fb and i not in [x for x, _ in ens]]
    print("   D pins:", [(nm[pins[i]["src"]], pins[i]["win"][c]) for i in Dp], " Q events", [x for x in hist.get(Q,(0,[]))[1] if x>t0][:10], "exact", Q in EX)
    print("   enable events", ev[e][:8], "init", int(s0[e]))
    for k, t in enumerate(ev[e][:4]):
        if valat(e, t) == bool(act): continue
        X = eid[(e, k)]; O = eid[(e, k - 1)] if k else None; tno = ev[e][k + 1] if k + 1 < len(ev[e]) else 10**12
        print("  close %s (open %s, next open @%d)" % (s_(X), s_(O) if O is not None else None, tno))
        for i in Dp:
            w = pins[i]["src"]; dlo, dhi, dmd = pins[i]["win"][c]
            if w not in ev: print("    D %s not exact" % nm[w]); continue
            for k2, t2 in enumerate(ev[w]):
                if O is not None and t2 + 3000 < el[O][2]: continue
                if t2 > tno: break
                y = eid[(w, k2)]
                sp = sep23(X, y); spo = sep23(O, y) if O is not None else None
                marg = (sp + dlo - ehi) if sp is not None else None
                f4 = form4(X, y) if (sp is None and not leqP(y, X)) else None
                print("    D %s: close<=y %s y<=close %s open<=y %s | Sep(close->y) %s Sep(open->y) %s form4 %s | hold margin %s kappa %s | read %+d after close read" % (
                    s_(y), bool(leqP(X, y)), bool(leqP(y, X)), bool(leqP(O, y)) if O is not None else None, sp, spo, f4, marg,
                    ("%.3f" % ((sp + dlo - ehi) / (sp + dlo + ehi))) if sp is not None else None, t2 + dmd - (t + emd)))
                if O is not None and leqP(O, y) and not leqP(X, y):
                    print("       chain back to open:", " <- ".join(s_(z) for z in chainback(y, O)))
