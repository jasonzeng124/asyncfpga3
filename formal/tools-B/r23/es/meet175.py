"""bsub1: (17,5) roots: true meeting events, path sums vs relup Up/Sep. usage: meet175.py c"""
import sys, threading, pickle, collections
sys.setrecursionlimit(400000); threading.stack_size(1024 * 1024 * 1024)
def main():
    c_ = sys.argv[1]; sys.argv = ["ao.py", c_, "0"]
    G = {"__name__": "x"}
    src = open("/tmp/claude-0/bsub1/tocc175/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
    exec(src, G)
    exec(open("/home/user/asyncfpga3/formal/tools/tocc/r1b/relup.py").read().split("# ---------------- emission")[0], G)
    G["CURD"][0] = G["RELD"]
    el, nm, alts, prev, et, tm, g, c = G["el"], G["nm"], G["alts"], G["prev"], G["et"], G["tm"], G["g"], G["c"]
    whi, wlo, sep23, sepAny, up_get, leqP, RELD = G["whi"], G["wlo"], G["sep23"], G["sepAny"], G["up_get"], G["leqP"], G["RELD"]
    E = lambda e: None if e is None else "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
    def chain(e, n=800):
        out = [e]
        for _ in range(n):
            cs = set(p for alt in alts[e] for p in alt)
            if prev[e] is not None: cs.add(prev[e])
            if not cs: break
            e = max(cs, key=lambda p: (et[p], tm[p])); out.append(e)
        return out
    def meet(evs):
        chs = [chain(e) for e in evs]; sets = [set(x) for x in chs[1:]]
        for e in chs[0]:
            if all(e in S for S in sets): return e, chs
        return None, chs
    def psum(ch, target, f):
        """sum of f along chain from target back to ... returns sum from target up to (but excluding) index of target"""
        i = ch.index(target); s = 0
        for k in range(i):
            child, par = ch[k], ch[k + 1]; v = el[child][0]
            s += f(v, v) if prev[child] == par else f(v, el[par][0])
        return s
    def pin(v, u):
        for p in g[v]["pins"]:
            if p["src"] == u and p["live"]: return p["win"][c]
    P = pickle.load(open("/tmp/claude-0/bsub1/tocc175/x4_c%s.pkl" % c_, "rb")); M = P["MEMO"]
    want = {"SLICE_X34Y76.B6": "H->U'", "SLICE_X36Y71.C6": "H->U'", "SLICE_X33Y91.B5": "U'->T"}
    seen = set()
    for tr in P["TRUNC"]:
        q = nm[tr["Q"]]
        if want.get(q) != tr["kind"]: continue
        c1, c2 = tr["c1"], tr["c2"]; k = (q, c1["B"], c2["A"])
        if k in seen: continue
        seen.add(k)
        print("=== %s %s  c1.B=%s b=%s  c2.A=%s a=%s  cert margin %s" % (q, tr["kind"], E(c1["B"]), c1["b"], E(c2["A"]), c2["a"], tr["margin"]))
        if tr["kind"] == "H->U'":
            Cr, elo = c1["B"], c1["b"]; covs = []
            for (u, key, B, b) in c2.get("pins", []):
                w = M.get(key)
                if w is None or w.get("A") is None: continue
                covs.append((nm[u], w["A"], w["a"], pin(tr["Q"], u)[1]))
            if not covs: print("   no anchored covers"); continue
            es, chs = meet([w for _, w, _, _ in covs] + [Cr])
            if es is None: print("   no meeting event"); continue
            sC = sep23(es, Cr); sCa = sepAny(es, Cr)[0]; loC = psum(chs[-1], es, wlo)
            print("   e* = %s ; Cr: Sep23 %s sepAny %s  sum-lo %d" % (E(es), sC, sCa, loC))
            worst_c = worst_p = None
            for (un, wA, wa, hq), ch in zip(covs, chs):
                u_ = up_get(es, wA, RELD); hi_ = psum(ch, es, whi)
                rc = (u_ + wa + hq) if u_ is not None else None; rp = hi_ + wa + hq
                print("   cover %s A=%s a=%d hi(Q pin)=%d : Up(e*->A)=%s sum-hi=%d -> need %s / %d" % (un, E(wA), wa, hq, u_, hi_, rc, rp))
                worst_c = rc if (rc is not None and (worst_c is None or rc > worst_c)) else (worst_c if rc is not None else 10**12)
                worst_p = rp if worst_p is None or rp > worst_p else worst_p
            print("   MARGIN cert (elo + Sep - max need) = %s ; PATH-SUM = %d" % (elo + max(sC or -10**12, sCa) - worst_c, elo + loC - worst_p))
        else:
            B1, b1, A2, a2 = c1["B"], c1["b"], c2["A"], c2["a"]
            print("   order: B1<=A2 %s A2<=B1 %s ; run gap %d" % (leqP(B1, A2), leqP(A2, B1), el[A2][2] - el[B1][2]))
            u_ = up_get(B1, A2, RELD) if tm[A2] >= tm[B1] else None
            if u_ is not None: print("   ChainUpOK: Up(B1->A2)=%d  margin b1-a2-Up = %d" % (u_, b1 - a2 - u_))
            es, chs = meet([B1, A2])
            if es is not None:
                s1 = sep23(es, B1); lo1 = psum(chs[0], es, wlo); u2 = up_get(es, A2, RELD); hi2 = psum(chs[1], es, whi)
                print("   e* = %s ; Sep(e*->B1) %s sum-lo %d ; Up(e*->A2) %s sum-hi %d" % (E(es), s1, lo1, u2, hi2))
                print("   JoinAnc margin cert = %s ; PATH-SUM = %d" % ((b1 + s1 - a2 - u2) if (s1 is not None and u2 is not None) else None, b1 + lo1 - a2 - hi2))
        sys.stdout.flush()
th = threading.Thread(target=main); th.start(); th.join()
