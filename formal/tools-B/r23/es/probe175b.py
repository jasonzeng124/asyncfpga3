import sys, threading
sys.setrecursionlimit(400000); threading.stack_size(1024 * 1024 * 1024)
def main():
    c_ = sys.argv[1]; pairs = sys.argv[2:]; sys.argv = ["ao.py", c_, "0"]
    G = {"__name__": "x"}
    src = open("/tmp/claude-0/bsub1/tocc175/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
    exec(src, G)
    exec(open("/home/user/asyncfpga3/formal/tools/tocc/r1b/relup.py").read().split("# ---------------- emission")[0], G)
    G["CURD"][0] = G["RELD"]
    el, nm, eid, sepAny, sep23, up_get, leqP, alts, prev, et, tm, whi, wlo = [G[k] for k in ("el","nm","eid","sepAny","sep23","up_get","leqP","alts","prev","et","tm","whi","wlo")]
    idx = {n: i for i, n in enumerate(nm)}; E = lambda e: "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
    def chain(e, n=800):
        out = [e]
        for _ in range(n):
            cs = set(p for alt in alts[e] for p in alt)
            if prev[e] is not None: cs.add(prev[e])
            if not cs: break
            e = max(cs, key=lambda p: (et[p], tm[p])); out.append(e)
        return out
    def psum(ch, i, f):
        s = 0
        for k in range(i):
            child, par = ch[k], ch[k + 1]; v = el[child][0]
            s += f(v, v) if prev[child] == par else f(v, el[par][0])
        return s
    for pr in pairs:
        a, b = pr.split("/"); an, ak = a.split(":"); bn, bk = b.split(":")
        A = eid[(idx[an], int(ak))]; B = eid[(idx[bn], int(bk))]
        ca, cb = chain(A), chain(B); sb = {e: i for i, e in enumerate(cb)}
        ia = next((i for i, e in enumerate(ca) if e in sb), None)
        es = ca[ia]; ib = sb[es]
        print("%s -> %s : leqP %s ; sepAny %s ; meet %s ; sum-hi meet->E %d (Up %s) ; sum-lo meet->B %d (Sep23 %s) ; path margin Sep(E->B) >= %d ; run gap %d" % (
            E(A), E(B), leqP(A, B), sepAny(A, B)[0], E(es), psum(ca, ia, whi), up_get(es, A, G["RELD"]), psum(cb, ib, wlo), sep23(es, B),
            psum(cb, ib, wlo) - psum(ca, ia, whi), el[B][2] - el[A][2]), flush=True)
th = threading.Thread(target=main); th.start(); th.join()
