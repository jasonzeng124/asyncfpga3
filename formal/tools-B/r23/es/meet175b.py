import sys, threading
sys.setrecursionlimit(400000); threading.stack_size(1024 * 1024 * 1024)
def main():
    c_ = sys.argv[1]; sys.argv = ["ao.py", c_, "0"]
    G = {"__name__": "x"}
    src = open("/tmp/claude-0/bsub1/tocc175/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
    exec(src, G)
    exec(open("/home/user/asyncfpga3/formal/tools/tocc/r1b/relup.py").read().split("# ---------------- emission")[0], G)
    G["CURD"][0] = G["RELD"]
    el, nm, alts, prev, et, tm, g, c, eid, ev = G["el"], G["nm"], G["alts"], G["prev"], G["et"], G["tm"], G["g"], G["c"], G["eid"], G["ev"]
    whi, wlo, sep23, up_get, RELD = G["whi"], G["wlo"], G["sep23"], G["up_get"], G["RELD"]
    idx = {n: i for i, n in enumerate(nm)}
    E = lambda e: "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
    def near(n, t): i = idx[n]; return min((eid[(i, k)] for k in range(len(ev[i]))), key=lambda e: abs(el[e][2] - t))
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
    def pin(v, u):
        for p in g[idx[v]]["pins"]:
            if p["src"] == idx[u] and p["live"]: return p["win"][c]
    T = {"0": (337109, 336012, 341168), "1": None}[c_] if c_ == "0" else tuple(int(x) for x in sys.argv[1:])
    bank = near("SLICE_X30Y76.A6", T[0]); selq = near("SLICE_X36Y69.A6", T[1] - 600); Cr = near("SLICE_X34Y76.A6", T[2])
    ca, cr = chain(bank), chain(Cr); sr = {e: i for i, e in enumerate(cr)}
    i_a = next(i for i, e in enumerate(ca) if e in sr); es = ca[i_a]; i_r = sr[es]
    hiA = psum(ca, i_a, whi); loR = psum(cr, i_r, wlo)
    tail = pin("SLICE_X31Y75.B6", "SLICE_X30Y76.A6")[1] + pin("SLICE_X33Y75.B6", "SLICE_X31Y75.B6")[1] + pin("SLICE_X34Y76.B6", "SLICE_X33Y75.B6")[1]
    elo = pin("SLICE_X34Y76.B6", "SLICE_X34Y76.A6")[0]
    print("c=%s bank reopen %s, select-latch event %s, Cr %s" % (c_, E(bank), E(selq), E(Cr)))
    print("  meet(bank, Cr) e* = %s; sum-hi e*->bank %d (relup Up %s), sum-lo e*->Cr %d (Sep23 %s); tail hi %d, elo %d" % (
        E(es), hiA, up_get(es, bank, RELD), loR, sep23(es, Cr), tail, elo))
    print("  PATH-SUM margin (data branch) = %d ; cert-with-relup margin = %s" % (loR + elo - hiA - tail,
          (sep23(es, Cr) + elo - up_get(es, bank, RELD) - tail) if up_get(es, bank, RELD) is not None and sep23(es, Cr) is not None else None))
    print("  run: tau(Cr) - tau(bank) = %d" % (el[Cr][2] - el[bank][2]))
th = threading.Thread(target=main); th.start(); th.join()
