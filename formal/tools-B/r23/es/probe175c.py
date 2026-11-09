import sys, threading, pickle
sys.setrecursionlimit(400000); threading.stack_size(1024 * 1024 * 1024)
def main():
    c_ = sys.argv[1]; sys.argv = ["ao.py", c_, "0"]
    G = {"__name__": "x"}
    src = open("/tmp/claude-0/bsub1/tocc175/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
    exec(src, G)
    exec(open("/home/user/asyncfpga3/formal/tools/tocc/r1b/relup.py").read().split("# ---------------- emission")[0], G)
    G["CURD"][0] = G["RELD"]
    el, nm, eid, up_get, leqP, sepAny, g, c = [G[k] for k in ("el","nm","eid","up_get","leqP","sepAny","g","c")]
    E = lambda e: "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
    def pin(v, u):
        for p in g[v]["pins"]:
            if p["src"] == u and p["live"]: return p["win"][c]
    P = pickle.load(open("/tmp/claude-0/bsub1/tocc175/es_c1.pkl", "rb"))
    for x in P["G"]:
        if len(x) != 7 or min(x[2], x[3]) >= 0: continue
        v, z, ms, me, cz, st, en_ = x; Ee = eid[en_]; B = cz["B"]; b = cz["b"]
        lz = pin(v, z)[0]; hE = G["hi_"](v, en_[0])
        u = up_get(B, Ee, G["RELD"]) if leqP(B, Ee) else None
        print("guard %s z %s E %s claim.B %s b %d : B<=E %s ; Up(B->E) %s ; GuardTime-with-Up margin (b + lo(v,z) - hi'(v,u) - Up) = %s ; run tau(E)-tau(B) %d" % (
            nm[v], nm[z], E(Ee), E(B), b, leqP(B, Ee), u, (b + lz - hE - u) if u is not None else None, el[Ee][2] - el[B][2]), flush=True)
th = threading.Thread(target=main); th.start(); th.join()
