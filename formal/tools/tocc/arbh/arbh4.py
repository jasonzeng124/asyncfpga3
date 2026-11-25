# arbh4 (UNTRUSTED): the join X37Y55.C6 and the OR hand-over X38Y53.A6 rise -> X38Y51.A6 fall at D = X39Y53.B6
import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[x]: x for x in range(len(nm))}
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
def E(n, k): return eid[(N[n], k)]
def pw(v, w):
    for p in g[N[v]]["pins"]:
        if p["live"] and nm[p["src"]] == w: return p["win"][c]
for k in (1, 3):
    J = E("SLICE_X37Y55.C6", k)
    print("c=%s J=%s alts %s" % (cc, s_(J), [[s_(p) for p in a] for a in alts[J]]))
    for en in ("SLICE_X36Y63.A6", "SLICE_X36Y68.A6", "SLICE_X37Y47.A6", "SLICE_X36Y69.A6"):
        X = E(en, k); print("    Sep(%s -> J) %s" % (s_(X), sep23(X, J)))
    for tgt in (("SLICE_X38Y51.A6", 0) if k == 1 else ("SLICE_X38Y53.A6", 1),):
        T = E(*tgt); print("    Sep(J -> %s) %s" % (s_(T), sep23(J, T)))
a = E("SLICE_X38Y53.A6", 0); b = E("SLICE_X38Y51.A6", 1)
sp = sep23(a, b); l1 = pw("SLICE_X39Y53.B6", "SLICE_X38Y51.A6"); h2 = pw("SLICE_X39Y53.B6", "SLICE_X38Y53.A6")
S = sp + l1[0]; H = h2[1]
print("c=%s OR hand-over %s -> %s: Sep %s; + lo(D<-X38Y51.A6) %d - hi(D<-X38Y53.A6) %d = margin %d, flip kappa %.3f" % (cc, s_(a), s_(b), sp, l1[0], H, S - H, (S - H) / (S + H)))
