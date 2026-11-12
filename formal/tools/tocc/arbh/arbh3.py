# arbh3 (UNTRUSTED): D = X39Y53.B6 = X38Y51.A6 | X38Y53.A6 histories, and the causal relations between consecutive input events
import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[x]: x for x in range(len(nm))}
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
evs = []
for w in ("SLICE_X38Y51.A6", "SLICE_X38Y53.A6"):
    print(w, "init", int(s0[N[w]]), "events", ev[N[w]])
    evs += [eid[(N[w], k)] for k in range(len(ev[N[w]]))]
D = N["SLICE_X39Y53.B6"]; print("D init", int(valat(D, t0)), "events", [x for x in hist[D][1] if x > t0])
evs.sort(key=lambda e: el[e][2])
for a, b in zip(evs, evs[1:]):
    print("  %s -> %s: a<=b %s Sep %s; b<=a %s" % (s_(a), s_(b), bool(leqP(a, b)), sep23(a, b), bool(leqP(b, a))))
print("alts of X38Y51.A6(1):", [[s_(p) for p in a] for a in alts[eid[(N['SLICE_X38Y51.A6'], 1)]]])
print("alts of X38Y53.A6(0):", [[s_(p) for p in a] for a in alts[eid[(N['SLICE_X38Y53.A6'], 0)]]])
