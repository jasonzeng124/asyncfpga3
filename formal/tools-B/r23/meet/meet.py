"""bsub1: true meeting event of the data re-latch and the re-open branches; path sums vs ao.py Up/Sep.
usage: UPREL=1 meet.py c"""
import sys, os
c_ = sys.argv[1]; sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
idx = {n: i for i, n in enumerate(nm)}
def E(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
def evk(n, k): return eid[(idx[n], k)]
A = evk("SLICE_X22Y87.A6", 0); Bs = evk("SLICE_X27Y80.A6", 2); Cr = evk("SLICE_X24Y77.A6", 2)
def chain(e, n=400):
    """actual trigger chain: at each event the cause (any alt, or prev) that happened last"""
    out = [e]
    for _ in range(n):
        cs = set(p for alt in alts[e] for p in alt)
        if prev[e] is not None: cs.add(prev[e])
        if not cs: break
        e = max(cs, key=lambda p: (et[p], tm[p])); out.append(e)
    return out
ca, cb, cr = chain(A), chain(Bs), chain(Cr)
sa = {e: i for i, e in enumerate(ca)}
def first_common(x):
    for j, e in enumerate(x):
        if e in sa: return e, sa[e], j
    return None, None, None
eAB, ia, ib = first_common(cb); eAR, ia2, ir = first_common(cr)
print("data re-latch A =", E(A), "| select open =", E(Bs), "| re-open Cr =", E(Cr))
print("meet(A, select) =", E(eAB) if eAB is not None else None, "hops", ia, ib, "| meet(A, re-open) =", E(eAR) if eAR is not None else None, "hops", ia2, ir)
es = eAR
def is_prev(child, par): return prev[child] == par
def pathsum(ch, upto, f):
    s = 0; hops = []
    for k in range(upto):
        child, par = ch[k], ch[k + 1]; v = el[child][0]; w = el[par][0]
        d = f(v, v) if is_prev(child, par) else f(v, w); s += d; hops.append((E(child), E(par), d))
    return s, hops
hiA, hopsA = pathsum(ca, ia2, whi); loR, hopsR = pathsum(cr, ir, wlo)
print("e* =", E(es), " longest(hi) path e*->A = %d ps over %d hops; shortest(lo) path e*->Cr = %d ps over %d hops" % (hiA, ia2, loR, ir))
def pin(v, u):
    for p in g[v]["pins"]:
        if p["src"] == u and p["live"]: return p["win"][c]
Q = idx["SLICE_X25Y76.B5"]; D5 = idx["SLICE_X22Y87.D5"]; Z = idx["SLICE_X22Y81.B5"]
tailhi = pin(D5, idx["SLICE_X22Y87.A6"])[1] + pin(Z, D5)[1] + pin(Q, Z)[1]
enlo = pin(Q, idx["SLICE_X24Y77.A6"])[0]
print("tail hi (A6->D5 en pin, D5->B5 data pin, B5->Q D pin) = %d; Q enable pin lo = %d" % (tailhi, enlo))
print("PATH-SUM MARGIN = (lo e*->Cr + en lo) - (hi e*->A + tail hi) = %d ps" % (loR + enlo - hiA - tailhi))
U = up_from(es, int(tm[A])); s23 = sep23(es, Cr); sA = sepAny(es, Cr)[0]
print("ao.py: Up(e*->A) = %s ; Sep23(e*->Cr) = %s ; sepAny = %s ; certificate margin = %s" % (U.get(A), s23, sA,
      (s23 + enlo - U[A] - tailhi) if (A in U and s23 is not None) else None))
print("run gap tau(Cr)-tau(A) = %d" % (el[Cr][2] - el[A][2]))
# hop-by-hop comparison along the chain e* -> A
print("hops e*->A where Up exceeds the chain's hi sum:")
acc = 0
for k in range(ia2 - 1, -1, -1):
    child, par = ca[k], ca[k + 1]; v = el[child][0]
    h = whi(v, v) if is_prev(child, par) else whi(v, el[par][0]); acc += h
    uc = U.get(child)
    if uc is None: print("   %s not in Up set" % E(child)); break
    if uc > acc + 1:
        # what dominates: best alt's max cause, and prev clause
        info = []
        if el[child][1] > 0:
            pp = prev[child]; info.append(("prev", E(pp), U.get(pp), sep23(pp, es), relbound(pp, es)))
        for alt in alts[child]:
            info.append([(E(p), U.get(p), sep23(p, es) is not None, relbound(p, es) if (p not in U and sep23(p, es) is None) else None) for p in alt])
        print("   %s Up=%d chain-hi=%d excess=%d ; %s" % (E(child), uc, acc, uc - acc, str(info)[:600]))
        acc = uc
p = evk("SLICE_X32Y65.C6", 2)
print("cause p =", E(p), "leqP(p,e*)", leqP(p, es), "leqP(e*,p)", leqP(es, p), "U[p] from e* =", U.get(p))
m = np.minimum(VCP[p], VCP[es]); nzx = np.nonzero(m)[0]
evv = EBASE[nzx] + m[nzx].astype(np.int64) - 1; evv = evv[np.argsort(-tm[evv])]
best = []
for a in evv[:200].tolist():
    dS = sep23(a, es)
    if dS is None: continue
    U0 = up_from(a, int(tm[p]), rel=False)
    if p not in U0: continue
    best.append((U0[p] - dS, E(a), U0[p], dS))
best.sort()
print("relative-clause bases (Up0(a->p) - Sep(a->e*)), best 5 of %d with both bounds (of %d candidates):" % (len(best), len(evv)), best[:5])
print("rank of best base among candidates sorted by tm:", [i for i, a in enumerate(evv[:200].tolist()) if E(a) == best[0][1]] if best else None)
