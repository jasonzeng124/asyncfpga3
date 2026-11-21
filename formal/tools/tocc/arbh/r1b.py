"""R1 (model-level, UNTRUSTED): for each failing guard (parsed from r1an_c<c>.txt), the first latch RE-OPEN in z's data
cone (first latch level) after the reader's E, its gap, and whether it is causally ordered after E in the certificate
(leqP). R1 = re-open unordered with E. For each distinct (E, reopen) pair: chains, env/arb tags, Up blocking.
usage: r1b.py c"""
import sys, os, re, collections, pickle, json
c_ = sys.argv[1]
sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/arbh/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
an = open("/tmp/claude-0/arbh/r1an.py").read()
an = an[an.index("ARBQ = {}"):an.index("roots = collections.defaultdict(list)")]
exec(an)
idn = {x: i for i, x in enumerate(nm)}
FG = []
for ln in open("/tmp/claude-0/arbh/r1an_c%s.txt" % c_):
    m = re.match(r"  (\S+) z=(\S+) S=(\S+)\((\d+)\) E=(\S+)\((\d+)\)@", ln)
    if m: FG.append((idn[m[1]], idn[m[2]], (idn[m[3]], int(m[4])), (idn[m[5]], int(m[6]))))
print("[c=%s] failing guards parsed: %d" % (c_, len(FG)))
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
DCOMB = C["comb"] - C["EXC"]
def transparent(Q, t):
    for p, v_ in C["LATCH"][Q][1]:
        pin = g[Q]["pins"][p]
        if valat(pin["src"], t - pin["win"][c][2]) == bool(v_): return True
    return False
OPENAT = collections.Counter(); EXP = {}
def cone_latches(z, tE):
    """closed latches bounding z's data cone at time tE (walking through comb and through latches transparent at tE)"""
    out = set(); seen = {z}; todo = [z]
    while todo:
        u = todo.pop()
        if u in C["LATCH"] and (u != z or True):
            if not transparent(u, tE): out.add(u); continue
            OPENAT[nm[u]] += 1
            enp = set(p for p, v_ in C["LATCH"][u][1])
            for j, p in enumerate(g[u]["pins"]):
                s = p["src"]
                if not p["live"] or j in enp or s == u: continue
                if s not in seen and (s in DCOMB or s in C["LATCH"]): seen.add(s); todo.append(s)
            continue
        if u not in g: continue
        if u != z and u not in DCOMB: continue
        for p in C["live"][u]:
            s = p["src"]
            if s in EX and s not in C["const"]: EXP.setdefault(z, set()).add((s, p["win"][c][2]))
            if s not in seen and (s in DCOMB or s in C["LATCH"]): seen.add(s); todo.append(s)
    return out
def reopens(Q, after):
    """first event of an enable source of latch Q making it transparent, read (mid) after time `after`"""
    best = None
    for p, v_ in C["LATCH"][Q][1]:
        pin = g[Q]["pins"][p]; u = pin["src"]
        if u not in EX: continue
        md = pin["win"][c][2]
        for k, t in enumerate(ev[u]):
            if t + md <= after: continue
            if valat(u, t) == bool(v_):
                if best is None or t + md < best[0]: best = (t + md, eid[(u, k)], Q)
                break
    return best
rows = []; pairs = collections.defaultdict(list)
for v, z, st, en_ in FG:
    E = eid[en_]; tE = et[E] + mid_(v, en_[0])
    zf = [x for x in flips(z) if x > tE - mid_(v, z)]
    cands = [r for r in (reopens(Q, tE - 0) for Q in cone_latches(z, tE)) if r]
    # earliest re-open after E, and earliest UNORDERED one
    for (s_, md) in EXP.get(z, ()):
        nk = [k for k, t in enumerate(ev[s_]) if t + md > tE]
        if nk: cands.append((ev[s_][nk[0]] + md, eid[(s_, nk[0])], s_))
    cands.sort()
    first = cands[0] if cands else None
    unord = [r for r in cands if not leqP(E, r[1])]
    fu = unord[0] if unord else None
    rows.append((v, z, st, en_, first, fu, zf[0] if zf else None, tE))
    if fu: pairs[(E, fu[1])].append((v, z, st, en_, fu[2], fu[0] - tE))
print("latches found transparent at E (walked through):", OPENAT.most_common(8))
print("guards with an UNORDERED re-open in z's first latch level after E: %d of %d" % (sum(1 for r in rows if r[5]), len(rows)))
print("guards whose first re-open after E is unordered: %d" % sum(1 for r in rows if r[4] and r[5] and r[4][1] == r[5][1]))
for v, z, st, en_, first, fu, zf, tE in rows:
    E = eid[en_]
    print("  %s z=%s E=%s(%d) | first reopen %s | first UNORDERED reopen %s | z next flip (as read) %s" % (
        nm[v], nm[z], nm[en_[0]], en_[1],
        ("%s via %s gap %+d ordered=%s sep23=%s need<=%d" % (en(first[1]), nm[first[2]], first[0] - tE, bool(leqP(E, first[1])), sep23(E, first[1]), hi_(v, en_[0]) - lo_(v, z))) if first else None,
        ("%s latch %s gap %+d" % (en(fu[1]), nm[fu[2]], fu[0] - tE)) if fu else None,
        ("%+d" % (zf + mid_(v, z) - tE)) if zf else None))
OUT = []
for (E, B), lst in sorted(pairs.items(), key=lambda kv: -len(kv[1])):
    print("\n=== E=%s  reopen=%s  [%d guards; latches %s; gaps %s]" % (en(E), en(B), len(lst), sorted(set(nm[x[4]] for x in lst)),
          sorted(set(int(x[5]) for x in lst))[:4]))
    print("    guards:", sorted(set((nm[x[0]], nm[x[1]]) for x in lst)))
    mc = maximal_common(E, B)
    chE = crit_chain(E, B); chB = crit_chain(B, E)
    print("    maximal common ancestors (%d): %s" % (len(mc), [en(e_) for e_ in mc[:6]]))
    print("    chain to E (%d ev):" % len(chE), " -> ".join(en(e_) for e_ in chE))
    print("    chain to reopen (%d ev):" % len(chB), " -> ".join(en(e_) for e_ in chB))
    envE = [en(e_) for e_ in chE if el[e_][0] in envnode]; envB = [en(e_) for e_ in chB if el[e_][0] in envnode]
    arbE = [en(e_) for e_ in chE if nm[el[e_][0]] in ARBQ]; arbB = [en(e_) for e_ in chB if nm[el[e_][0]] in ARBQ]
    orE = [en(e_) for e_ in chE if len(alts[e_]) > 1]; orB = [en(e_) for e_ in chB if len(alts[e_]) > 1]
    print("    ENV on E-chain %s | ENV on reopen-chain %s | ARB on E-chain %s | ARB on reopen-chain %s" % (envE, envB, arbE, arbB))
    print("    OR events: E-chain %d, reopen-chain %d" % (len(orE), len(orB)))
    # all env/arb events strictly between common frontier and E / B (not only critical chain)
    def between(X, Y):
        """events e with e <= X causally, not <= Y"""
        r = []
        for e_ in range(NE):
            if tm[e_] > tm[X]: continue
            if (leqP(e_, X) or e_ == X) and not (leqP(e_, Y) or e_ == Y): r.append(e_)
        return r
    bE = between(E, B); bB = between(B, E)
    def kinds(lst_):
        k = collections.Counter()
        for e_ in lst_:
            for t_ in tag(e_):
                k[t_.split(":")[0] if t_.startswith("OR") else t_] += 1
        return dict(k)
    print("    events below E not below reopen: %d %s; ENV: %s; ARB: %s" % (len(bE), kinds(bE),
          [en(e_) for e_ in bE if el[e_][0] in envnode][:6], [en(e_) for e_ in bE if nm[el[e_][0]] in ARBQ][:6]))
    print("    events below reopen not below E: %d %s; ENV: %s; ARB: %s" % (len(bB), kinds(bB),
          [en(e_) for e_ in bB if el[e_][0] in envnode][:6], [en(e_) for e_ in bB if nm[el[e_][0]] in ARBQ][:6]))
    ups = []
    for e0 in mc[:4]:
        s = sep23(e0, B)
        w, blk = why_no_up(e0, E, crit_chain(E, e0))
        ups.append((en(e0), s, w)); print("    e0=%s: Sep23(e0->reopen)=%s; %s" % (en(e0), s, w))
    OUT.append(dict(E=(nm[el[E][0]], el[E][1]), B=(nm[el[B][0]], el[B][1]), tE=int(et[E]), tB=int(et[B]),
                    guards=[(nm[x[0]], nm[x[1]], nm[x[2][0]], x[2][1], nm[x[3][0]], x[3][1], nm[x[4]], int(x[5])) for x in lst],
                    envE=envE, envB=envB, arbE=arbE, arbB=arbB, ups=ups,
                    envBelowE=[en(e_) for e_ in bE if el[e_][0] in envnode], envBelowB=[en(e_) for e_ in bB if el[e_][0] in envnode],
                    arbBelowE=[en(e_) for e_ in bE if nm[el[e_][0]] in ARBQ], arbBelowB=[en(e_) for e_ in bB if nm[el[e_][0]] in ARBQ]))
pickle.dump(dict(OUT=OUT, rows=[(nm[r[0]], nm[r[1]], (nm[r[2][0]], r[2][1]), (nm[r[3][0]], r[3][1]),
                                 (nm[el[r[4][1]][0]], el[r[4][1]][1], nm[r[4][2]]) if r[4] else None,
                                 (nm[el[r[5][1]][0]], el[r[5][1]][1], nm[r[5][2]]) if r[5] else None) for r in rows]),
            open("/tmp/claude-0/arbh/r1b_c%s.pkl" % c_, "wb"))
