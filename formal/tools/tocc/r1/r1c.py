"""Hazard pairs behind each failing guard (UNTRUSTED). usage: r1c.py c
For a failing guard (v, z, [S, E]) the value of z read by v must not change on [tS, tE] (read times, mid delays).
Walk z's data cone over that window:
 * comb gate: recurse into data pins (same window, same deadline); exact pins (mux selects etc.) -> 'exact' pair;
 * latch L transparent somewhere in the window: L's first close after the window start, Lc; if Lc is before the
   window end, recurse into D with window [start, Lc] and deadline Lc (L holds afterwards), and add the pair
   (deadline, L's next re-open) for the hold part; else recurse into D with the same window and deadline;
 * latch closed over the whole window: pair (deadline, first re-open of L read after the window start).
A pair (X, Y) needs X before Y. R1 = Y not causally after X (not leqP). For each R1 pair: chains, ENV/ARB/OR tags,
events below X not below Y and vice versa, and why Up fails from the maximal common ancestors."""
import sys, os, re, collections, pickle, json
c_ = sys.argv[1]
sys.argv = ["datal.py", c_]
src = open("/tmp/claude-0/r1/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
an = open("/tmp/claude-0/r1/r1an.py").read()
exec(an[an.index("ARBQ = {}"):an.index("roots = collections.defaultdict(list)")])
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
idn = {x: i for i, x in enumerate(nm)}
FG = []
for ln in open("/tmp/claude-0/r1/r1an_c%s.txt" % c_):
    m = re.match(r"  (\S+) z=(\S+) S=(\S+)\((\d+)\) E=(\S+)\((\d+)\)@", ln)
    if m: FG.append((idn[m[1]], idn[m[2]], (idn[m[3]], int(m[4])), (idn[m[5]], int(m[6]))))
DCOMB = C["comb"] - C["EXC"]
def en_events(L):
    out = []
    for p, v_ in C["LATCH"][L][1]:
        pin = g[L]["pins"][p]; u = pin["src"]
        if u not in EX: continue
        md = pin["win"][c][2]
        for k, t in enumerate(ev[u]): out.append((t + md, eid[(u, k)], valat(u, t) == bool(v_)))
    return sorted(out)
def transparent(L, t):
    for p, v_ in C["LATCH"][L][1]:
        pin = g[L]["pins"][p]
        if valat(pin["src"], t - pin["win"][c][2]) == bool(v_): return True
    return False
def walk(z, a, b, X, pairs, depth=0, seen=None):
    seen = seen if seen is not None else {}
    key = (z, X)
    if key in seen:
        oa, ob = seen[key]
        if a >= oa and b <= ob: return
        a, b = min(a, oa), max(b, ob)
    seen[key] = (a, b)
    if depth > 60: return
    if z in C["LATCH"]:
        evs_ = en_events(z)
        openin = transparent(z, a) or any(a < t <= b and op for t, e_, op in evs_)
        if openin:
            closes = [(t, e_) for t, e_, op in evs_ if t > a and not op and not transparent(z, t)]
            Lc = closes[0] if closes else None
            enp = set(p for p, v_ in C["LATCH"][z][1])
            if Lc is not None and Lc[0] < b:
                nb, nX = Lc[0], Lc[1]
                ro = [(t, e_) for t, e_, op in evs_ if t > Lc[0] and op]
                if ro: pairs.append(("reopen", X, ro[0][1], z, ro[0][0]))
            else: nb, nX = b, X
            for j, p in enumerate(g[z]["pins"]):
                s = p["src"]
                if not p["live"] or j in enp or s == z: continue
                d = p["win"][c][2]
                if s in DCOMB or s in C["LATCH"]: walk(s, a - d, nb - d, nX, pairs, depth + 1, seen)
                elif s in EX and s not in C["const"]: exact_pair(s, a - d, nb - d, nX, pairs, z)
        else:
            ro = [(t, e_) for t, e_, op in evs_ if t > a and op]
            if ro: pairs.append(("reopen", X, ro[0][1], z, ro[0][0]))
        return
    if z not in g or z not in DCOMB: return
    for p in C["live"][z]:
        s = p["src"]; d = p["win"][c][2]
        if s in DCOMB or s in C["LATCH"]: walk(s, a - d, b - d, X, pairs, depth + 1, seen)
        elif s in EX and s not in C["const"]: exact_pair(s, a - d, b - d, X, pairs, z)
def exact_pair(s, a, b, X, pairs, via):
    nk = [k for k, t in enumerate(ev[s]) if t > a]
    if nk: pairs.append(("exact" if ev[s][nk[0]] > b else "exact-inside", X, eid[(s, nk[0])], via, ev[s][nk[0]]))
ALL = collections.defaultdict(list); per_guard = []
for v, z, st, en_ in FG:
    E = eid[en_]; S = eid[st]
    tS = et[S] + mid_(v, st[0]) - mid_(v, z); tE = et[E] + mid_(v, en_[0]) - mid_(v, z)
    pairs = []; walk(z, tS, tE, E, pairs); pairs = list(set(pairs))
    bad = [p for p in pairs if p[1] != p[2] and not leqP(p[1], p[2])]
    per_guard.append((v, z, st, en_, len(pairs), bad))
    for kind, X, Y, via, ty in bad: ALL[(kind, X, Y)].append((v, z, st, en_, via))
print("[c=%s] failing guards %d; guards with at least one unordered hazard pair %d" % (c_, len(FG), sum(1 for x in per_guard if x[5])))
kc = collections.Counter(k[0] for k in ALL)
print("distinct unordered pairs by kind:", dict(kc))
for v, z, st, en_, np_, bad in per_guard:
    print("  %s z=%s S=%s(%d) E=%s(%d): %d pairs, unordered: %s" % (nm[v], nm[z], nm[st[0]], st[1], nm[en_[0]], en_[1], np_,
          sorted(set("%s %s<%s via %s" % (k, en(X), en(Y), nm[via]) for k, X, Y, via, ty in bad))[:4]))
OUT = []
for (kind, X, Y), lst in sorted(ALL.items(), key=lambda kv: -len(kv[1])):
    print("\n=== [%s] X=%s must precede Y=%s (gap %+d ps) [%d guards; via %s]" % (kind, en(X), en(Y), et[Y] - et[X], len(set((a_[0], a_[2], a_[3]) for a_ in lst)), sorted(set(nm[a_[4]] for a_ in lst))))
    print("    guards:", sorted(set((nm[a_[0]], nm[a_[1]], "%s(%d)" % (nm[a_[3][0]], a_[3][1])) for a_ in lst))[:6])
    mc = maximal_common(X, Y)
    chX = crit_chain(X, Y); chY = crit_chain(Y, X)
    print("    maximal common ancestors (%d): %s" % (len(mc), [en(e_) for e_ in mc[:6]]))
    print("    chain to X (%d):" % len(chX), " -> ".join(en(e_) for e_ in chX))
    print("    chain to Y (%d):" % len(chY), " -> ".join(en(e_) for e_ in chY))
    def between(P, Q):
        return [e_ for e_ in range(NE) if tm[e_] <= tm[P] and (leqP(e_, P) or e_ == P) and not (leqP(e_, Q) or e_ == Q)]
    bX = between(X, Y); bY = between(Y, X)
    envX = [en(e_) for e_ in bX if el[e_][0] in envnode]; envY = [en(e_) for e_ in bY if el[e_][0] in envnode]
    arbX = [en(e_) for e_ in bX if nm[el[e_][0]] in ARBQ]; arbY = [en(e_) for e_ in bY if nm[el[e_][0]] in ARBQ]
    print("    below X not Y: %d events, OR %d, ENV %s, ARB %s" % (len(bX), sum(1 for e_ in bX if len(alts[e_]) > 1), envX, arbX[:6]))
    print("    below Y not X: %d events, OR %d, ENV %s, ARB %s" % (len(bY), sum(1 for e_ in bY if len(alts[e_]) > 1), envY, arbY[:6]))
    sY = sep23(Y, X)
    print("    reverse order: Y <= X causally? %s; Sep23(Y->X) = %s" % (bool(leqP(Y, X)), sY))
    ups = []
    for e0 in mc[:4]:
        s = sep23(e0, Y)
        w, blk = why_no_up(e0, X, crit_chain(X, e0))
        ups.append((en(e0), s, w)); print("    e0=%s: Sep23(e0->Y)=%s; %s" % (en(e0), s, w))
    OUT.append(dict(kind=kind, X=(nm[el[X][0]], el[X][1]), Y=(nm[el[Y][0]], el[Y][1]), tX=int(et[X]), tY=int(et[Y]),
                    guards=sorted(set((nm[a_[0]], nm[a_[1]], (nm[a_[2][0]], a_[2][1]), (nm[a_[3][0]], a_[3][1]), nm[a_[4]]) for a_ in lst)),
                    chX=[en(e_) for e_ in chX], chY=[en(e_) for e_ in chY], envX=envX, envY=envY, arbX=arbX, arbY=arbY, ups=ups,
                    nbX=len(bX), nbY=len(bY), revleq=bool(leqP(Y, X))))
pickle.dump(dict(OUT=OUT), open("/tmp/claude-0/r1/r1c_c%s.pkl" % c_, "wb"))
