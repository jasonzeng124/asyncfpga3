import sys, pickle, collections, os
c_ = sys.argv[1]
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/r1c/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
dsrc = open("/tmp/claude-0/r1c/data.py").read()
a0 = dsrc.index("def dwin(v, z):"); a1 = dsrc.index("def terms(")
exec(dsrc[a0:a1].replace('def valat(n, t): return K["valat"](n, t)', ''))
DEPTH = 4
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
def first_close_after(l, T):
    en = ens(l); cand = []
    for p, vv in en:
        pp = g[l]["pins"][p]
        for k, t in enumerate(ev[pp["src"]]): cand.append(t + pp["win"][c][2])
    for rt in sorted(cand):
        if rt > T and not transp(l, rt) and transp(l, rt - 1): return rt
    return None
def terms2(z, T, depth, via):
    out = []
    for l, (plo, phi) in paths(z).items():
        Tref = T - (plo + phi) // 2
        st = transp(l, Tref)
        en = ens(l); cand = []
        for p, vv in en:
            pp = g[l]["pins"][p]
            for k, t in enumerate(ev[pp["src"]]): cand.append((t + pp["win"][c][2], pp["src"], k, p))
        cand.sort(); B = None; Brt = None
        for (rt, s_, k, p) in cand:
            if rt > Tref and transp(l, rt) and not transp(l, rt - 1): B = (s_, k); Brt = rt; break
        out.append((l, B, Brt, list(via)))
        if st and depth < DEPTH:
            fb = C["LATCH"][l][0]; enp = {p for p, _ in C["LATCH"][l][1]}
            fc = first_close_after(l, Tref)
            for j, p in enumerate(g[l]["pins"]):
                if not p["live"] or j in fb or j in enp or p["src"] in C["const"] or p["src"] in EX: continue
                out += terms2(p["src"], Tref - p["win"][c][2], depth + 1, via + [(l, fc)])
    return out
rows = pickle.load(open("/tmp/claude-0/r1c/data2_c%s.pkl" % c_, "rb"))
cnt = collections.Counter(); ex = []; mv = collections.Counter()
for r in rows:
    if r[0] >= 0: continue
    _, ms, me, v, z, st, en, val, why, wa, wb = r
    if en is None: continue
    E = eid[en]; tE = et[E] + mid_(v, en[0])
    u, j = st; ts = ev[u][j] + mid_(v, u)
    bad = cut = 0; tS0 = ts
    for (l, B, Brt, via) in terms2(z, ts - mid_(v, z), 0, []):
        if B is None or et[eid[B]] >= et[E]: continue
        # cut if some intermediate (transparent-at-use) latch closed before this upstream reopening was read
        if any(fc is not None and fc < Brt for (l2, fc) in via): cut += 1
        else:
            bad += 1
            vl = [l2 for (l2, fc) in via]
            moved = [nm[x] for x in vl + [l] if any(tS0 <= t <= tE for t in (hist[x][1] if x in hist else []))]
            mv["via/upstream latch changed in window" if any(nm[x] in moved for x in vl) else ("only the upstream latch changed (masked downstream)" if moved else "nothing changed")] += 1
            if len(ex) < 3: ex.append((nm[v], nm[z], nm[l], B and (nm[B[0]], B[1]), int(et[eid[B]]), int(et[E]), [(nm[a], b) for a, b in via]))
    if bad or cut: cnt["guard with B-before-E: all cut by an intermediate latch closing" if not bad else "guard with an uncut B-before-E term"] += 1
print("[c=%s]" % c_, dict(cnt), "terms:", dict(mv))
for x in ex: print("  uncut:", x)
