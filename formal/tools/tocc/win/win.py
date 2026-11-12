#!/usr/bin/env python3
"""Shard C window study (UNTRUSTED).  usage: win.py c PAIR [PAIR ...]   (PAIR = _a_b; needs ao_c<c>_..._dcp<PAIR>.pkl)
1. node groups: per exact node, event count as a function of the token-level loop counts (tok.py) across the pairs.
2. windows: cut each run at the events of a head node h (main loop: count 2*L9; inner loop: count 2*L10); an event e
   belongs to window floor(VCP[e,h] / 2) - (0 for events below no head event: window -1 = prefix).  VCP = plain CP order
   (min over AND-OR alternatives), so per node the windows are contiguous.
3. for windows of the same kind: per-node counts, alternatives (shifted by the per-node offsets o_j), L (final VC incl. RT
   edges, and per-reader lowered entries), RT edges, time stamps relative to the head event."""
import sys, os, pickle, collections, itertools
import numpy as np
sys.path.insert(0, "/tmp/claude-0/win")
import tok
c = int(sys.argv[1]); PAIRS = sys.argv[2:]
SUF = "_prevanc_cyc_causeanc_dcp"
nm = pickle.load(open("/tmp/claude-0/win/model.pkl", "rb"))["names"]
R = {}
for P in PAIRS:
    D = pickle.load(open("/tmp/claude-0/win/ao_c%d%s%s.pkl" % (c, SUF, P), "rb"))
    a, b = map(int, P.strip("_").split("_")); tr, _ = tok.run(a, b)
    D["tok"] = tr; D["tc"] = collections.Counter(x[0] for x in tr)
    D["tc"]["L10c"] = sum(1 for x in tr if x[0] == "L10" and x[1]); D["tc"]["L4c"] = sum(1 for x in tr if x[0] == "L4" and x[1])
    D["tc"]["L6c"] = sum(1 for x in tr if x[0] == "L6" and x[1])
    el = D["el"]; D["cnt"] = collections.Counter(n for n, k, t in el); D["eid"] = {(n, k): i for i, (n, k, t) in enumerate(el)}
    D["xi"] = {n: i for i, n in enumerate(D["xs"])}
    R[P] = D
out = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s); out.append(s)
# ---- 1. node groups
nodes = sorted(set().union(*[set(D["xs"]) for D in R.values()]))
sig = collections.defaultdict(list)
for n in nodes: sig[tuple(R[P]["cnt"].get(n, 0) for P in PAIRS)].append(n)
pr("[c=%d] pairs %s" % (c, PAIRS))
for P in PAIRS: pr("  %s token loop counts %s; events %d" % (P, dict(R[P]["tc"]), len(R[P]["el"])))
feats = ["L2", "L4", "L4c", "L6", "L6c", "L9", "L10", "L10c"]
pr("  node groups (event counts per pair -> nodes; best fit count = sum coef*feature + const):")
for s, ns in sorted(sig.items(), key=lambda x: -len(x[1])):
    fit = ""
    for f1, f2 in itertools.product(feats + [None], repeat=2):
        for c1, c2, k0 in itertools.product((1, 2), (0, -1, -2, 1, 2), (0, 1, 2, -1, -2, 3)):
            if f1 and not any(R[P]["tc"][f1] for P in PAIRS): continue
            if f2 and not any(R[P]["tc"][f2] for P in PAIRS): continue
            if all(c1 * R[P]["tc"][f1 or "x"] + (c2 * R[P]["tc"][f2] if f2 else 0) + k0 == s[i] for i, P in enumerate(PAIRS)) and f1:
                fit = "%d*%s%s%+d" % (c1, f1, ("%+d*%s" % (c2, f2)) if f2 and c2 else "", k0); break
        if fit: break
    pr("    %s : %d nodes  fit %s" % (s, len(ns), fit or "?"))
pickle.dump(dict(sig=dict(sig)), open("/tmp/claude-0/win/groups_c%d.pkl" % c, "wb"))
# ---- 2/3. windows
def windows(D, h):
    VCP = D["VCP"]; xi = D["xi"]; el = D["el"]
    hv = VCP[:, xi[h]].astype(np.int64)
    w = np.where(hv == 0, -1, (hv - 1) // 2)
    return w
from classify import load
CM = load(); ENVN = set(CM["bs"][k] for k in ("req", "pend_ack", "out0_ack", "rst"))
def Dsets(D):
    """reader v -> D(v) as in ao.Dof (env readers: approximated by alt sources)"""
    el = D["el"]; alts = D["alts"]; EXs = set(D["xs"]); out = {}
    byn = collections.defaultdict(list)
    for e, (n, k, t) in enumerate(el): byn[n].append(e)
    for v in D["xs"]:
        S = [v]
        if v in CM["live"] and v not in ENVN:
            for p in CM["live"][v]:
                w = p["src"]
                if w in EXs and w not in S: S.append(w)
        for e in byn[v]:
            for alt in alts[e]:
                for q in alt:
                    if el[q][0] not in S: S.append(el[q][0])
        out[v] = S
    return out
def analyse(D, h, kindf, label, refine=None):
    el = D["el"]; eid = D["eid"]; xs = D["xs"]; xi = D["xi"]; VC = D["VC"]; alts = D["alts"]; rt = D["rt"]; OV = D["OVER"]
    if "DS" not in D:
        D["DS"] = Dsets(D); rd = collections.defaultdict(set)
        for v, S in D["DS"].items():
            for a in S: rd[a].add(v)
        D["RD"] = rd
    DS = D["DS"]; RD = D["RD"]
    w = windows(D, h); NW = int(w.max()) + 1
    cnt = collections.defaultdict(lambda: collections.Counter())
    for e, (n, k, t) in enumerate(el): cnt[int(w[e])][n] += 1
    nonmono = 0
    for n in xs:
        ws = [int(w[eid[(n, k)]]) for k in range(D["cnt"].get(n, 0))]
        if ws != sorted(ws): nonmono += 1
    off = {}
    run = collections.Counter()
    for j in range(-1, NW + 1):
        off[j] = dict(run); run.update(cnt[j])
    def o(j, n): return off[j].get(n, 0)
    hev = [eid[(h, 2 * j)] for j in range(NW)]
    th = [el[x][2] for x in hev]
    kinds = [kindf(D, j) for j in range(NW)]
    if refine: kinds = [(kinds[j], refine(cnt[j])) for j in range(NW)]
    pr("  [%s] head %s; windows %d (+prefix -1); events per window %s; kinds %s; per-node window non-monotone %d" % (
        label, nm[h], NW, [sum(cnt[j].values()) for j in range(-1, NW)], kinds, nonmono))
    def rel(x, j):
        n, k, t = el[x]; return (nm[n], k - o(j, n))
    def sig_ev(x, j):
        n, k, t = el[x]
        A = frozenset(frozenset(rel(p, j) for p in alt) for alt in alts[x])
        Ls = {}
        for v in RD[n]:
            for b in DS[v]:
                if b == n: continue
                L = min(int(VC[x, xi[b]]), OV.get(v, {}).get((n, k, b), 99))
                Ls[(nm[v], nm[b])] = L - o(j, b)
        RT = frozenset(rel(p, j) for p in rt.get(x, []))
        return A, Ls, RT, t - th[j]
    back = collections.Counter(); farn = collections.Counter()
    for j in range(NW):
        for e in np.nonzero(w == j)[0]:
            for alt in alts[int(e)]:
                for p in alt:
                    d = j - int(w[p]); back[d] += 1
                    if d >= 2: farn[(nm[el[int(e)][0]], nm[el[p][0]], "prefix" if w[p] < 0 else "w")] += 1
            for p in rt.get(int(e), []):
                d = j - int(w[p]); back[("rt", d)] += 1
                if d >= 2: farn[("RT", nm[el[int(e)][0]], nm[el[p][0]], "prefix" if w[p] < 0 else "w")] += 1
    pr("    cause reach (window of event - window of cause -> count): %s" % sorted(back.items(), key=str))
    pr("    reach >= 2 windows, by (event node, cause node, cause in prefix or a window): %s" % sorted(farn.items()))
    byk = collections.defaultdict(list)
    for j in range(NW): byk[kinds[j]].append(j)
    res = {}
    for kd, js in sorted(byk.items(), key=str):
        rep = []
        pr("    kind %s: windows %s, sizes %s events, %d nodes" % (kd, js, [sum(cnt[j].values()) for j in js], len(cnt[js[0]])))
        for j0, j in zip(js, js[1:]):
            dc = [n for n in set(cnt[j]) | set(cnt[j0]) if cnt[j][n] != cnt[j0][n]]
            dA = dL = dR = nev = 0; dT = []; exA = []; exL = []; exT = []
            for n in cnt[j]:
                if n in dc: continue
                for i in range(cnt[j][n]):
                    x0 = eid[(n, o(j0, n) + i)]; x1 = eid[(n, o(j, n) + i)]; nev += 1
                    s0 = sig_ev(x0, j0); s1 = sig_ev(x1, j)
                    if s0[0] != s1[0]: dA += 1; exA.append((nm[n], i, s0[0], s1[0]))
                    if s0[1] != s1[1]:
                        dL += 1; dd = [(k_, s0[1].get(k_), s1[1].get(k_)) for k_ in set(s0[1]) | set(s1[1]) if s0[1].get(k_) != s1[1].get(k_)]
                        exL.append((nm[n], i, len(dd), dd[:2]))
                    if s0[2] != s1[2]: dR += 1
                    dT.append(s1[3] - s0[3])
                    if s1[3] != s0[3]: exT.append((s1[3] - s0[3], nm[n], i))
            odd = [nm[n] for n in xs if (o(j, n) - o(j0, n)) % 2 and cnt[j].get(n, 0) + cnt[j0].get(n, 0) > 0]
            oddall = sum(1 for n in xs if (o(j, n) - o(j0, n)) % 2)
            pr("      w%d vs w%d: nodes with ODD offset difference (state polarity flipped): %d active in the windows %s, %d overall" % (j, j0, len(odd), odd[:5], oddall))
            rep.append(dict(odd=len(odd), oddall=oddall, j=j, dc=len(dc), dA=dA, dL=dL, dR=dR, nev=nev, dT=(min(dT), max(dT)) if dT else None))
            pr("      w%d vs w%d: count-diff nodes %d; on the %d events of equal-count nodes: alt-diff %d, L-diff %d, RT-diff %d, dt range %s, dt!=0 at %d events" % (
                j, j0, len(dc), nev, dA, dL, dR, rep[-1]["dT"], len(exT)))
            for x in exA[:2]: pr("         alt diff: %s(+%d) %s | %s" % (x[0], x[1], sorted(map(sorted, x[2])), sorted(map(sorted, x[3]))))
            for x in exL[:2]: pr("         L diff: %s(+%d) %d entries, e.g. %s" % x)
            if exT: pr("         dt diff e.g. %s" % (sorted(exT)[:2] + sorted(exT)[-1:]))
            for n in dc[:6]: pr("         count diff: %s %d vs %d; per-window counts %s" % (nm[n], cnt[j0][n], cnt[j][n], [cnt[q][n] for q in range(-1, NW)]))
        res[kd] = (js, rep)
    return w, res, {j: dict(v) for j, v in cnt.items()}, kinds

# ---- kinds from the token run
def main_kinds(D):
    ks = []; cur = None
    for x in D["tok"]:
        if x[0] == "L9": cur = [0, None]; ks.append(cur)
        elif x[0] == "L10" and cur is not None: cur[0] += 1
        elif x[0] == "Z10" and cur is not None: cur[1] = x[1]
    return [("inner%d" % a, "exit" if z else "loop") for a, z in ks]
def inner_kinds(D):
    ks = []; first = False; seen9 = False
    for x in D["tok"]:
        if x[0] == "L9": first = True; seen9 = True
        elif x[0] == "L10" and seen9: ks.append(["first" if first else "next", "shift" if x[1] else "exit"]); first = False
        elif x[0] == "Z10" and seen9: ks[-1][1] = "exit-done" if x[1] else "exit-loop"
    return [tuple(k) for k in ks]
def pick_head(D, P, want):
    i = PAIRS.index(P)
    cands = [n for s, ns in sig.items() if all(s[q] == want(R[PP]) for q, PP in enumerate(PAIRS)) for n in ns]
    if not cands: return None
    eid = D["eid"]; el = D["el"]
    return min(cands, key=lambda n: (el[eid[(n, 0)]][2], n))
RES = {}
for P in PAIRS:
    D = R[P]; pr("== pair %s" % P)
    mk = main_kinds(D); ik = inner_kinds(D)
    h9 = pick_head(D, P, lambda X: 2 * X["tc"]["L9"])
    h10 = pick_head(D, P, lambda X: 2 * X["tc"]["L10"])
    r9 = analyse(D, h9, lambda D_, j: mk[j] if j < len(mk) else "extra", "main loop (cm9)") if h9 else None
    r10 = analyse(D, h10, lambda D_, j: ik[j] if j < len(ik) else "extra", "inner loop (cm10)") if h10 else None
    RES[P] = (h9, h10, r9, r10)
open("/tmp/claude-0/win/win_c%d.txt" % c, "w").write("\n".join(out) + "\n")
pickle.dump(RES, open("/tmp/claude-0/win/win_c%d.pkl" % c, "wb"))
