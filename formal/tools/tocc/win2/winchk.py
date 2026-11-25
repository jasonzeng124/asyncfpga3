#!/usr/bin/env python3
"""Shard C, every-word structural checks on THE target's window decomposition (UNTRUSTED Python; one simulated run).
usage: winchk.py c PAIR [alphabet]     (PAIR = _a_b; needs ao_c<c>_prevanc_cyc_causeanc_dcp<PAIR>.pkl with VCP/OVER/xs/prev)

Word: word index 0 = the prefix (events below the first main-loop head event), index i >= 1 = main-loop window i-1
(window of e = floor((VCP[e,h]-1)/2), h = SLICE_X39Y21.C5, as win/win.py).  Per word index i: len_i(u), off_i(u).
Relative coordinates as Formal/Net/AO/Unroll*.lean: cause q = (node, abs - off_i(node)); Lr(u,k,c) = L(e,c) - off_i(c)
with L = VC (CF order incl. RT edges, ao.py's LSound bound) [variant: L lowered by min over readers of ao's OVER].
Checks (Lean definitions quoted in RESULTS.txt):
  BackChain  (UnrollTime)  physical causes of window i+1 (alts) : rel >= -len_i(q)
  PairChain  (UnrollAsm)   a,c in some D(v), len_{i+1}(a) > 0 : -len_i(c) <= Lr_{i+1}(a,0,c)
  StChain    (UnrollData)  s0_{i+1}(u) = s0_i(u) xor len_i(u)%2, with s0 a function of the KIND (kind invariance)
  KindLStep  (UnrollRest)  on wF (fc = alt + RT edges), five clauses, pv = previous window
  KindRT / KindSub / KindNe (UnrollRest) with fc = [alt + rt(e) for alt in alts(e)], sep from ao.rtinfo
  kind invariance of len / causes / fc / Lr / s0 (the kind's data must be one WKindF per kind)"""
import sys, pickle, collections
import numpy as np
sys.path.insert(0, "/tmp/claude-0/winchk")
import tok
from classify import load
c = int(sys.argv[1]); P = sys.argv[2]; ALPH = sys.argv[3] if len(sys.argv) > 3 else "m"
D = pickle.load(open("/tmp/claude-0/winchk/ao_c%d_prevanc_cyc_causeanc_dcp%s.pkl" % (c, P), "rb"))
CM = load(); nm = CM["names"]; bs = CM["bs"]
el = D["el"]; alts = D["alts"]; rt = D["rt"]; VC = D["VC"]; VCP = D["VCP"]; OVER = D["OVER"]; xs = D["xs"]
prevE = D["prev"]; s0 = D["s0"]; rtinfo = D["rtinfo"]
NE = len(el); NX = len(xs); xi = {n: i for i, n in enumerate(xs)}
eid = {(n, k): i for i, (n, k, t) in enumerate(el)}
cnt = collections.Counter(n for n, k, t in el)
enode = np.array([xi[n] for n, k, t in el]); ek = np.array([k for n, k, t in el])
ENVN = {bs[k]: k for k in ("req", "pend_ack", "out0_ack", "rst")}
RST = bs["rst"]
out = []
def pr(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.append(s)
a_, b_ = map(int, P.strip("_").split("_")); tr, _ = tok.run(a_, b_)
def main_kinds():
    ks = []; cur = None
    for x in tr:
        if x[0] == "L9": cur = [0, None]; ks.append(cur)
        elif x[0] == "L10" and cur is not None: cur[0] += 1
        elif x[0] == "Z10" and cur is not None: cur[1] = x[1]
    return [("m%d" % a, "exit" if z else "loop") for a, z in ks]
def inner_kinds():
    ks = []; first = 0; seen9 = False
    for x in tr:
        if x[0] == "L9": first = 0; seen9 = True
        elif x[0] == "L10" and seen9:
            ks.append(["first" if first == 0 else ("second" if first == 1 else "later"), "shift" if x[1] else "exit"]); first += 1
        elif x[0] == "Z10" and seen9: ks[-1][1] = "exit-done" if x[1] else "exit-loop"
    return [tuple(k) for k in ks]
# ---------------- D sets (as ao.Dof)
EXs = set(xs)
byn = collections.defaultdict(list)
for e, (n, k, t) in enumerate(el): byn[n].append(e)
from cert import ENVREAD
def Dof(v):
    if v in ENVN: return [v] + [bs[k] for k in ENVREAD[ENVN[v]]]
    S = [v]
    for p in CM["live"][v]:
        w = p["src"]
        if w in EXs and w not in S: S.append(w)
    for e in byn[v]:
        for alt in alts[e]:
            for q in alt:
                if el[q][0] not in S: S.append(el[q][0])
    return S
DS = {v: Dof(v) for v in xs}
partners = collections.defaultdict(set)   # a -> {c : a, c in D(v) for some v}
for v, S in DS.items():
    for a in S: partners[a].update(S)
inD = set().union(*DS.values())
pr("[c=%d pair %s] events %d, exact nodes %d, nodes in some D(v) %d, (a,c) dependency pairs %d" % (
    c, P, NE, NX, len(inD), sum(len(s) for s in partners.values())))
# ---------------- L variants
Lvc = VC.astype(np.int32)
Llow = Lvc.copy(); nlow = 0
for v, ov in OVER.items():
    for (a, k, b), m2 in ov.items():
        e = eid[(a, k)]
        if m2 < Llow[e, xi[b]]: Llow[e, xi[b]] = m2; nlow += 1
pr("L variants: VC (CF order incl. RT, single L); 'low' = VC lowered by min over readers of ao OVER (%d entries)" % nlow)
def fc(e): return [list(alt) + list(rt.get(e, [])) for alt in alts[e]]

def run(label, hname, kinds_of_window, inner=False):
    h = xi[next(i for i, n in enumerate(nm) if n == hname)]
    hv = VCP[:, h].astype(np.int64)
    W = np.where(hv == 0, 0, (hv - 1) // 2 + 1)        # word index: 0 = prefix
    NWw = int(W.max()) + 1
    nonmono = sum(1 for n in xs if list(W[byn[n]]) != sorted(W[byn[n]]))
    ln = np.zeros((NWw + 1, NX), dtype=np.int64)
    for e in range(NE): ln[W[e], enode[e]] += 1
    off = np.zeros((NWw + 1, NX), dtype=np.int64)
    for i in range(1, NWw + 1): off[i] = off[i - 1] + ln[i - 1]
    kinds = ["pre"] + [kinds_of_window(j) for j in range(NWw - 1)]
    pr("\n==== %s: head %s, word length %d (prefix + %d windows), per-node window non-monotone %d" % (label, hname, NWw, NWw - 1, nonmono))
    pr("  kinds: %s" % kinds)
    pr("  events per word index: %s" % [int(ln[i].sum()) for i in range(NWw)])
    R = {}
    # ---- BackChain (physical causes)
    bc = collections.Counter(); bcx = collections.Counter(); reach = collections.Counter(); bcw = collections.Counter()
    rtreach = collections.Counter(); rtx = collections.Counter()
    for e in range(NE):
        i = int(W[e])
        for alt in alts[e]:
            for q in alt:
                qn = enode[q]; rel = ek[q] - off[i, qn]
                reach[i - int(W[q])] += 1
                if i >= 1 and rel < -ln[i - 1, qn]:
                    bc["fail"] += 1; bcw[i] += 1
                    tag = "rst" if el[q][0] == RST else ("env" if el[q][0] in ENVN else "gate")
                    bcx[(tag, nm[el[e][0]], nm[el[q][0]], "first post-reset event" if ek[e] == 0 else "k=%d" % ek[e], i - int(W[q]))] += 1
        for q in rt.get(e, []):
            rtreach[i - int(W[q])] += 1
            if i >= 1 and int(W[q]) < i - 1: rtx[(nm[el[e][0]], nm[el[q][0]], "src last event" if ek[q] + 1 == cnt[el[q][0]] else "src k=%d" % ek[q])] += 1
    pr("  BackChain: physical cause reach (window(e)-window(cause) -> n) %s; violations %d at word indices %s" % (
        sorted(reach.items()), bc["fail"], dict(sorted(bcw.items()))))
    for k_, v_ in sorted(bcx.items(), key=lambda x: -x[1])[:12]: pr("     %s x%d" % (k_, v_))
    if len(bcx) > 12: pr("     ... %d distinct (tag, event node, cause node, which event, reach)" % len(bcx))
    tagc = collections.Counter()
    for k_, v_ in bcx.items(): tagc[k_[0]] += v_
    pr("     by cause tag: %s" % dict(tagc))
    pr("  [info, not BackChain] RT-edge (fc only) reach %s; RT edges reaching >= 2 back: %d (%d distinct (event node, source node, src))" % (
        sorted(rtreach.items()), sum(rtx.values()), len(rtx)))
    for k_, v_ in sorted(rtx.items(), key=lambda x: -x[1])[:6]: pr("     %s x%d" % (k_, v_))
    R["BackChain"] = bc["fail"]
    # ---- StChain + kind invariance of s0
    s0v = np.array([s0[n] for n in xs], dtype=bool)
    st = s0v[None, :] ^ (off[:NWw] % 2 == 1)
    Dmask = np.array([n in inD for n in xs])
    byk = collections.defaultdict(list)
    for i, kd in enumerate(kinds): byk[kd].append(i)
    stbad = collections.Counter(); stn = collections.Counter()
    for kd, js in byk.items():
        for j in js[1:]:
            d = np.nonzero((st[j] != st[js[0]]) & Dmask)[0]
            if len(d): stbad[(kd, js[0], j)] = len(d)
            for x in d: stn[nm[xs[x]]] += 1
    pr("  StChain (kind-invariant s0 on D nodes): %d window pairs of one kind disagree (kind, first window, window -> #nodes): %s" % (
        len(stbad), dict(list(stbad.items())[:10])))
    if stn: pr("     nodes: %s" % sorted(stn.items(), key=lambda x: -x[1])[:10])
    R["StChain"] = len(stbad)
    # ---- PairChain
    for Lname, LL in (("VC", Lvc), ("low", Llow)):
        pc = collections.Counter(); pcx = collections.Counter(); pcq = collections.Counter()
        for i in range(NWw - 1):
            for a in xs:
                ia = xi[a]
                if ln[i + 1, ia] == 0: continue
                e = eid[(a, int(off[i + 1, ia]))]
                for cc in partners[a]:
                    ic = xi[cc]
                    if LL[e, ic] - off[i + 1, ic] < -ln[i, ic]:
                        pc[i + 1] += 1
                        quiet = "c quiet in windows i,i+1" if ln[i, ic] + ln[i + 1, ic] == 0 else "c active"
                        pcq[quiet] += 1
                        pcx[(nm[a], nm[cc], quiet)] += 1
        pr("  PairChain [L=%s]: violations %d (by word index of w' %s); %s; distinct (a, c) %d" % (
            Lname, sum(pc.values()), dict(sorted(pc.items())), dict(pcq), len(pcx)))
        for k_, v_ in sorted(pcx.items(), key=lambda x: -x[1])[:6]: pr("     %s x%d" % (k_, v_))
        R["PairChain_" + Lname] = sum(pc.values())
    # ---- KindLStep (on wF: fc)
    for Lname, LL, clamp in (("VC", Lvc, False), ("low", Llow, False), ("VC, entries <= off_{i-1} clamped to none", Lvc, True)):
        if clamp:
            LL = LL.copy()
            for e in range(NE):
                i = int(W[e])
                if i >= 1:
                    m = LL[e] <= off[i - 1]; LL[e, m] = -10**9
        nf = 0; nfD = 0; fx = collections.Counter(); fwhy = collections.Counter(); fev = 0
        for e in range(NE):
            i = int(W[e]); u = enode[e]; L = LL[e]
            ok = np.zeros(NX, dtype=bool); ok[u] = True
            if i == 0: ok |= L <= 0
            p = prevE[e]
            if p is not None and (W[p] == i or (W[p] == i - 1 and i >= 1)):
                ok |= L <= LL[p]
            if ok.all(): continue
            F = fc(e)
            ok5 = np.ones(NX, dtype=bool)
            for alt in F:
                oa = np.zeros(NX, dtype=bool)
                for q in alt:
                    if int(W[q]) >= i - 1: oa |= L <= LL[q]      # q in this window or the previous one
                    oa[enode[q]] |= L[enode[q]] <= ek[q] + 1
                ok5 &= oa
            ok |= ok5
            bad = np.nonzero(~ok)[0]
            if len(bad):
                fev += 1; nf += len(bad); bD = [x for x in bad if xs[x] in partners[el[e][0]]]; nfD += len(bD)
                far = []
                if p is not None and W[p] < i - 1: far.append("prev event %d back" % (i - W[p]))
                for alt in F:
                    for q in alt:
                        if W[q] < i - 1:
                            far.append(("RT " if q in rt.get(e, []) and q not in alts[e][0] else "") +
                                       ("rst" if el[q][0] == RST else "cause") + " %d back" % (i - W[q]))
                why = ", ".join(sorted(set(far))) or "none >=2 back (bound attained via a chain)"
                if not F or any(len(a) == 0 for a in F): why += " [empty alternative]"
                fwhy[why] += len(bD)
                fx[(nm[el[e][0]], "k=%d" % ek[e], kinds[i] if i < len(kinds) else "?", why)] += len(bD)
        pr("  KindLStep [L=%s]: failing (event, c) entries %d at %d events; with c in D-partners of u: %d" % (Lname, nf, fev, nfD))
        for k_, v_ in sorted(fwhy.items(), key=lambda x: -x[1])[:8]: pr("     why (D-partner entries): %s x%d" % (k_, v_))
        for k_, v_ in sorted(fx.items(), key=lambda x: -x[1])[:6]: pr("     e.g. %s x%d" % (k_, v_))
        R["KindLStep_" + Lname] = (nf, nfD)
    # ---- KindRT / KindSub / KindNe
    rtbad = 0; rtw = collections.Counter()
    for W_, Us in rt.items():
        for U in Us:
            info = rtinfo.get((U, W_))
            if info is None or info[1] < 1: rtbad += 1
            rtw[int(W[W_]) - int(W[U])] += 1
    sub = sum(1 for e in range(NE) for aF in fc(e) if not any(all(q in aF for q in aP) for aP in alts[e]))
    ne = sum(1 for e in range(NE) if not fc(e))
    pr("  KindRT: RT edges %d, without a recorded Sep >= 1: %d (kind-relative sep entry window distance %s); KindSub violations %d; KindNe (empty fc) %d" % (
        sum(len(x) for x in rt.values()), rtbad, sorted(rtw.items()), sub, ne))
    R["KindRT"] = rtbad; R["KindSub"] = sub; R["KindNe"] = ne
    # ---- kind invariance (needed for one WKindF per kind)
    pr("  kind invariance (window vs first window of the same kind; relative coordinates):")
    for kd, js in sorted(byk.items(), key=str):
        if len(js) < 2: pr("     %s: windows %s (single)" % (kd, js)); continue
        j0 = js[0]
        for j in js[1:]:
            dl_ = [xs[x] for x in np.nonzero(ln[j] != ln[j0])[0]]
            dA = dF = dL = dLD = 0; nev = 0
            for x in np.nonzero((ln[j] == ln[j0]) & (ln[j] > 0))[0]:
                n = xs[x]
                for r in range(int(ln[j, x])):
                    e0 = eid[(n, int(off[j0, x]) + r)]; e1 = eid[(n, int(off[j, x]) + r)]; nev += 1
                    rel = lambda q, jj: (el[q][0], el[q][1] - int(off[jj, enode[q]]))
                    A0 = sorted(sorted(rel(q, j0) for q in a) for a in alts[e0]); A1 = sorted(sorted(rel(q, j) for q in a) for a in alts[e1])
                    if A0 != A1: dA += 1
                    F0 = sorted(sorted(rel(q, j0) for q in a) for a in fc(e0)); F1 = sorted(sorted(rel(q, j) for q in a) for a in fc(e1))
                    if F0 != F1: dF += 1
                    d = (Lvc[e0] - off[j0]) != (Lvc[e1] - off[j])
                    if d.any(): dL += 1
                    if any(d[xi[cc]] for cc in partners[n]): dLD += 1
            pr("     %s: w%d vs w%d: len differs at %d nodes %s; on %d events: causes differ %d, fc differ %d, Lr differ %d (on D-partners %d)" % (
                kd, j, j0, len(dl_), [nm[n] for n in dl_[:3]], nev, dA, dF, dL, dLD))
    return R

mk = main_kinds()
RES = {}
RES["main"] = run("MAIN granularity, kinds = (m, loop|exit)", "SLICE_X39Y21.C5", lambda j: mk[j] if j < len(mk) else "extra")
RES["main_it01"] = run("MAIN granularity, iterations 0,1 own kinds", "SLICE_X39Y21.C5",
                       lambda j: ("it%d" % j,) + mk[j] if j < 2 else (mk[j] if j < len(mk) else "extra"))
RES["main_prev"] = run("MAIN granularity, kind = (prev m, m, exit), iterations 0,1 own kinds", "SLICE_X39Y21.C5",
                       lambda j: ("it%d" % j,) + mk[j] if j < 2 else ((mk[j - 1][0],) + mk[j] if j < len(mk) else "extra"))
ik = inner_kinds()
if "--inner" in sys.argv:
    RES["inner"] = run("INNER granularity, kinds = (first|second|later, shift|exit)", "SLICE_X38Y51.B5", lambda j: ik[j] if j < len(ik) else "extra")
pr("\nSUMMARY %s" % RES)
open("/tmp/claude-0/winchk/winchk_c%d%s.txt" % (c, P), "w").write("\n".join(out) + "\n")
