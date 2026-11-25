# Shard C (UNTRUSTED).  exec'd at the end of datal.py.  Emits the Sep/Up entries behind every guard's GuardTime and
# re-checks the emitted tables, keyed by (node name, event index), against a transcription of DecT.lean:
# upFormB (incl. upRelB, the relative clause) and sepFormB (forms i-iv), with first-match lookup replaced by unique keys
# (the emitter keeps one value per key: Up the smallest, Sep the largest, each with its own justification).
import time as _time
_t = _time.time()
for x in G_:
    if len(x) != 7: continue
    v, z, ms, me, cz, st, en_ = x
    S = eid[st]; E = eid[en_] if en_ else None
    if cz["A"] is not None and ms > NEG: emit_sepq(cz["A"], S)
    if cz["B"] is not None and E is not None and me > NEG:
        if (v, z, st, en_) in RELG: CURD[0] = RELD
        emit_sepq(E, cz["B"]); CURD[0] = 0
for (A_, B_) in sorted(globals().get("RELU", ())):
    CURD[0] = RELD; emit_sepq(A_, B_); CURD[0] = 0
K = lambda e: (nm[el[e][0]], el[e][1])
UPN = {(K(a), K(b)): d for (a, b), d in UPT.items()}
SEPN = {(K(a), K(b)): d for (a, b), d in SEPT.items()}
CAUS = {K(e): [[K(p) for p in alt] for alt in alts[e]] for e in range(NE)}
TMN = {K(e): int(tm[e]) for e in range(NE)}
NODE = {nm[n]: n for n in EX}
LEN = {nm[n]: len(ev[n]) for n in EX}
UPBYT = collections.defaultdict(list)
for (a, p), dA in UPN.items(): UPBYT[p].append((a, dA))
SEPBYT = collections.defaultdict(list)
for (b, a), d in SEPN.items(): SEPBYT[a].append((b, d))
def H(vn, wn): return whi(NODE[vn], NODE[wn])
def Lo(vn, wn): return wlo(NODE[vn], NODE[wn])
def upRel(e0, p, h, d):
    for a, dA in UPBYT.get(p, ()):
        dS = SEPN.get((a, e0))
        if dS is not None and dA + h <= d + dS: return True
    return False
def pcl(e0, p, h, d, which):
    dp = UPN.get((e0, p))
    if dp is not None and dp + h <= d: which["U"] += 1; return True
    if (p, e0) in SEPN and h <= d: which["S"] += 1; return True
    if upRel(e0, p, h, d): which["R"] += 1; return True
    return False
def upForm(e0, e, d, which):
    if e == e0: return True
    vn, k = e; v = NODE[vn]
    if v in envnode or v not in g or v in DATA or not k < LEN[vn]: return False
    if not any(all(pcl(e0, p, H(vn, p[0]), d, which) for p in alt) for alt in CAUS[e]): return False
    if k == 0: return True
    return pcl(e0, (vn, k - 1), H(vn, vn), d, which)
def sepForm(b, a, d):
    if b == a and d == 0: return True
    an, k = a
    if all(any((b, p) in SEPN and d <= SEPN[(b, p)] + Lo(an, p[0]) for p in alt) for alt in CAUS[a]): return True
    if k > 0 and (b, (an, k - 1)) in SEPN and d <= SEPN[(b, (an, k - 1))] + Lo(an, an): return True
    if d >= 1:
        for e0, dl in SEPBYT.get(a, ()):
            du = UPN.get((e0, b))
            if du is not None and d + du <= dl and TMN[e0] < TMN[b]: return True
    return False
which = collections.Counter(); upbad = []; sepbad = []
for (e0, e), d in UPN.items():
    if d < 0 or not upForm(e0, e, d, which): upbad.append((e0, e, d))
for (b, a), d in SEPN.items():
    if not a[1] < LEN[a[0]]: continue          # sepB: vacuous for k >= len
    if d < 0 or not sepForm(b, a, d): sepbad.append((b, a, d))
# GuardTime (TimedOccX.lean) with the emitted Sep, and the guard verdicts
gt_fail = 0; gt_mismatch = 0; GTRES = []
for x in G_:
    if len(x) != 7: GTRES.append(False); continue
    v, z, ms, me, cz, st, en_ = x
    ok = True
    if cz["A"] is not None:
        d = SEPN.get((K(cz["A"]), (nm[st[0]], st[1])))
        ok &= d is not None and pwin(v, z)[1] + cz["a"] <= lo_(v, st[0]) + d
    if cz["B"] is not None:
        d = SEPN.get(((nm[en_[0]], en_[1]), K(cz["B"]))) if en_ else None
        ok &= d is not None and hi_(v, en_[0]) <= pwin(v, z)[0] + cz["b"] + d
    GTRES.append(ok)
    if not ok: gt_fail += 1
    if ok != (min(ms, me) >= 0): gt_mismatch += 1
urel = sum(1 for j in UPJ.values() if j[0] == "alt" and any(t[0] == "R" for t in list(j[2]) + ([j[3]] if j[3] else [])))
print("[lchk] emitted Up entries %d (distinct e0 %d, entries using the relative clause %d), Sep entries %d (form iv %d); %.0fs" % (
    len(UPN), len(set(a for a, b in UPN)), urel, len(SEPN), sum(1 for j in SEPJ.values() if j[0] == "iv"), _time.time() - _t))
print("[lchk] upFormB failures %d, sepFormB failures %d; clauses used by causes/prev %s" % (len(upbad), len(sepbad), dict(which)))
print("[lchk] GuardTime with emitted tables: failed %d of %d (mismatch with datal's margin verdict: %d)" % (gt_fail, len(G_), gt_mismatch))
print("[lchk] relup stats %s; Up tables built %d (by depth %s)" % (dict(RELSTAT), len(UPST), dict(collections.Counter(k[1] for k in UPST))))
for u in upbad[:5]: print("   upbad", u)
for s_ in sepbad[:5]: print("   sepbad", s_)
