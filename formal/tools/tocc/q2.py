#!/usr/bin/env python3
"""Shard C (UNTRUSTED): which lowered per-reader L entries (= failing TO rows) are NEEDED by the reader's local
check, and the residual failures with no L lowered.  usage: q2.py c [suffix-flags...]   (uses ao2 pickles)"""
import sys, pickle, collections
c = sys.argv[1]; extra = sys.argv[2:]
sys.argv = ["ao.py", c, "0", "--prevanc"] + extra
src = open("/tmp/claude-0/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
suf = "_prevanc" + ("_deep" if DEEP else "") + ("_bcp" if BCP else "") + ("_cyc" if CYC else "") + ("_causeanc" if CAUSEANC else "")
P = pickle.load(open("/tmp/claude-0/tocc/ao_c%s%s.pkl" % (c, suf), "rb")); rt = P["rt"]
VC = vclock(rt)
def reader_rows(v):
    D = Dof(v); over = {}; rows = []
    if v in envnode: return D, over, rows
    for a in D:
        for b in D:
            if a == b: continue
            need = (hi_(v, b) if (v, b) in dl else 1) - (lo_(v, a) if (v, a) in dl else 1)
            if need <= 0: continue
            for k in range(len(ev[a])):
                mm = int(VC[eid[(a, k)], xi[b]])
                if mm == 0: continue
                def passes(mm):
                    if a == v:
                        for k2 in range(k + 1):
                            if all(any(el[p][0] == b and mm <= el[p][1] + 1 for p in alt) for alt in alts[eid[(v, k2)]]):
                                return "ex", None
                    s, _ = sepAny(eid[(b, mm - 1)], eid[(a, k)])
                    return ("ok" if s >= need else "fail"), s
                r, s = passes(mm)
                if r != "fail": continue
                m2 = mm - 1
                while m2 > 0 and passes(m2)[0] == "fail": m2 -= 1
                over[(a, k, b)] = m2; rows.append((s - need, a, k, b, mm - 1, s, need))
    return D, over, rows
def fails_with(v, over):
    Lv = lambda a, k, b: min(int(VC[eid[(a, k)], xi[b]]), over.get((a, k, b), 99))
    D, nv_, out = check(v, Lv)
    return [(kind, nn) for kind, nn in out if not kind.endswith("~")]
freaders = sorted(set(f[0] for f in P["fails"]))
allreaders = sorted(v for v in EX if v not in envnode)
needed = []; harmless = 0; nrows = 0; resid = []
for v in allreaders:
    D, over, rows = reader_rows(v)
    base = fails_with(v, {})
    resid += [(v, k_, n_, D) for k_, n_ in base]
    if not rows: continue
    nrows += len(rows)
    if v not in freaders: harmless += len(rows); continue
    bset = set(base)
    for r in rows:
        key = (r[1], r[2], r[3])
        f1 = [x for x in fails_with(v, {key: over[key]}) if x not in bset]
        if f1: needed.append((v, r, f1))
        else: harmless += 1
print("[c=%s %s] failing TO rows %d: NOT needed by the reader's local check (lowering alone causes no failure) %d; needed %d at %d readers" % (
    c, suf, nrows, harmless, len(needed), len(set(x[0] for x in needed))))
cat = collections.Counter(("a=v" if x[1][1] == x[0] else "a!=v") for x in needed)
print("  needed rows by kind:", dict(cat), "; margins (worst 5):", sorted(round(x[1][0]) for x in needed)[:5])
print("  needed rows by b (top 6):", [(nm[b], n) for b, n in collections.Counter(x[1][3] for x in needed).most_common(6)])
for v, r, f1 in sorted(needed, key=lambda x: x[1][0])[:6]:
    m_, a, k, b, mb, s, need = r
    print("   v=%s a=%s(%d) b=%s(%d) Sep=%s need=%d margin=%s -> new failures %s" % (nm[v], nm[a], k, nm[b], mb, s, need, m_, f1[:3]))
print("  residual failures with NO L lowered: %d %s at %d nodes" % (len(resid), dict(collections.Counter(x[1] for x in resid)), len(set(x[0] for x in resid))))
pickle.dump(dict(needed=needed, resid=resid), open("/tmp/claude-0/tocc/q2_c%s%s.pkl" % (c, suf), "wb"))
