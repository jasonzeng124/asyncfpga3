import sys, pickle, collections, os
c_ = sys.argv[1]; mode = sys.argv[2]
sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
PS = os.environ.get("PAIR", "")
P = pickle.load(open("/tmp/claude-0/race/ao_c%s_prevanc_cyc_causeanc_dcp%s.pkl" % (c_, PS), "rb")); rt = P["rt"]
VC = vclock(rt)
def row_ok(v, a, k, b, mm, need):
    if mm == 0: return True
    if a == v:
        for k2 in range(k + 1):
            if all(any(el[p][0] == b and mm <= el[p][1] + 1 for p in alt) for alt in alts[eid[(v, k2)]]): return True
    s, _ = sepAny(eid[(b, mm - 1)], eid[(a, k)])
    return s >= need
if mode == "over":
    overs = {}
    for v in sorted(EX):
        if v in envnode: continue
        D = Dof(v); over = {}
        for a in D:
            for b in D:
                if a == b: continue
                need = (hi_(v, b) if (v, b) in dl else 1) - (lo_(v, a) if (v, a) in dl else 1)
                if need <= 0: continue
                for k in range(len(ev[a])):
                    mm = int(VC[eid[(a, k)], xi[b]])
                    if mm == 0 or row_ok(v, a, k, b, mm, need): continue
                    m2 = mm - 1
                    while m2 > 0 and not row_ok(v, a, k, b, m2, need): m2 -= 1
                    over[(a, k, b)] = m2
        if over: overs[v] = over
    pickle.dump(overs, open("/tmp/claude-0/race/overs_c%s%s.pkl" % (c_, PS), "wb"))
    print("[c=%s] readers with lowered entries %d, entries %d" % (c_, len(overs), sum(len(o) for o in overs.values())))
else:
    O = [pickle.load(open("/tmp/claude-0/race/overs_c%d%s.pkl" % (cc, PS), "rb")) for cc in (0, 1)]
    nfail = 0; nrow = 0; rfail = 0; nent = 0
    for v in sorted(EX):
        over = {}
        for o in O:
            for key, val in o.get(v, {}).items(): over[key] = min(val, over.get(key, 99))
        nent += len(over)
        Lv = lambda a, k, b: min(int(VC[eid[(a, k)], xi[b]]), over.get((a, k, b), 99))
        D, nv_, out = check(v, Lv)
        nfail += sum(1 for kind, nn in out if not kind.endswith("~"))
        if v in envnode: continue
        for a in D:
            for b in D:
                if a == b: continue
                need = (hi_(v, b) if (v, b) in dl else 1) - (lo_(v, a) if (v, a) in dl else 1)
                if need <= 0: continue
                for k in range(len(ev[a])):
                    mm = Lv(a, k, b)
                    if mm == 0: continue
                    nrow += 1
                    if not row_ok(v, a, k, b, mm, need): rfail += 1
    print("[c=%s] union-lowered L (min over both corners, %d entries): LCheckXA failures %d; TOA rows with L > 0 %d, failing at this corner %d" % (c_, nent, nfail, nrow, rfail))
