import sys, os, collections
c_ = sys.argv[1]
sys.argv = ["datal.py", c_]
os.environ["NPASS"] = "1"
src = open("/tmp/claude-0/arbh/datal.py").read(); src = src[:src.index("# ---------------- loop covers")]
exec(src)
roots = collections.defaultdict(set); gaps = {}
nfail = 0
for x in G_:
    if len(x) != 7: continue
    v, z, ms, me, cz, st, en_ = x
    if min(ms, me) >= 0: continue
    nfail += 1
    if en_ is None or me >= 0: roots[("start-side", None)].add(id(x)); continue
    E = eid[en_]
    # leaves: offending claims whose covers are all fine (or none): their own B is the root end event
    stack = [cz["key"]]; seen = set()
    while stack:
        k = stack.pop()
        if k in seen: continue
        seen.add(k)
        w = memo.get(k)
        if not isinstance(w, dict) or w["B"] is None or sep(E, w["B"]) != NEG: continue
        bad_kids = [k2 for u, k2 in w.get("cov", []) if k2 is not None and isinstance(memo.get(k2), dict) and memo[k2]["B"] == w["B"]]
        if bad_kids: stack += bad_kids
        else:
            B = w["B"]; roots[B].add(id(x)); gaps[B] = (int(et[B] - et[E]), nm[v], nm[z], nm[el[E][0]], el[E][1], nm[k[0]], w["kind"], w.get("phases", [])[-1:] )
print("[c=%s%s] failing guards %d; root end events (an event that ends a claim and is not ordered after the reader's E):" % (c_, os.environ.get("PAIR", ""), nfail))
for B, gs in sorted(roots.items(), key=lambda kv: -len(kv[1])):
    if B == ("start-side", None): print("   %3d guards: start-side failure" % len(gs)); continue
    gp, vn, zn, en, ek, owner, kind, ph = gaps[B]
    f4 = form4(eid[(el[B][0], el[B][1])], eid[(el[B][0], el[B][1])]) if False else None
    f4 = form4(eid[(el[B][0], el[B][1])] if False else None, None) if False else None
    print("   %3d guards: %s(%d)@%d, sim gap after E %+d ps, ends claim of %s (%s %s), e.g. reader %s z %s E=%s(%d)" % (len(gs), nm[el[B][0]], el[B][1], el[B][2], gp, owner, kind, ph, vn, zn, en, ek))
