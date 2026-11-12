import sys, os, collections
c_ = sys.argv[1]
sys.argv = ["datal.py", c_]
os.environ["NPASS"] = "1"
src = open("/tmp/claude-0/arbh/datal.py").read(); src = src[:src.index("# ---------------- loop covers")]
exec(src)
need = collections.defaultdict(list)
for x in G_:
    if len(x) != 7: continue
    v, z, ms, me, cz, st, en_ = x
    if me >= 0 or en_ is None: continue
    E = eid[en_]
    for u, k2 in cz.get("cov", []):
        w = memo.get(k2)
        if isinstance(w, dict) and w["B"] is not None and sep(E, w["B"]) == NEG:
            need[(E, w["B"])].append((nm[v], nm[z], nm[u]))
print("[c=%s%s] distinct (E, pin-end) pairs lacking an order: %d" % (c_, os.environ.get("PAIR",""), len(need)))
for (E, B), lst in sorted(need.items(), key=lambda kv: -len(kv[1]))[:12]:
    f4, e0 = form4(E, B, 60)
    print("  E=%s(%d)@%d  B=%s(%d)@%d  gap %+d ps  E<=B causally %s  form-iv(60 ancestors) %s  [%d guards, e.g. %s]" % (
        nm[el[E][0]], el[E][1], et[E], nm[el[B][0]], el[B][1], et[B], et[B] - et[E], bool(leqP(E, B)), f4, len(lst), lst[0]))
