# r1h counterfactual (NOT in the builder): for every truncation whose c1.B = B (select re-open), does an UPPER bound
# Up(B -> c2.A) = u with c2.a + u <= c1.b exist?  (the UnionUp join; needs a Lean ChainOK alternative, see RESULTS)
import sys, pickle, collections, os
cc = sys.argv[1]; pk = sys.argv[2]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1h/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
os.environ.setdefault("REL", "1"); os.environ.setdefault("RELD", "99"); os.environ.setdefault("RELK", "16"); os.environ.setdefault("RELTRY", "64")
exec(open("/tmp/claude-0/r1h/relup.py").read())
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
D = pickle.load(open(pk, "rb"))
B = [e for e in range(NE) if nm[el[e][0]] == "SLICE_X27Y80.A6" and el[e][1] == 2][0]
rows = {}
for t in D["TRUNC"]:
    if t[4] != B or t[3] is None: continue
    k = (t[0], t[1], t[2], t[3]); r = rows.get(k)
    if r is None or t[5] - t[6] < r[0]: rows[k] = (t[5] - t[6], t)
res = collections.Counter(); out = []
upc = {}
for k, (need, t) in rows.items():
    A2 = t[3]
    if A2 not in upc:
        u0 = up_get(B, A2, 0); u9 = up_get(B, A2, RELD)
        upc[A2] = (u0, u9)
    u0, u9 = upc[A2]
    u = min([x for x in (u0, u9) if x is not None], default=None)
    ok = u is not None and u <= need
    res[("Up exists" if u is not None else "no Up", "join passes" if ok else "fails")] += 1
    out.append((nm[t[0]], t[1], t[2], s_(A2), need, u0, u9, int(et[A2] - et[B])))
print("distinct truncations with c1.B = B:", len(rows), dict(res))
for A2, (u0, u9) in sorted(upc.items(), key=lambda x: et[x[0]]): print("  Up(B ->", s_(A2), ") depth0", u0, "rel", u9, "sim dt", int(et[A2] - et[B]))
for r in sorted(out, key=lambda r: r[4])[:10]: print("  tightest", r)
