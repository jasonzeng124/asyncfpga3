import sys, os, pickle, collections
os.environ["UPREL"] = "1"
c_ = sys.argv[1]; pk = sys.argv[2]; sys.argv = ["ao.py", c_, "0"]
src = open("/tmp/claude-0/bsub1/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
P = pickle.load(open(pk, "rb")); seen = set(); R = collections.Counter(); ex = []
for tr in P["TRUNC"]:
    c1, c2 = tr["c1"], tr["c2"]; k = (tr["Q"], tr["kind"], c1["B"], c2["A"])
    if k in seen or tr["kind"] != "U->H": continue
    seen.add(k); B_, A_ = c1["B"], c2["A"]
    if not leqP(B_, A_): R["B: unordered"] += 1; continue
    if c2["a"] < 1: R["a<1"] += 1; continue
    U = up_from(B_, int(tm[A_]))
    if A_ not in U: R["A: no Up"] += 1; ex.append((nm[tr["Q"]], "noUp")); continue
    m = c1["b"] - c2["a"] - U[A_]
    R["A: Up too large" if m < 0 else "A: Up OK?!"] += 1
    if len(ex) < 12: ex.append((nm[tr["Q"]], el[B_][2], el[A_][2], c1["b"], c2["a"], U[A_], m))
print(R); print(ex)
