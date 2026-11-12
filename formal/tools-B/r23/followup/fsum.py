#!/usr/bin/env python3
"""bsub1 follow-up (UNTRUSTED): summarize datal_t pickles: failing guards, truncations by kind and class, joins by form.
usage: fsum.py c TAG=PKL ...   (run in tocc/ or tocc175/; classes: A = c1.B causally before c2.A, B = unordered,
C = H->U' with c1.B = c2.A (finite shortfall), O = other)"""
import sys, os, pickle, collections
c_ = sys.argv[1]; args = sys.argv[2:]
HERE = os.path.dirname(os.path.abspath(__file__))
sys.argv = ["ao.py", c_, "0"]
src = open(os.path.join(HERE, "ao.py")).read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
for a in args:
    tag, pk = a.split("=", 1)
    P = pickle.load(open(pk, "rb")); st = P["stats"]
    nf = sum(1 for x in P["G"] if len(x) == 7 and min(x[2], x[3]) < 0)
    seen = {}
    for tr in P["TRUNC"]:
        if tr["suppressed"]: continue
        k = (tr["Q"], tr["kind"], tr["c1"]["B"], tr["c2"]["A"])
        if k in seen: continue
        B_, A_ = tr["c1"]["B"], tr["c2"]["A"]
        if B_ == A_: cl = "C"
        elif leqP(B_, A_): cl = "A"
        elif leqP(A_, B_): cl = "O(c2.A<=c1.B, Sep short)"
        else: cl = "B"
        seen[k] = cl
    tk = {k.split("(")[-1].rstrip(")"): v for k, v in st.items() if k.startswith("latch claim truncated")}
    jn = {k.replace("link joined by ", ""): v for k, v in st.items() if k.startswith("link joined")}
    print("%-12s c=%s failing guards %3d/%d | truncated claim builds %s | joins %s" % (tag, c_, nf, len(P["G"]), tk, jn))
    print("             distinct truncation events by (kind, class):", dict(sorted(collections.Counter((k[1], v) for k, v in seen.items()).items())))
