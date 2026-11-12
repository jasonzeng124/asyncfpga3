# r1f2: memo claims + TRUNC + U->H obligations of the two latches and of X35Y91.B5, X34Y89.D6, X32Y92.D6 (final pkl)
import sys, pickle
cc = sys.argv[1]; pk = sys.argv[2]; EXTRA = sys.argv[3:]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1f/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
D = pickle.load(open(pk, "rb")); M = D["MEMO"]
T = set(EXTRA) if EXTRA else {"SLICE_X35Y91.B6", "SLICE_X34Y91.C5", "SLICE_X35Y91.B5", "SLICE_X34Y89.D6", "SLICE_X32Y92.D6"}
for k, w in M.items():
    if nm[k[0]] in T:
        print(nm[k[0]], k[1:], "A", s_(w["A"]), w["a"], "B", s_(w["B"]), w["b"], w["kind"], "bad", w["bad"], "trunc", s_(w["trunc"]),
              "ph", [(p, s_(b)) for p, b in (w.get("phases") or [])], "cov", [(nm[u], kk[1:3]) for u, kk in (w.get("cov") or [])][:4])
for t in D["TRUNC"]:
    if nm[t[0]] in T: print("TRUNC", nm[t[0]], t[1], t[2], "c2.A", s_(t[3]), "c1.B", s_(t[4]), "b", t[5], "a", t[6], "d", t[7])
for k, m, x in D["OBL"]:
    if isinstance(x, tuple) and x and x[0] in T and "ChainOK" in k: print("OBL", k[:20], m, x[0], s_(x[1]) if isinstance(x[1], (int, np.integer)) else x[1], s_(x[2]) if len(x) > 2 and isinstance(x[2], (int, np.integer)) else "")
