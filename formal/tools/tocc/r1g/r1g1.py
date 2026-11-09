# r1g: trace the c=0 residue (X24Y76.D5 / X25Y76.B6 claims ending at X27Y80.A6(2)) in a datal pkl
import sys, pickle, collections
cc = sys.argv[1]; pk = sys.argv[2]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1g/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
D = pickle.load(open(pk, "rb")); M = D["MEMO"]
tgt = [k for k in M if (nm[k[0]] if isinstance(k[0], int) else "") in ("SLICE_X24Y76.D5", "SLICE_X25Y76.B6") and M[k].get("trunc") is not None]
print("truncated claims of the roots:", len(tgt))
for k in tgt[:4]:
    w = M[k]; print("\nKEY", nm[k[0]], k[1:], "A", s_(w["A"]), w["a"], "B", s_(w["B"]), w["b"], "trunc", s_(w["trunc"]), "restart", w.get("restart"))
    print("  phases", [(p, s_(b)) for p, b in w["phases"]])
    for t in D["TRUNC"]:
        if t[0] == k[0] and t[4] == w["trunc"]: print("  TRUNC", t[1], t[2], "c2.A", s_(t[3]), "c1.B", s_(t[4]), "c1.b", t[5], "c2.a", t[6], "sep", t[7]); break
    # follow covers whose B equals X27Y80.A6(2)
    seen = set(); stack = [(kk, 1) for u, kk in (w.get("cov") or []) if kk in M]
    while stack:
        kk, d = stack.pop()
        if kk in seen or d > 12: continue
        seen.add(kk); x = M[kk]
        if x["B"] is None or "X27Y80.A6" not in (s_(x["B"]) or ""): continue
        print("  " * d, nm[kk[0]], x["kind"], kk[1:4], "A", s_(x["A"]), x["a"], "B", s_(x["B"]), x["b"], "trunc", s_(x.get("trunc")), "rs", x.get("restart"))
        if x.get("phases"): print("  " * d, "   phases", [(p, s_(b)) for p, b in x["phases"]])
        stack += [(k2, d + 1) for u, k2 in (x.get("cov") or []) if k2 in M]
rs = [r for r in D["RSLOG"] if nm[r[0]] in ("SLICE_X24Y76.D5", "SLICE_X25Y76.B6")]
print("\nRSLOG accepted for roots:", len(rs)); print(D["stats"].get("latch restart tried (truncated claim ends before the needed end)"), D["stats"].get("latch restart accepted"))
