import sys, pickle
cc = sys.argv[1]; pk = sys.argv[2]; names = sys.argv[3].split(",")
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/r1g/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
D = pickle.load(open(pk, "rb")); M = D["MEMO"]
for k, x in M.items():
    if not isinstance(k[0], int) or nm[k[0]] not in names: continue
    print(nm[k[0]], x["kind"], k[1:], "A", s_(x["A"]), x["a"], "B", s_(x["B"]), x["b"], "trunc", s_(x.get("trunc")), "rs", x.get("restart"))
    if x.get("phases"): print("   phases", [(p, s_(b)) for p, b in x["phases"]])
    print("   cov", [(nm[k2[0]] if isinstance(k2[0], int) else k2, s_(M[k2]["A"]) if k2 in M else None, s_(M[k2]["B"]) if k2 in M else None, M[k2]["b"] if k2 in M else None) for u, k2 in (x.get("cov") or [])][:8])
for t in D["TRUNC"]:
    if nm[t[0]] in names: print("TRUNC", nm[t[0]], t[1], t[2], s_(t[3]), s_(t[4]), t[5], t[6], t[7])
