import sys, os, pickle
cc = sys.argv[1]; pk = sys.argv[2]; NODES = sys.argv[3].split(",")
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/race/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
D = pickle.load(open(pk, "rb")); M = D["MEMO"]
for k, v in M.items():
    if nm[k[0]] in NODES:
        print(nm[k[0]], k[1:], v["kind"], "A", s_(v["A"]), v["a"], "B", s_(v["B"]), v["b"], "bad" if v["bad"] else "", v.get("phases"))
        for u, kk in (v.get("cov") or [])[:8]:
            w = M.get(kk)
            if w: print("    cov", nm[u], kk[1:3], w["kind"], "A", s_(w["A"]), w["a"], "B", s_(w["B"]), w["b"], "bad" if w["bad"] else "")
for k, m, det in D["OBL"]:
    if m < 0: print("OBL", k, m, det if isinstance(det, str) else (det[0], s_(det[1]), s_(det[2])))
