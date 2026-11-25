# debug: build the latch claim of Q at its value interval containing time T and print the chain and the D claims
import sys, os
QN = sys.argv[2]; TT = int(sys.argv[3])
src = open("/tmp/claude-0/race/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
Q = [n for n in g if nm[n] == QN][0]
def show(n, t, d=0, maxd=4):
    pass
cl = claim(Q, TT)
print("Q", QN, {k: (s_(v) if k in ("A", "B") else v) for k, v in cl.items() if k not in ("cov",)})
for k_, v_ in memo.items():
    if isinstance(v_, dict) and d_ != None if False else isinstance(v_, dict):
        print("  memo", nm[k_[0]], k_[1:3], "A", s_(v_["A"]), v_["a"], "B", s_(v_["B"]), v_["b"], v_["kind"], "bad" if v_.get("bad") else "", [ (nm[u], kk[1:3] if kk else None) for u, kk in v_.get("cov", [])][:4])
for t in TRUNC: print("TRUNC", nm[t[0]], t[1], t[2], s_(t[3]), s_(t[4]), t[5:])
for k, m, det in OBL:
    if m < 0: print("OBL", k, m, det if isinstance(det, str) else det[0])
print("stats", {k: v for k, v in stats.items() if "anchor" in k})
for k, m, det in OBLTRIAL:
    if m < 0: print("TRIALOBL", k, m, det if isinstance(det, str) else det[0])
for k_, v_ in memo.items():
    if isinstance(v_, dict) and nm[k_[0]] in os.environ.get("SHOW", "").split(","):
        print("  SHOW", nm[k_[0]], k_[1:3], "A", s_(v_["A"]), v_["a"], "B", s_(v_["B"]), v_["b"], v_["kind"], "bad" if v_.get("bad") else "", [(nm[u], kk[1:3] if kk else None) for u, kk in v_.get("cov", [])][:6])
OPEN = [e for e in range(NE) if s_(e).startswith(os.environ.get("OPENEV", "SLICE_X30Y76.A6(0)@"))]
if OPEN:
    o = OPEN[0]
    for k_, v_ in memo.items():
        if isinstance(v_, dict) and v_["A"] == o:
            ca = [memo.get(kk) for u, kk in v_.get("cov", [])]
            ca = [(nm[u], s_(memo[kk]["A"]) if kk in memo and memo[kk]["A"] is not None else None, memo[kk]["a"] if kk in memo else None) for u, kk in v_.get("cov", [])]
            if all(x[1] is None or not x[1].startswith(os.environ.get("OPENEV", "SLICE_X30Y76.A6(0)@")) for x in ca):
                print("ORIGIN", nm[k_[0]], k_[1:3], v_["kind"], v_["a"], ca, "ex pins:", [nm[p["src"]] for p in g[k_[0]]["pins"] if p["live"] and p["src"] in EX] if k_[0] in g else None)
