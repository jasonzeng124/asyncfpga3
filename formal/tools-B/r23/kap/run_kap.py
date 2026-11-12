"""run simadv with a classes JSON, then check SLICE_X22Y81.B5 (D of latch SLICE_X25Y76.B5) changes as read by the latch
while its enable (SLICE_X24Y77.A6, as read) is open, and the gap from each D change to the latch's next re-open read.
usage: run_kap.py PAIR KAPPA CORNER CLASSES CDEFAULT TAG  (appends to results.txt)"""
import sys, json, subprocess, os, pickle
from bisect import bisect_right
pair, kap, cor, cls, cdef, tag = sys.argv[1:7]
NET = "/tmp/claude-0/bsub1/tocc/net.json"; BND = "/tmp/claude-0/bsub1/tocc/bnd.json"
dump = "/tmp/claude-0/bsub1/kap/_d_%s.json" % tag
cmd = ["python3", "/tmp/claude-0/bsub1/kap/simadv.py", NET, BND, "--pairs", pair, "--corner", cor, "--kappa", kap,
       "--classes", cls, "--cdefault", cdef, "--data0", "--full", "--R", "400000", "--su", "1000", "--datachange", "broad",
       "--nextreq", "seq", "--tmax", os.environ.get("TMAX", "9000000"), "--w", "20", "--dump", dump]
r = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, KDEN="100"))
res = [l for l in r.stdout.splitlines() if l.startswith("RESULT")]
net = json.load(open(NET)); N = net["nodes"]; G = net["gates"]; idx = {n: i for i, n in enumerate(N)}
drv = {g["out"]: gi for gi, g in enumerate(G)}
CJ = json.load(open(cls)); ACL = {}; CLS = {}
for k in ("F", "S"):
    for x in CJ.get(k, []):
        if isinstance(x, list): ACL[(idx[x[0]], x[1])] = k
        else: CLS[idx[x]] = k
KD = 100; PK = round(float(kap) * KD); FMX, FMN = ("fmax", "fmin") if cor == "0" else ("smax", "smin")
def dly(gi, pin):
    g = G[gi]; e = g["arcs"][pin]; k = ACL.get((g["out"], pin), CLS.get(g["out"], cdef))
    if k == "S": return ((KD + PK) * e[FMX]) // KD
    if k == "F": return ((KD - PK) * e[FMN] + KD - 1) // KD
    return (e[FMN] + e[FMX]) // 2
def pindelay(v, src):
    g = G[drv[v]]
    for j, u in enumerate(g["ins"]):
        d = dly(drv[v], j); uu = u
        while uu in drv and G[drv[uu]]["k"] == 1 and G[drv[uu]]["init"] == 2: d += dly(drv[uu], 0); uu = G[drv[uu]]["ins"][0]
        if uu == src: return j, d
out = "NODUMP"
if os.path.exists(dump):
    D = json.load(open(dump)); H = {int(k): v for k, v in D["nodes"].items()}; os.unlink(dump)
    def val(n, t):
        if n not in H: return False
        b, ts = H[n]; return bool(b) ^ (bisect_right(ts, t) % 2 == 1)
    Q = idx["SLICE_X25Y76.B5"]; z = idx["SLICE_X22Y81.B5"]; en = idx["SLICE_X24Y77.A6"]
    sys.path.insert(0, "/tmp/claude-0/bsub1/tocc"); from classify import load
    C = load(); fb, enl = C["LATCH"][Q]; pe, act = enl[0]
    je, de = pindelay(Q, en); jd, dd = pindelay(Q, z)
    assert je == pe, (je, pe)
    zf = [x for x in (H[z][1] if z in H else []) if x > 400000]
    ef = [x for x in (H[en][1] if en in H else []) if x > 400000]
    opens = [x + de for x in ef if val(en, x) == bool(act)]
    rows = []; bad = 0
    for x in zf:
        tr = x + dd; isopen = val(en, tr - de) == bool(act)
        nxt = [o for o in opens if o > tr]
        rows.append((x, "OPEN" if isopen else "closed", (nxt[0] - tr) if nxt else None))
        bad += isopen
    qf = [x for x in (H[Q][1] if Q in H else []) if x > 400000]
    out = "D changes %d, read while OPEN %d; D-change -> next re-open read gaps %s; Q changes %d" % (len(zf), bad, [r_[2] for r_ in rows], len(qf))
line = "%-22s pair %-22s k=%s c=%s cdef=%s %s | %s" % (tag, pair, kap, cor, cdef, res[0] if res else "NORESULT rc=%d %s" % (r.returncode, r.stderr[-200:].replace("\n", " ")), out)
open("/tmp/claude-0/bsub1/kap/results.txt", "a").write(line + "\n"); print(line)
