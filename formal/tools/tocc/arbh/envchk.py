"""Compare an adversarial run with the reference run (UNTRUSTED). usage: envchk.py ref.pkl test.pkl [...]
Per test run: gcd right?, hazchk data-driven control changes, exact nodes whose event count differs from the reference,
failing-guard intervals (from r1b_c<c>.pkl) in which z AS READ by v changes, and the order of the R1 pairs."""
import sys, pickle, math, collections
sys.path.insert(0, "/tmp/claude-0/arbh")
from hazchk import check, C
nm = C["names"]; idn = {x: i for i, x in enumerate(nm)}; g = C["gates"]
def evs(H, n):
    R = H["R"]; return [x for x in (H["hist"][n][1] if n in H["hist"] else []) if x > R - 1]
def flips(H, n): return H["hist"][n][1] if n in H["hist"] else []
def delay(H, v, u):
    if v not in g: return 0
    for j, p in enumerate(g[v]["pins"]):
        if p["src"] == u: return H["DS"][v][j]
    return 0
EXTRA = [(("SLICE_X39Y47.D6", 1), ("SLICE_X30Y76.A6", 2)), (("SLICE_X34Y45.A5", 1), ("SLICE_X30Y76.A6", 2))]
def run(ref, fn):
    H = pickle.load(open(fn, "rb")); _, hz = check(fn)
    c = H["c"]; Rb = pickle.load(open("/tmp/claude-0/arbh/r1b_c%d.pkl" % c, "rb"))
    gcd_ok = H["res"] == [math.gcd(H["A"], H["B"])]
    diff = [n for n in C["EXACT"] if len(evs(H, n)) != len(evs(ref, n))]
    def T(H_, nk):
        n = idn[nk[0]]; e = evs(H_, n); return e[nk[1]] if nk[1] < len(e) else None
    zchg = 0; zchg_ex = []; flip = 0; flip_ex = []
    for (v, z, st, en_, first, fu) in Rb["rows"]:
        vi, zi = idn[v], idn[z]
        tS = T(H, st); tE = T(H, en_)
        if tS is None or tE is None: continue
        a = tS + delay(H, vi, idn[st[0]]) - delay(H, vi, zi); b = tE + delay(H, vi, idn[en_[0]]) - delay(H, vi, zi)
        n = sum(1 for x in flips(H, zi) if a <= x <= b)
        if n: zchg += 1; zchg_ex.append((v, z, st, en_, n))
        if first:
            tR = T(H, first[:2])
            if tR is not None and tR < tE: flip += 1; flip_ex.append((v, en_, first[:2], tE - tR))
    xo = []
    if c == 1:
        for E_, B_ in EXTRA:
            tE = T(H, E_); tB = T(H, B_); xo.append((tB - tE) if tE is not None and tB is not None else None)
    return dict(fn=fn, c=c, res=H["res"], ok=gcd_ok, hz=len(hz), hzex=hz[:3], ndiff=len(diff), diffex=[nm[n] for n in diff[:4]],
                zchg=zchg, zchg_ex=zchg_ex[:3], flip=flip, flip_ex=flip_ex[:3], extra=xo, tend=H["tend"], ENVD=H.get("ENVD"), ADV=H.get("ADV"))
if __name__ == "__main__":
    ref = pickle.load(open(sys.argv[1], "rb"))
    for fn in sys.argv[2:]:
        r = run(ref, fn)
        print("%-40s c=%d out %s ok=%s hazards=%d exact-nodes-with-different-event-count=%d %s | guards with z change inside the read window %d %s | first-reopen-before-E %d %s | R1-root gaps (reopen - E) %s | tend %d" % (
            fn.split("/")[-1], r["c"], r["res"], r["ok"], r["hz"], r["ndiff"], r["diffex"], r["zchg"], r["zchg_ex"], r["flip"], r["flip_ex"], r["extra"], r["tend"]), flush=True)
