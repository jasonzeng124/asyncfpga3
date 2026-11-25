"""arbh hold-race outcome of one run (UNTRUSTED): gcd, hazchk, exact event-count diffs vs the mid run, and for the latches
X36Y63.B6, X36Y68.B6, X37Y47.B6, X36Y69.B6 (D = X39Y53.B6): per close of the enable (as read by the latch), the value held
through the closed phase, the slack (next D change as read by the latch) - (close as read), and the held-value sequence /
latch output history vs the reference."""
import sys, pickle, math, bisect
sys.path.insert(0, "/tmp/claude-0/arbh")
from hazchk import check, C
nm = C["names"]; idn = {x: i for i, x in enumerate(nm)}; g = C["gates"]
LAT = {"SLICE_X36Y63.B6": "SLICE_X36Y63.A6", "SLICE_X36Y68.B6": "SLICE_X36Y68.A6", "SLICE_X37Y47.B6": "SLICE_X37Y47.A6", "SLICE_X36Y69.B6": "SLICE_X36Y69.A6"}
Dn = "SLICE_X39Y53.B6"
def ev(H, x):
    n = idn[x]; R = H["R"]; return [t for t in (H["hist"][n][1] if n in H["hist"] else []) if t > R - 1]
def pin(H, v, u):
    for j, p in enumerate(g[idn[v]]["pins"]):
        if p["src"] == idn[u]: return H["DS"][idn[v]][j]
def val(H, x, t):
    n = idn[x]
    if n not in H["hist"]: return False
    b, ts = H["hist"][n]; return b ^ (bisect.bisect_right(ts, t) % 2 == 1)
def latchinfo(H):
    out = {}; minsl = None; bad = []
    for Q, en in LAT.items():
        dE = pin(H, Q, en); dD = pin(H, Q, Dn); E = ev(H, en); D = ev(H, Dn)
        held = []
        for i, t in enumerate(E):
            if val(H, en, t): continue          # opening
            tc = t + dE; tn = (E[i + 1] + dE) if i + 1 < len(E) else 10**15
            dv = val(H, Dn, tc - dD)
            q = [val(H, Q, x) for x in [tc + 400] + [x for x in ev(H, Q) if tc < x < tn]]   # Q through the closed phase
            nxt = [x + dD for x in D if x + dD > tc]
            sl = (nxt[0] - tc) if nxt else None
            if sl is not None and (minsl is None or sl < minsl[0]): minsl = (sl, Q, i)
            if any(v != dv for v in q): bad.append((Q, i, dv))
            held.append(int(dv))
        out[Q] = (held, len(ev(H, Q)))
    return out, minsl, bad
def run(fn, ref=None):
    H = pickle.load(open(fn, "rb")); _, hz = check(fn)
    li, minsl, bad = latchinfo(H)
    r = dict(res=H["res"], ok=H["res"] == [math.gcd(H["A"], H["B"])], timeout=H["tend"] > 49_000_000, hz=len(hz), minslack=minsl, holdbad=bad[:4], nD=len(ev(H, Dn)))
    if ref:
        R = pickle.load(open(ref, "rb")); lr, _, _ = latchinfo(R)
        r["latch_same"] = all(li[q] == lr[q] for q in LAT)
        r["ndiff"] = sum(1 for n in C["EXACT"] if len(ev(H, nm[n])) != len(ev(R, nm[n])))
        r["nD_ref"] = len(ev(R, Dn))
    return r
if __name__ == "__main__":
    for fn in sys.argv[1:]: print(fn.split("/")[-1], run(fn))
