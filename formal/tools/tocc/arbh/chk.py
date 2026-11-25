"""race outcome of one run (UNTRUSTED): gcd, hazchk, order of A=X22Y87.A6(0) vs B=X27Y80.A6(2), X22Y81.B5 glitches,
whether X22Y81.B5 changes while a reader latch is transparent, and the reader latches' histories vs a reference."""
import sys, pickle, math
sys.path.insert(0, "/tmp/claude-0/arbh")
from hazchk import check, C
nm = C["names"]; idn = {x: i for i, x in enumerate(nm)}; g = C["gates"]
READERS = {"SLICE_X25Y76.B5": "SLICE_X24Y77.A6", "SLICE_X25Y76.B6": "SLICE_X24Y77.A6", "SLICE_X27Y85.A6": "SLICE_X26Y85.A6", "SLICE_X27Y85.A5": "SLICE_X26Y85.A6"}
def ev(H, x):
    n = idn[x]; R = H["R"]; return [t for t in (H["hist"][n][1] if n in H["hist"] else []) if t > R - 1]
def pin(H, v, u):
    for j, p in enumerate(g[idn[v]]["pins"]):
        if p["src"] == idn[u]: return H["DS"][idn[v]][j]
def val(H, x, t):
    n = idn[x]
    if n not in H["hist"]: return False
    b, ts = H["hist"][n]; import bisect; return b ^ (bisect.bisect_right(ts, t) % 2 == 1)
def run(fn, ref=None):
    H = pickle.load(open(fn, "rb")); _, hz = check(fn)
    a = ev(H, "SLICE_X22Y87.A6"); b = ev(H, "SLICE_X27Y80.A6")
    tA = a[0] if a else None; tB = b[2] if len(b) > 2 else None
    D = ev(H, "SLICE_X22Y81.B5")
    bad = []
    for L, en in READERS.items():
        # D as read by L changes while L's enable as read by L is 1 (transparent) -> legit only if it is the intended data; report
        dD = pin(H, L, "SLICE_X22Y81.B5"); dE = pin(H, L, en)
        for t in D:
            tr = t + dD
            if val(H, en, tr - dE): bad.append((L, t))
    out = dict(res=H["res"], ok=H["res"] == [math.gcd(H["A"], H["B"])], hz=len(hz), hzex=hz[:3], tA=tA, tB=tB,
               skew=(tA - tB) if tA and tB else None, D=D[:8], Dopen=bad[:6], nDopen=len(bad))
    if ref is not None:
        R = pickle.load(open(ref, "rb"))
        out["readers_same"] = {L: len(ev(H, L)) == len(ev(R, L)) for L in READERS}
        out["ndiff"] = sum(1 for n in C["EXACT"] if len(ev(H, nm[n])) != len(ev(R, nm[n])))
    return out
if __name__ == "__main__":
    for fn in sys.argv[1:]: print(fn.split("/")[-1], run(fn))
def captures(H):
    """per reader latch: the value it holds at the end of each closed phase (just before the next enable rise is read)
    and its number of output changes"""
    out = {}
    for L, en in READERS.items():
        E = ev(H, en); dE = pin(H, L, en)
        out[L] = ([int(val(H, L, t + dE - 1)) for i, t in enumerate(E) if i % 2 == 0 and i > 0], len(ev(H, L)))
    return out
def dchg_open(H):
    """X22Y81.B5 changes read by a reader while it is transparent: (reader, time read, enable-read-rise before it, ps since)"""
    res = []
    D = ev(H, "SLICE_X22Y81.B5")
    for L, en in READERS.items():
        dD = pin(H, L, "SLICE_X22Y81.B5"); dE = pin(H, L, en); E = ev(H, en)
        for t in D:
            tr = t + dD
            if val(H, en, tr - dE):
                rises = [x + dE for i, x in enumerate(E) if i % 2 == 0 and x + dE <= tr]
                res.append((L, tr, tr - rises[-1] if rises else None))
    return res
