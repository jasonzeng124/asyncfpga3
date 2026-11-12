"""For each control (exact) gate v reading a data node z: every time z's value AS READ by v changes, is v
sensitive to z at that moment (F differs for z = 0/1 given the other pins' read values)? Such a change drives
v's output from data: a bundling violation in this run."""
import sys, pickle, collections
from bisect import bisect_right
sys.path.insert(0, "/tmp/claude-0/race")
from classify import load, lut
C = load(); g = C["gates"]; nm = C["names"]; EX = C["EXACT"]; DATA = C["DATA"]
def check(fn):
    H = pickle.load(open(fn, "rb")); hist = H["hist"]; DS = H["DS"]; R = H["R"]
    def val(n, t):
        if n not in hist: return False
        b, ts = hist[n]; return b ^ (bisect_right(ts, t) % 2 == 1)
    hz = []
    for v in EX:
        if v not in g: continue
        pins = g[v]["pins"]; ds = DS[v]
        for j, p in enumerate(pins):
            z = p["src"]
            if not p["live"] or z not in DATA: continue
            for tz in (hist[z][1] if z in hist else []):
                tau = tz + ds[j]
                if tau < R: continue
                outs = []
                for zv in (False, True):
                    bits = [(zv if q == j else val(pp["src"], tau - ds[q])) for q, pp in enumerate(pins)]
                    outs.append(lut(g[v]["init"], g[v]["k"], bits))
                if outs[0] != outs[1]: hz.append((nm[v], nm[z], tau))
    return H, hz
if __name__ == "__main__":
    for fn in sys.argv[1:]:
        H, hz = check(fn)
        print("%s: pair (%d,%d) c=%d out %s want %s; data-driven control changes: %d %s" % (
            fn.split("/")[-1], H["A"], H["B"], H["c"], H["res"], __import__("math").gcd(H["A"], H["B"]), len(hz), hz[:4]))
