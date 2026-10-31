"""UNTRUSTED evidence (probe E8Hyp): one SatPin behaviour of gcd_hw's xaudit skeleton.
Every LUT pin i reads its driver with the FIXED delay arc_lo(i) + lut_lo (slow-corner lower
band ends, ps): the `t - lo` shift warps of Events8Bridge.satPin_exists. Time 0 is the Kleene
fixpoint of fix0.py (rst = 1); rst falls at T; the 32 select inputs are held constant (value
from argv, default 0). The run is checked for what HARB7 implies about the real wires:
(1) the two grants of each arbiter are never high together, and reports (2) how often both
requests of an arbiter are high together (contention) and (3) how many grants rose.
Usage: sim0.py skel.json skel_C.bands.json [selval] [T_ps] [horizon_ps]"""
import json, sys, heapq, bisect
skel, bands = sys.argv[1], sys.argv[2]
selval = int(sys.argv[3]) if len(sys.argv) > 3 else 0
T = int(sys.argv[4]) if len(sys.argv) > 4 else 20000
H = int(sys.argv[5]) if len(sys.argv) > 5 else 3_000_000
d = json.load(open(skel)); m = d["modules"]["gcd_ctl"]; b = json.load(open(bands))
rst = m["ports"]["rig_rst"]["bits"][0]
sels = {p["bits"][0] for n, p in m["ports"].items() if n.startswith("sel_")}
cells = {}
readers = {}
for cn, c in m["cells"].items():
    k = int(c["type"][3]); ins = [c["connections"][f"I{i}"][0] for i in range(k)]
    out = c["connections"]["O"][0]; init = int(c["parameters"]["INIT"], 2)
    lut_lo = b["cells"][cn][0]
    dl = [(b["arcs"][f"{cn}/I{i}"][0] if isinstance(ins[i], int) else 0) + lut_lo for i in range(k)]
    cells[cn] = (k, ins, out, init, dl)
    for i, w in enumerate(ins):
        if isinstance(w, int): readers.setdefault(w, []).append((cn, i))
# time-0 fixpoint (binary: selects at selval, rst 1) by iteration
v0 = {}
def rd0(w):
    if w == "0": return 0
    if w == "1": return 1
    if w == rst: return 1
    if w in sels: return selval
    return v0.get(w, 0)
for _ in range(200):
    ch = 0
    for cn, (k, ins, out, init, dl) in cells.items():
        a = sum(rd0(w) << i for i, w in enumerate(ins)); nv = (init >> a) & 1
        if v0.get(out, 0) != nv: v0[out] = nv; ch += 1
    if not ch: break
assert ch == 0, "no fixpoint"
for cn, (k, ins, out, init, dl) in cells.items():   # check it IS a fixpoint (hfix)
    assert ((init >> sum(rd0(w) << i for i, w in enumerate(ins))) & 1) == v0.get(out, 0)
hist = {}   # wire -> ([times], [values]) change list, value at 0 first
def val(w, t):
    if w == "0": return 0
    if w == "1": return 1
    if w == rst: return 1 if t < T else 0
    if w in sels: return selval
    if t < 0: t = 0
    h = hist.get(w)
    if h is None: return v0.get(w, 0)
    i = bisect.bisect_right(h[0], t) - 1
    return h[1][i] if i >= 0 else v0.get(w, 0)
def setv(w, t, x):
    h = hist.setdefault(w, ([], []))
    h[0].append(t); h[1].append(x)
pq = []
def sched(w, t):
    for cn, i in readers.get(w, []):
        heapq.heappush(pq, (t + cells[cn][4][i], cn))
sched(rst, T)
cur = dict(v0); nev = 0; last = None
while pq:
    t, cn = heapq.heappop(pq)
    if t > H: break
    if (t, cn) == last: continue
    last = (t, cn)
    k, ins, out, init, dl = cells[cn]
    a = sum(val(w, t - dl[i]) << i for i, w in enumerate(ins))
    nv = (init >> a) & 1
    if cur.get(out, 0) != nv:
        cur[out] = nv; setv(out, t, nv); sched(out, t); nev += 1
print(f"selval={selval} T={T} horizon={H} ps: {nev} output events, last event at {max((h[0][-1] for h in hist.values()), default=0)} ps")
# arbiter checks
arbs = sorted({cn.rsplit(".", 1)[0] for cn in cells if ".ugrant$" in cn})
def times(w): return hist.get(w, ([], []))
def high_both(w1, w2):
    ev = sorted(set([0] + times(w1)[0] + times(w2)[0]))
    return sum(1 for t in ev if val(w1, t) and val(w2, t))
def arb_wires(a):
    """q, and per grant (g, its request r), by evaluating the grant LUT as events4/model.py does."""
    q = cells[a + ".ustate$LUT6"][2]
    out = []
    for h in ("LUT5", "LUT6"):
        k, ins, g, init, dl = cells[a + ".ugrant$" + h]
        reqs = [w for w in ins if isinstance(w, int) and w != q]
        mine = None
        for r in reqs:
            hit = 0
            for qv in (0, 1):
                addr = sum(((1 if w == r else (qv if w == q else (1 if w == "1" else 0))) << i) for i, w in enumerate(ins))
                hit |= (init >> addr) & 1
            if hit: mine = r
        out.append((g, mine))
    return q, out
bad = 0; free = 0
for a in arbs:
    q, ((g1, r1), (g2, r2)) = arb_wires(a)
    both_g = high_both(g1, g2); both_r = high_both(r1, r2)
    ev = sorted(set([0] + times(r1)[0] + times(r2)[0] + times(g1)[0] + times(g2)[0]))
    fr = sum(1 for t in ev if val(r1, t) and val(r2, t) and not val(g1, t) and not val(g2, t))
    rises = sum(1 for x in times(g1)[1] + times(g2)[1] if x == 1)
    bad += both_g; free += fr
    print(f"  {a.split('udut.')[-1]}: grant rises {rises}, both grants high at {both_g} event times, both requests high at {both_r}, of which with no grant held {fr}")
print("FREE CONTESTS", free)
print("GRANT EXCLUSION", "OK" if bad == 0 else "VIOLATED")
if "--dump" in sys.argv:
    for a in arbs:
        q, ((g1, r1), (g2, r2)) = arb_wires(a)
        ws = dict(r1=r1, r2=r2, q=q, g1=g1, g2=g2)
        evs = sorted((t, n, x) for n, w in ws.items() for t, x in zip(*times(w)))
        if evs: print(a.split("udut.")[-1], evs)
# E8Arb addition: per arbiter, event list incl. R0 and A0 (UNTRUSTED)
if "--arb" in sys.argv:
    for a in arbs:
        q, ((g1, r1), (g2, r2)) = arb_wires(a)
        st = cells[a + ".ustate$LUT6"]
        R0 = cells[a + ".ustate$LUT5"][2]
        a0 = [w for w in st[1] if isinstance(w, int) and w not in (r1, r2, q, rst)]
        ws = dict(r1=r1, r2=r2, q=q, g1=g1, g2=g2, R0=R0, A0=a0[0] if a0 else None)
        evs = sorted((t, n, x) for n, w in ws.items() if w is not None for t, x in zip(*times(w)))
        if evs: print(a.split("udut.")[-1], "init", {n: v0.get(w, 0) for n, w in ws.items() if w is not None}, evs)
