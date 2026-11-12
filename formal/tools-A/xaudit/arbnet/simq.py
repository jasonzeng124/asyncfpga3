"""simq.py -- UNTRUSTED evidence (lead, 2026-10-31): does one concrete SatPin behaviour of the gcd_hw
skeleton satisfy the arbiter hypotheses QQuiet and ArbOrd of Events9FullArb.design_verdict9arbnet_ordq?
The behaviour is Wip/E8Hyp/sim0.py's (copied below unchanged up to its own checks): every pin read with the
fixed delay arc_lo + lut_lo of the band file, from the rst=1 Kleene fixpoint, rst released at T, selects
constant. Added checks per arbiter (ustate = <arb>.ustate$LUT6):
  QQuiet: after each change of q at tau, ustate's other input reads (val(w, u - dl_i)) are constant for
    u in [tau, tau + W], W = the band hi of ustate's own q pin (arc hi + lut hi): the form the Lean
    hypothesis takes (phi of PqQ), stronger than this behaviour's own fixed delay needs;
  ArbOrd (fixed delays): for each grant reader, Dr + 2 <= DQ + Dq with this behaviour's delays
    (Dr = grant's request pin, DQ = ustate's pin for that request, Dq = grant's q pin).
Usage: simq.py skel.json skel_C.bands.json [selval] [T_ps] [horizon_ps]
"""
import json, sys, heapq, bisect
NEG = '--neg-window' in sys.argv
sys.argv = [a for a in sys.argv if a != '--neg-window']
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

# ---- added: QQuiet and fixed-delay ArbOrd per arbiter
def chg(w):
    return times(w)[0]
qq_bad = 0; ord_bad = 0; nflip = 0
for a in arbs:
    sc = a + ".ustate$LUT6"
    k, ins, q, init, dl = cells[sc]
    qi = [i for i, w in enumerate(ins) if w == q]
    W = (b["arcs"][f"{sc}/I{qi[0]}"][1] if qi else 0) + b["cells"][sc][1]
    if NEG: W = 10 ** 9   # negative control: any later input change violates
    flips = chg(q); nflip += len(flips)
    for tau in flips:
        for i, w in enumerate(ins):
            if w == q or not isinstance(w, int): continue
            # read of input i at u is val(w, u - dl[i]); changes of w in (tau - dl[i], tau + W - dl[i]]
            for tc in chg(w):
                if tau - dl[i] < tc <= tau + W - dl[i]:
                    qq_bad += 1
                    print(f"  QQUIET VIOLATION {a.split('udut.')[-1]}: q flip at {tau}, input I{i} read changes at {tc + dl[i]} (window {W})")
    qq, gl = arb_wires(a)
    for h, (g, r) in zip(("LUT5", "LUT6"), gl):
        gk, gins, _, _, gdl = cells[a + ".ugrant$" + h]
        if r is None: continue
        Dr = gdl[gins.index(r)]; Dq = gdl[gins.index(q)]
        DQ = dl[ins.index(r)] if r in ins else None
        ok = DQ is not None and Dr + 2 <= DQ + Dq
        if not ok: ord_bad += 1
        print(f"  ORD {a.split('udut.')[-1]} {h}: Dr {Dr} DQ {DQ} Dq {Dq} -> {'ok' if ok else 'FAIL'} (margin {None if DQ is None else DQ + Dq - Dr - 2})")
print(f"QQUIET {'OK' if qq_bad == 0 else 'VIOLATED'} ({nflip} q flips, {qq_bad} violations)")
print(f"ARBORD(fixed delays, grant readers) {'OK' if ord_bad == 0 else 'FAILS'} ({ord_bad} failing)")
