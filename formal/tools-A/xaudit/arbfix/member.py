"""UNTRUSTED (probe E8ArbFix): is a RECORDED per-pin run (sim.py --json) of each arbiter a behaviour
of the virtual arbiter core?

  member.py skel.json bands.json run.json

OLD core (XA_ARB=old bands, model.py build_arb_old) -- necessary conditions only:
  N1 (Lean: Events8Arb.vmerge_needs_grant): at the FIRST rise of R0 (time t), some grant must have
     been high at a time <= t - (F_lo + tap_lo) of the old R0 node;
  N2 (per round; Lean has the first-rise case Events8Arb.vgrant_rise_ctl, later rounds need SelOK):
     a grant rising at t in the round whose A0 fall is a must have t >= a + lo + F_lo + 2;
  N3 (the guard G judgement of cert8/9 at A_b = C(g_b, A0): filt_b(M A0) <= M g_b, no token):
     A0 must not rise in a b-round before g_b has risen in it.
FIX core (model.py build_arb_fix): CONSTRUCTS the virtual signals (ctl edges, sigma per round, every
pin lag = the run's fixed per-pin delay minus the core's offsets) and checks, at every ps of the run,
that the virtual grants equal the real grant wires and that R0 = OR of the two shadows 2 ps earlier,
and that every lag lies in its band.  A failure prints the first mismatching time.
"""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "events4"))
skel, bandp, runp = [x for x in sys.argv[1:] if not x.startswith("--")][:3]
# negative controls of the FIX check itself (each must make some arbiter NOT MEMBER on a run with a
# q-caused grant/R0 edge):  --mut=samectl  every reader reads ctl with the GRANT's ctl lag (one
# common reader timing: E8Arb section 4's (1,1) ctl pin for grant and shadow);  --mut=noshift  the
# shadows' 2 merge/tap steps dropped
MUT = next((x.split("=", 1)[1] for x in sys.argv if x.startswith("--mut=")), None)
run = json.load(open(runp))

def sig(w, H):
    v = [w["v0"]] * (H + 1)
    for t, x in w["ev"]:
        for i in range(t, H + 1):
            v[i] = x
    return v

def _rnet(R, b):
    return R["wires"][f"r{b}"]["net"]

def mk(mode):
    import importlib, model
    model.ARB_MODE = mode
    importlib.reload(model) if False else None
    model.ARB_MODE = mode
    return model.Model(skel, bandp)

Mold, Mfix = mk("old"), mk("fix")
H = max([t for a in run["arbs"].values() for w in a["wires"].values() for t, _ in w["ev"]] + [0]) + 6000
tot = dict(N1=0, N2=0, N3=0, fixok=0, fixbad=0, arbs=0)
for qc, ab in Mfix.arbs.items():
    a = qc.rsplit(".", 1)[0]
    if a not in run["arbs"]:
        continue
    tot["arbs"] += 1
    R = run["arbs"][a]; W = {n: sig(w, H) for n, w in R["wires"].items()}; D = R["delay"]
    nm = a.split("udut.")[-1]
    # rounds: A0 low phases [a_k, b_k)
    A0 = W["A0"]
    falls = [0] if A0[0] == 0 else []
    rises = []
    for t in range(1, H + 1):
        if A0[t - 1] == 1 and A0[t] == 0: falls.append(t)
        if A0[t - 1] == 0 and A0[t] == 1: rises.append(t)
    q = W["q"]
    grants = {1: W["g1"], 2: W["g2"]}
    # ---------------- old core: N1, N2, N3
    od = Mold.nodes
    on = od["arb:" + ab["R0"]]
    rR = [t for t in range(1, H + 1) if W["R0"][t - 1] == 0 and W["R0"][t] == 1]
    msg = []
    if rR:
        t = rR[0]
        need = min(on["F"][0] + p.lo for p in on["pins"])
        ok = any(grants[b][u] for b in (1, 2) for u in range(0, max(0, t - need) + 1))
        if not ok:
            tot["N1"] += 1; msg.append(f"N1 VIOLATED (R0 rises {t}, no grant high by {t - need})")
    octl = od["vctl:" + qc]["pins"][0].lo
    for b, gname in enumerate(sorted(ab["grants"], key=lambda g: g[-4:])):
        g = grants[b + 1]
        loF = od["arb:" + gname]["F"][0]
        for t in range(1, H + 1):
            if g[t - 1] == 0 and g[t] == 1:
                ak = max([f for f in falls if f <= t], default=None)
                if ak is not None and t < ak + octl + loF + 2:
                    tot["N2"] += 1; msg.append(f"N2 VIOLATED (g{b+1} rises {t}, A0 fell {ak}, old core needs >= {ak + octl + loF + 2})")
                # N3: A0 rise in this round before g rises
                rk = [r for r in rises if ak is not None and ak <= r < t]
                if rk:
                    tot["N3"] += 1; msg.append(f"N3 VIOLATED (A0 rises {rk[0]} before g{b+1} rises {t})")
    # ---------------- fix core: construct and compare
    fd = Mfix.nodes
    K = ab["K"]; loc = ab["lo_ctl"]
    gl = sorted(ab["grants"], key=lambda g: g[-4:])          # LUT5 = g1, LUT6 = g2
    lag = {}; bad = []
    nets = {}
    for b in (1, 2):                       # the request net g_b reads (sim.py's r_b)
        nets[b] = [w for w in Mfix.n.cells[gl[b - 1]]["ins"] if w == _rnet(R, b)][0]
    n = Mfix.n
    def inband(x, p, what, X=None, w=None, e=0):
        if X is None:                       # ctl pin: band as in the core
            lo, hi = p.taps[0]
        else:                               # request pin, read from the request NET (the run's
            i = n.cells[X]["ins"].index(w)  # wire): arc + lut - 1 - e; the stateless path above
            a, l = n.arcband(X, i), n.lutband(X)   # the net is in the pin band, fixed in the run
            lo, hi = a[0] + l[0] - 1 - e, a[1] + l[1] - 1 - e
        if not (lo <= x <= hi):
            bad.append(f"{what} lag {x} not in {(lo, hi)}")
    for b in (1, 2):
        ng = fd["arb:" + gl[b - 1]]; ns = fd[f"vsh:{ab['R0']}/{b - 1}"]
        lr, lq = D[f"g{b}"][f"r{b}"] - 1, D[f"g{b}"]["q"] - K - 1
        sr, sq = D["R0"][f"r{b}"] - 3, D["R0"]["q"] - K - 3
        rnet = nets[b]
        inband(lr, ng["pins"][0], f"g{b} req", gl[b - 1], rnet, 0); inband(lq, ng["pins"][1], f"g{b} ctl")
        inband(sr, ns["pins"][0], f"sh{b} req", ab["R0"], rnet, 2); inband(sq, ns["pins"][1], f"sh{b} ctl")
        if MUT == "samectl":
            sq = lq
        if MUT == "noshift":
            sr, sq = sr + 2, sq + 2
        lag[("g", b)] = (lr, lq); lag[("s", b)] = (sr, sq)
    if not (D["st"]["A0"] >= 1):
        bad.append("A0 delay")
    # ctl rounds
    c, e, win = [], [], []
    for k, ak in enumerate(falls):
        bk = next((r for r in rises if r > ak), None)
        end = bk if bk is not None else H + 1
        fl = [t for t in range(max(ak, 1), end) if q[t] != q[t - 1]]
        w = (1 if q[fl[0]] == 1 else 2) if fl else (1 if q[ak] == 1 else 2)
        ck = ak + loc + 1
        if fl:
            ck = max(ck, fl[0] + K)
        # after the winner's previous falls (read with its ctl lag)
        for kind in ("g", "s"):
            X = grants[w] if kind == "g" else None
        c.append(ck); win.append(w)
        if bk is not None:
            ek = bk + loc + 1
            e.append(ek)
        else:
            e.append(None)
    ctl = [0] * (H + 1)
    for ck, ek in zip(c, e):
        for t in range(ck, (ek if ek is not None else H + 1)):
            if t <= H: ctl[t] = 1
    # ctl lag check: every ctl edge lag >= loc + 1, edges in A0's order
    for ck, ak in zip(c, falls):
        if ck - ak < loc + 1: bad.append("ctl rise lag")
    rnd = [None] * (H + 1)
    for k, (ck, ek) in enumerate(zip(c, e)):
        for t in range(ck, (ek if ek is not None else H + 1)):
            if t <= H: rnd[t] = k
    def virt(b, lr, lq, shift):
        r = W[f"r{b}"]; X = [0] * (H + 1)
        for t in range(2, H + 1):
            sr, sq = t - 1 - lr, t - 1 - lq
            rv = r[max(sr, 0)]
            en = 1 if (sq >= 0 and ctl[sq] and win[rnd[sq]] == b) else 0
            X[t] = rv if rv == en else X[t - 2]
        return X
    mism = []
    for b in (1, 2):
        Vg = virt(b, *lag[("g", b)], 0)
        Vs = virt(b, *lag[("s", b)], 2)
        g = grants[b]
        tm = next((t for t in range(H + 1) if Vg[t] != g[t]), None)
        if tm is not None: mism.append(f"g{b} differs at {tm} (virtual {Vg[tm]}, real {g[tm]})")
        lag[("V", b)] = Vs
    R0 = W["R0"]
    tm = next((t for t in range(2, H + 1) if (lag[("V", 1)][t - 2] | lag[("V", 2)][t - 2]) != R0[t]), None)
    if tm is not None: mism.append(f"R0 differs at {tm}")
    ok = not mism and not bad
    tot["fixok" if ok else "fixbad"] += 1
    nr = sum(1 for g in grants.values() for t in range(1, H + 1) if g[t - 1] == 0 and g[t] == 1)
    print(f"{nm:24s} rounds {len(falls)} grant rises {nr} | old: {'; '.join(msg) or 'N1-N3 hold'} | fix: {'MEMBER' if ok else 'NOT MEMBER ' + '; '.join(bad + mism)}")
print("summary", tot)
