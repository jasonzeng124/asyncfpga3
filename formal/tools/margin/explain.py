#!/usr/bin/env python3
"""margin/explain.py (shard C, UNTRUSTED): the picosecond form of one failing race (PROGRAM.md, "A kappa is not a result").

    python3 explain.py OUT/ NODE PIN KAPPA [--w 0] [--routed routed.json] [--sdfmap sdf_arcs.json]

OUT/ is a margin run directory (net.json, bnd.json, net.simx, simx, witness/command.txt, margins.txt). NODE PIN KAPPA
name a failing row of margins.txt (PIN 99 / 100+i for cone rows). The tool
1. re-runs the row's adversary (its slow arcs at (1+k) FAST_MAX, all else at (1-k) FAST_MIN) and the reference run
   (no slow arcs, same k) with dumps (w = 0 by default: transport, so every flip has an exact cause);
2. finds the CAPTURE: the first storage LUT (a LUT reading its own output) whose output history differs between the
   two runs, at time t*;
3. finds the two RACING ARRIVALS at that LUT: the arrival the adversary delayed (on a slowed pin, or the latest-moved
   arrival) and the arrival on another pin that overtook it in the witness;
4. traces both back, flip by flip (output flip at t caused by the input flip at t - d), in the WITNESS run (the failing
   behaviour, with its delays) to their common launch (the SPLIT: the latest flip both depend on);
5. reports both paths from the split to the capture: every arc with its prjxray band, cells (LUT, MUXF, CARRY) and
   routing (pips, hops) apart; the slack at the band MIDPOINTS (fast corner and slow corner) and at nextpnr's SDF when
   --sdfmap is given; and the slack as a multiple of the measured delay error (8.5 % median ring error, August ring
   data on claude/research) of the longer path.
Every number is an untrusted reading of one simulated run; the paths are those of the witness's failure.
"""
import argparse, json, os, re, subprocess, sys, bisect
ap = argparse.ArgumentParser()
ap.add_argument("out"); ap.add_argument("node"); ap.add_argument("pin", type=int); ap.add_argument("kappa")
ap.add_argument("--w", type=int, default=0); ap.add_argument("--routed", default=None)
ap.add_argument("--sdfmap", default=None, help="JSON {\"NODE:PIN\": ps} nominal SDF delay per arc (optional)")
ap.add_argument("--sdf", default=None, help="nextpnr's SDF of this build (needs --routed): the paths' delays at the nominal SDF")
ap.add_argument("--err", type=float, default=0.085, help="measured relative delay error (median ring scatter)")
ap.add_argument("--err7", type=float, default=0.47, help="worst measured relative error on the shortest rings (7 links: ratio 0.773..1.470, cells/hw/README.md on claude/research)")
a = ap.parse_args()
O = os.path.abspath(a.out)
net = json.load(open(os.path.join(O, "net.json"))); G = net["gates"]; N = net["nodes"]; idx = {n: i for i, n in enumerate(N)}
ENV = set(idx[x] for x in json.load(open(os.path.join(O, "bnd.json")))["env"])
drv = {g["out"]: gi for gi, g in enumerate(G) if g["out"] not in ENV}
CELL = {"lut6", "lut5", "muxf", "carry"}
def is_copy(g): return g["k"] == 1 and g["init"] == 2
# the row's slow arcs
S = None
for l in open(os.path.join(O, "margins.txt")):
    f = l.split()
    if len(f) > 4 and not l.startswith("#") and f[1] == a.node and f[2] == str(a.pin):
        S = [[x.rsplit("/", 1)[0], int(x.rsplit("/", 1)[1])] for x in f[-1].split(",")]; break
if S is None: sys.exit("row %s %d not in margins.txt" % (a.node, a.pin))
SL = set((drv[idx[n]], p) for n, p in S)   # (gate index, pin)
base = [l for l in open(os.path.join(O, "witness", "command.txt")) if not l.startswith("#")][0].split()
env = {}
while "=" in base[0] and not base[0].startswith("/"): k, v = base.pop(0).split("=", 1); env[k] = v
KD = int(env.get("KDEN", "100"))
def setopt(cmd, opt, val):
    cmd = list(cmd)
    if opt in cmd: cmd[cmd.index(opt) + 1] = val
    else: cmd += [opt, val]
    return cmd
def run(slow, tag):
    cf = os.path.join(O, "tmp", "ex_%s.json" % tag); df = os.path.join(O, "tmp", "ex_%s_dump.json" % tag)
    os.makedirs(os.path.dirname(cf), exist_ok=True); json.dump({"S": slow, "F": []}, open(cf, "w"))
    cmd = setopt(setopt(base, "--kappa", a.kappa), "--classes", cf)
    if "--w" in cmd: i = cmd.index("--w"); del cmd[i:i + 2]
    if a.w: cmd += ["--w", str(a.w)]
    cmd = [x for x in cmd if x != "--periodic"] + ["--periodic", "--dump", df]
    r = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, **env), cwd=O)
    res = ([x for x in r.stdout.splitlines() if x.startswith("RESULT")] or ["NO-VERDICT"])[0]
    d = json.load(open(df)); os.unlink(df)
    return res, {int(k): (bool(v[0]), v[1]) for k, v in d["nodes"].items()}
PK = round(float(a.kappa) * KD)
def delay(gi, p, slow, corner=0):
    e = G[gi]["arcs"][p]; FN, FX = (e["fmin"], e["fmax"]) if corner == 0 else (e["smin"], e["smax"])
    d = ((KD + PK) * FX) // KD if slow else -((-(KD - PK) * FN) // KD)
    if a.w and G[gi]["kind"] in ("lut6", "lut5") and d < a.w: d = a.w
    return d
names = {}
if a.routed:
    Rj = json.load(open(a.routed))["modules"]["top"]["cells"]
    bel = {c["attributes"].get("NEXTPNR_BEL"): nm for nm, c in Rj.items() if c.get("attributes", {}).get("NEXTPNR_BEL")}
    for gi, g in enumerate(G):
        m = re.match(r"(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])", g["name"])
        if m: names[g["out"]] = bel.get("%s/%s%sLUT" % (m.group(1), m.group(2), m.group(3)), "")
resw, W = run(S, "wit"); resr, R = run([], "ref")
print("witness   (route slow): %s" % resw); print("reference (all fast)  : %s" % resr)
def flips(D, n): return D.get(n, (False, []))[1]
def v0(D, n): return D.get(n, (False, []))[0]
storage = set()
for gi, g in enumerate(G):
    if is_copy(g) or g["out"] in ENV or g["k"] < 2: continue
    srcs = []
    for u in g["ins"]:
        while u in drv and is_copy(G[drv[u]]): u = G[drv[u]]["ins"][0]
        srcs.append(u)
    if g["out"] in srcs: storage.add(gi)
def firstdiff(n):
    fw, fr = flips(W, n), flips(R, n)
    if v0(W, n) != v0(R, n): return 0
    for x, y in zip(fw, fr):
        if x != y: return min(x, y)
    if len(fw) != len(fr): return (fw[len(fr)] if len(fw) > len(fr) else fr[len(fw)])
    return None
allc = []
for gi, g in enumerate(G):
    if g["out"] in ENV: continue
    t = firstdiff(g["out"])
    if t is not None: allc.append((t, gi))
allc.sort()
print("first nodes to diverge (any gate): " + ", ".join("%s(%s)@%d%s" % (N[G[gi]["out"]], G[gi]["kind"], t, "*" if any((gi, p) in SL for p in range(G[gi]["k"])) else "") for t, gi in allc[:6]) + "   (* = an adversary arc)")
cands = []
for gi in storage:
    t = firstdiff(G[gi]["out"])
    if t is not None: cands.append((t, gi))
if not cands: sys.exit("no storage LUT diverges between witness and reference")
cands.sort()
for t, gi in cands[:8]: print("  diverges: %-22s at %d ps%s" % (N[G[gi]["out"]], t, "  <- the row's storage LUT" if N[G[gi]["out"]] == a.node else ""))
own = [(t, gi) for t, gi in cands if N[G[gi]["out"]] == a.node]
# a single-pin row names its storage LUT: explain the race there; a cone row: the first diverging storage LUT
if a.pin >= 99 and os.path.exists(os.path.join(O, "cones.json")):
    # a cone row: the capture is one of the group's latch bits (the cone feeds their data pins), not whatever
    # storage LUT diverges first downstream
    mem = next((set(r.get("members", [])) for r in json.load(open(os.path.join(O, "cones.json"))) if r["node"] == a.node and r["pin"] == a.pin), set())
    own = [(t, gi) for t, gi in cands if N[G[gi]["out"]] in mem]
    if not own: sys.exit("no latch of the cone row's group diverges")
tstar, q = own[0] if (own and (a.pin < 99 or os.path.exists(os.path.join(O, "cones.json")))) else cands[0]; gq = G[q]
print("\nCAPTURE: %s (%s) first differs at %d ps" % (N[gq["out"]], gq["name"], tstar))
# arrivals at q's pins in both runs around t*
def arrivals(D, slowset):
    out = []
    for p, u in enumerate(gq["ins"]):
        d = delay(q, p, (q, p) in slowset)
        for t in flips(D, u):
            if tstar - 20000 <= t + d <= tstar + 20000: out.append((t + d, p, t))
    return sorted(out)
aw, ar = arrivals(W, SL), arrivals(R, set())
slowpins = [p for p in range(gq["k"]) if (q, p) in SL]
def single_race():
    """single-pin rows: the arrival the adversary delayed vs the other-pin arrival that overtook it"""
    moved = []
    for p in range(gq["k"]):
        tw = [x for x in aw if x[1] == p]; tr = [x for x in ar if x[1] == p]
        for x, y in zip(tw, tr): moved.append((x[0] - y[0], p, x, y))
    moved.sort(reverse=True)
    mi = ([m for m in moved if m[1] in slowpins] or moved) if slowpins else moved
    if not mi or mi[0][0] <= 0: sys.exit("no arrival at the capture moved later in the witness (the race is not at a pin of %s)" % N[gq["out"]])
    dly, pi, (aiw, _, ui_w), (air, _, ui_r) = mi[0]
    over = [x for x in aw if x[1] != pi and air < x[0] < aiw]
    if not over: over = [x for x in aw if x[1] != pi and x[0] < aiw][-1:]
    if not over: sys.exit("no competing arrival found")
    ajw, pj, uj = over[0]
    print("RACE at %s: pin %d (delayed %d ps by the adversary: reference arrival %d, witness %d) against pin %d (arrival %d)" %
          (N[gq["out"]], pi, dly, air, aiw, pj, ajw))
    return pi, (gq["ins"][pi], ui_w), pj, (gq["ins"][pj], uj)
def stall_runts(width=300, show=8):
    """a stall: list the earliest short pulses (< width ps) on storage LUT outputs in the witness that the reference
    has no pulse of that width on (hazards that can leave a handshake half done)"""
    def pulses(D, n):
        fl = flips(D, n); return [(fl[i], fl[i + 1] - fl[i]) for i in range(len(fl) - 1) if fl[i + 1] - fl[i] < width]
    out = []
    for gi in storage:
        n = G[gi]["out"]; pw = pulses(W, n)
        if not pw: continue
        pr = set(w for t, w in pulses(R, n))
        for t, w in pw:
            if w not in pr: out.append((t, w, n)); break
    out.sort()
    print("STALL: earliest short pulses (< %d ps) on storage LUTs in the witness, absent from the reference:" % width)
    for t, w, n in out[:show]:
        print("  %8d ps  %4d ps wide  %s %s" % (t, w, N[n], names.get(n, "")))
    if not out: print("  none")
def cone_race():
    """cone rows (a setup / capture race). The slowed cone shifts the witness's whole timeline, so the runs are aligned
    by CAPTURE COUNT: the k-th close of the latch (enable arrival with its holding value) in each run. The first k whose
    captured value differs is the failure; in the witness, path A = the first data-pin arrival after that close (the
    data that came too late), path B = the enable arrival that closed the latch."""
    srcs = set(idx[x] for x in rowsrc.split("+") if x in idx)
    def src0(u):
        while u in drv and is_copy(G[drv[u]]): u = G[drv[u]]["ins"][0]
        return u
    o = gq["out"]; srcp = [src0(u) for u in gq["ins"]]
    en = [p for p, u in enumerate(srcp) if u in srcs]
    fb = [p for p, u in enumerate(srcp) if u == o]
    if not en or not fb: sys.exit("cone row: %s has no enable pin from %s or no feedback pin" % (N[o], rowsrc))
    e, f = en[0], fb[0]
    k, I = gq["k"], gq["init"]
    hv = [v for v in (0, 1) if all(((I >> x) & 1) == ((I >> (x ^ (1 << f))) & 1) for x in range(1 << k) if ((x >> e) & 1) == v)]
    if not hv: sys.exit("cone row: no holding value of the enable pin")
    hv = hv[0]
    def closes(D, slow):
        u = gq["ins"][e]; d = delay(q, e, (q, e) in slow); v0_, fl = D.get(u, (False, []))
        out = []
        for i, t in enumerate(fl):
            nv = v0_ ^ (i % 2 == 0)
            if nv == hv: out.append((t + d, t))
        return out
    def val(D, n, t):
        v0_, fl = D.get(n, (False, [])); return v0_ ^ (bisect.bisect_right(fl, t) % 2 == 1)
    cr, cw = closes(R, set()), closes(W, SL)
    kk = None
    for i, ((tr_, _), (tw_, _)) in enumerate(zip(cr, cw)):
        if val(R, o, tr_ + 400) != val(W, o, tw_ + 400): kk = i; break
    if kk is None:
        if len(cw) < len(cr):
            stall_runts()
            sys.exit("cone row: the latch %s captures the same values in both runs but closes only %d times in the witness (%d in the "
                     "reference): the witness STALLS (deadlock / livelock) before its next capture; it is not a wrong capture at "
                     "this latch, and this tool does not trace stalls yet" % (N[o], len(cw), len(cr)))
        sys.exit("cone row: every capture of %s holds the same value in both runs (%d / %d closes)" % (N[o], len(cr), len(cw)))
    tcw, ucw = cw[kk]
    dat = [p for p in range(k) if p not in en and p not in fb]
    late = []
    for p in dat:
        u = gq["ins"][p]; d = delay(q, p, (q, p) in SL)
        for t in flips(W, u):
            if tcw < t + d <= tcw + 20000: late.append((t + d, p, t)); break
    if not late: sys.exit("cone row: no data arrival after the %d-th close in the witness" % kk)
    adw, pi, udw = min(late)
    print("RACE (capture) at %s: close #%d (enable pin %d) at %d ps in the witness; data pin %d changes %d ps AFTER it (the reference "
          "captured the new value: close at %d ps)" % (N[o], kk, e, tcw, pi, adw - tcw, cr[kk][0]))
    return pi, (gq["ins"][pi], udw), e, (gq["ins"][e], ucw)
rowsrc = None
for l in open(os.path.join(O, "margins.txt")):
    f = l.split()
    if len(f) > 4 and not l.startswith("#") and f[1] == a.node and f[2] == str(a.pin): rowsrc = f[3]; break
pi, A0, pj, B0 = cone_race() if a.pin >= 99 else single_race()
# both paths are traced in the WITNESS (the failing behaviour, its delays); their nominal delays are then summed below
TR = W
# back-trace in the WITNESS run: the cause DAG. A flip of node n at t (gate g) depends on, for each pin p that g's
# INIT depends on, the last flip of that input at or before t - d_p (within a window). The split is the latest flip that
# is an ancestor of both racing arrivals; each path is the critical chain (latest arrival at every gate) from it.
def dep(g, j):
    k, I = g["k"], g["init"]
    return any(((I >> x) & 1) != ((I >> (x ^ (1 << j))) & 1) for x in range(1 << k))
WIN = 40000
BJ = json.load(open(os.path.join(O, "bnd.json")))["boundary"]
BACKS = [idx[BJ[k]] for k in ("a_ack", "b_ack", "start_ack", "out0_req") if k in BJ and isinstance(BJ[k], str) and BJ[k] in idx]
BDATA = set(idx[x] for k in ("a_data", "b_data") for x in (BJ.get(k) or []) if isinstance(x, str) and x in idx)
def parents(n, t):
    if n in ENV:
        # the harness: a data bit moves in reaction to an acknowledge (or out0's request); its parents are the last
        # flips of those boundary nodes at or before t (the harness reacts after >= 1 ps)
        if n not in BDATA: return []
        out = []
        for b in BACKS:
            fl = flips(TR, b); i = bisect.bisect_right(fl, t - 1) - 1
            if i >= 0 and fl[i] >= t - WIN: out.append(((b, fl[i]), None, 0, t - fl[i]))
        return out
    if n not in drv: return []
    gi = drv[n]; g = G[gi]; out = []
    for p, u in enumerate(g["ins"]):
        if not dep(g, p) and not is_copy(g): continue
        d = delay(gi, p, (gi, p) in SL); fl = flips(TR, u)
        i = bisect.bisect_right(fl, t - d) - 1
        if i >= 0 and fl[i] >= t - WIN: out.append(((u, fl[i]), gi, p, d))
    return out
def ancestors(x0):
    seen = {x0: None}; st = [x0]; tmin = x0[1] - WIN
    while st:
        x = st.pop()
        for y, gi, p, d in parents(*x):
            if y[1] >= tmin and y not in seen: seen[y] = 1; st.append(y)
    return seen
def nearflip(n, t):
    fl = flips(R, n)
    if not fl: return None
    i = min(range(len(fl)), key=lambda k: abs(fl[k] - t)); return (n, fl[i])
if A0[1] not in flips(TR, A0[0]) or B0[1] not in flips(TR, B0[0]): sys.exit("racing input flips not found in the witness run")
AA, AB = ancestors(A0), ancestors(B0)
common = [x for x in AA if x in AB]
def show(S0, lab):
    lut = sorted([x for x in S0 if x[0] in drv and G[drv[x[0]]]["kind"] in ("lut6", "lut5")], key=lambda x: -x[1])
    print("  %s ancestors: %d flips, %d LUT flips; latest LUT flips: %s" % (lab, len(S0), len(lut), ", ".join("%s@%d" % (N[n], t) for n, t in lut[:6])))
show(AA, "A (%s@%d)" % (N[A0[0]], A0[1])); show(AB, "B (%s@%d)" % (N[B0[0]], B0[1]))
if not common:
    print("\nno common launch within %d ps before the race" % WIN); sys.exit(0)
sp = max(common, key=lambda x: x[1])
def crit(x0, anc):
    """critical chain from the split to x0: walk back from x0 through parents that descend from sp, latest arrival first"""
    # descendants of sp inside anc: those whose ancestor set contains sp (memoised DFS)
    memo = {}
    def hs(x):
        if x == sp: return True
        if x in memo: return memo[x]
        memo[x] = False
        r = any(y in anc and y[1] >= sp[1] and hs(y) for y, gi, p, d in parents(*x))
        memo[x] = r; return r
    sys.setrecursionlimit(100000)
    path = []; x = x0
    while x != sp:
        cand = [(y[1] + d, y, gi, p) for y, gi, p, d in parents(*x) if y in anc and y[1] >= sp[1] and hs(y)]
        if not cand: break
        _, y, gi, p = max(cand); path.append((gi, p, x[1]) if gi is not None else ("ENV", x[0], x[1] - y[1])); x = y
    return list(reversed(path))
pa = crit(A0, AA) + [(q, pi, None)]; pb = crit(B0, AB) + [(q, pj, None)]
sn, st = sp
sdf = json.load(open(a.sdfmap)) if a.sdfmap else None
_u = sn
while _u in drv and G[drv[_u]]["kind"] not in CELL: _u = G[drv[_u]]["ins"][0]
print("SPLIT (common launch): %s flips at %d ps; driven by the cell %s %s" % (N[sn], st, N[_u], names.get(_u, "")))
def summ(arcs, label):
    tot = {"cell": [0, 0, 0, 0, 0], "route": [0, 0, 0, 0, 0]}
    lines = []
    for gi, p, t in arcs:
        if gi == "ENV":
            lines.append("    HARNESS: %s moves %d ps after the acknowledge it reacts to (simulated harness; Spec.Env allows any delay >= 0)" % (N[p], t))
            continue
        g = G[gi]; e = g["arcs"][p]; kind = "cell" if g["kind"] in CELL else "route"
        sd = sdf.get("%s:%d" % (N[g["out"]], p)) if sdf else None
        vals = [e["fmin"], e["fmax"], e["smin"], e["smax"], sd if sd is not None else 0]
        for i in range(5): tot[kind][i] += vals[i]
        if kind == "cell" or g["kind"] in ("lut6", "lut5"):
            lines.append("    %-28s pin %d  %-5s fast [%d, %d]  slow [%d, %d]%s  %s" % (N[g["out"]], p, g["kind"], *vals[:4], ("  sdf %d" % sd) if sd is not None else "", names.get(g["out"], "")))
    nr = sum(1 for gi, p, t in arcs if gi != "ENV" and G[gi]["kind"] not in CELL)
    print("  %s: %d arcs (%d cells, %d routing)" % (label, len(arcs), len(arcs) - nr, nr))
    for l in lines: print(l)
    for kind in ("cell", "route"):
        x = tot[kind]; print("    %-5s total: fast [%d, %d] mid %.0f   slow [%d, %d] mid %.0f%s" % (kind, x[0], x[1], (x[0] + x[1]) / 2, x[2], x[3], (x[2] + x[3]) / 2, ("   sdf %d" % x[4]) if sdf else ""))
    return {k: [tot["cell"][i] + tot["route"][i] for i in range(5)][j] for j, k in enumerate(("fmin", "fmax", "smin", "smax", "sdf"))}
# ---- nominal SDF (nextpnr's model): cells = IOPATH of each LUT / MUXF on the path, routing = INTERCONNECT from the
# previous cell's output to this cell's pin, starting from the cell that drives the split.
SDFI = SDFX = None; BELI = {}
if a.sdf and a.routed:
    for nm, c in Rj.items():
        b = c.get("attributes", {}).get("NEXTPNR_BEL")
        if b: BELI[b] = nm
    SDFI, SDFX = {}, {}
    inst = None
    for l in open(a.sdf):
        if "(INSTANCE" in l:
            inst = l.split("(INSTANCE", 1)[1].strip().rstrip(")").strip().replace("\\", "")
        elif "(IOPATH" in l:
            f = l.split(); SDFI[(inst, f[1], f[2])] = int(f[3].strip("(").split(":")[1])
        elif "(INTERCONNECT" in l:
            f = l.split(); SDFX[(f[1].replace("\\", ""), f[2].replace("\\", ""))] = int(f[3].strip("(").split(":")[1])
def cellinfo(gi):
    g = G[gi]
    m = re.match(r"(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", g["name"])
    if m:
        return BELI.get("%s/%s%sLUT" % (m.group(1), m.group(2), m.group(3))), (lambda p: "A%d" % (p + 1)), "O" + m.group(3)
    m = re.match(r"(SLICE_X\d+Y\d+)\.(F7A|F7B|F8)$", g["name"])
    if m:
        return BELI.get("%s/%sMUX" % (m.group(1), m.group(2))), (lambda p: ["0", "1", "S0"][p]), "OUT"
    return None
def sdf_path(arcs, splitnode):
    """(cells, routing, unmapped) ps at nextpnr's SDF along arcs, from the cell driving splitnode"""
    u = splitnode
    while u in drv and G[drv[u]]["kind"] not in CELL: u = G[drv[u]]["ins"][0]
    prev = cellinfo(drv[u]) if u in drv else None
    cells = route = 0; miss = []
    for gi, p, t in arcs:
        if gi == "ENV":
            m = re.match(r"(SLICE_X\d+Y\d+)\.([A-D])([56])$", N[p]); prev = None
            if m: prev = (BELI.get("%s/%s%sLUT" % (m.group(1), m.group(2), m.group(3))), None, "O" + m.group(3))
            continue
        if G[gi]["kind"] not in CELL: continue
        ci = cellinfo(gi)
        if not ci or not ci[0]: miss.append(N[G[gi]["out"]]); prev = None; continue
        pin = ci[1](p)
        if prev and prev[0]:
            x = SDFX.get((prev[0] + "/" + prev[2], ci[0] + "/" + pin))
            if x is None: miss.append("route->%s/%s" % (N[G[gi]["out"]], pin))
            else: route += x
        else: miss.append("route->%s/%s" % (N[G[gi]["out"]], pin))
        y = SDFI.get((ci[0], pin, ci[2]))
        if y is None: miss.append("%s %s->%s" % (N[G[gi]["out"]], pin, ci[2]))
        else: cells += y
        prev = ci
    return cells, route, miss
print("\nPATH A (must arrive FIRST; the adversary slowed it): split -> %s pin %d" % (N[gq["out"]], pi))
A = summ(pa, "path A")
print("PATH B (overtook it in the witness): split -> %s pin %d" % (N[gq["out"]], pj))
B = summ(pb, "path B")
print("\nSLACK (path B - path A; positive = the required order holds):")
for lab, x, y in (("fast-corner band midpoint", (B["fmin"] + B["fmax"]) / 2, (A["fmin"] + A["fmax"]) / 2),
                  ("slow-corner band midpoint", (B["smin"] + B["smax"]) / 2, (A["smin"] + A["smax"]) / 2),
                  ("worst in-band (A fast max, B fast min)", B["fmin"], A["fmax"])) + ((("nextpnr SDF", B["sdf"], A["sdf"]),) if sdf else ()):
    sl = x - y; L = max(x, y)
    print("  %-40s A %7.0f  B %7.0f  slack %+7.0f ps = %+.2f x median error (%.1f %% of %.0f) = %+.2f x worst short-ring error (%.0f %%)" % (lab, y, x, sl, sl / (a.err * L) if L else 0, 100 * a.err, L, sl / (a.err7 * L) if L else 0, 100 * a.err7))
if SDFI is not None:
    ca, ra, ma = sdf_path(pa, sn); cb, rb, mb = sdf_path(pb, sn)
    print("NEXTPNR SDF (nominal; from the cell driving the split):")
    print("  path A: cells %d + routing %d = %d ps%s" % (ca, ra, ca + ra, ("   UNMAPPED: " + ", ".join(ma)) if ma else ""))
    print("  path B: cells %d + routing %d = %d ps%s" % (cb, rb, cb + rb, ("   UNMAPPED: " + ", ".join(mb)) if mb else ""))
    sl = (cb + rb) - (ca + ra); L = max(ca + ra, cb + rb)
    print("  slack %+d ps = %+.2f x median error (%.1f %% of %d ps) = %+.2f x worst short-ring error (%.0f %%)%s" % (sl, sl / (a.err * L) if L else 0, 100 * a.err, L, sl / (a.err7 * L) if L else 0, 100 * a.err7, "  (partial: unmapped arcs above)" if ma or mb else ""))
    print("  (the ring data also fit measured = 0.938 x SDF + 988 ps per ring period: a ~1 ns constant the SDF does not charge;")
    print("   whether it falls on one of these two paths and not the other is not known)")
