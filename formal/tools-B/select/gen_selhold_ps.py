#!/usr/bin/env python3
"""Shard B (UNTRUSTED generator; every row is checked in Lean by CertPS.certOK and SelectHold.selOK, kernel decide):
select-hold rows (`SelectHold.SelRow`) for THE target's umux*.udat latches (tools-B/select/uncovered_mux.json.xz:
latches whose data source is a 2:1 mux LUT with latch select and latch inputs at depth 0).

Per latch: a close of its enable source es (es leaving the open value cv = !pe) in a simb.py dump, at t0 = close - 1:
* the mux row: P = [select pin, selected data pin], the selected pin being the one that, with the select's value at
  t0 and the tied pins, forces the mux INIT to the mux's value at t0 (other pins free);
* two chains from es (the cause) at that close, one to the select latch, one to the selected input latch, found by a
  structural search (bestchain: simple paths of <= MAXD LUT steps, every step with a controlling set at t0 whose
  static pins do not change in the run on [t0, close + HOR]; margin at κ = 0 first, then fewest premises, then the
  largest margin). ctlcert.py (time-respecting) is NOT used: in this run the selected inputs mostly never change
  after the closes (ctlcert needs the target to change) and its window would span microseconds;
* each chain's LUT steps become CRows (controlling set = path pin + fewest static pins, memory row only if needed,
  as tools-B/ps/gen_certs_ps.py's ctlset), all at t0;
* the latch LRow, verbatim from Formal/Cells/LatchViewPS/B*.lean;
* margin ratios kA/kB per chain = min(ΣFmin(path)/(ΣFmax(e)+1), ΣSmin(path)/(ΣSmax(e)+1)) as a reduced fraction
  (maximises the κ range (1+κ)kB ≤ kA(1-κ), i.e. κ ≤ (kA-kB)/(kA+kB)); the sums are recomputed by Lean in selOK.
usage: gen_selhold_ps.py NET.json DUMP.json UMUX.json.xz LEANCELLS OUTDIR
env: MAXD (8), HOR (20000 ps), MAXV (DFS visits, 200000), MAXROWS (20), PERINST (rows per umux instance), CLOSES (closes tried per latch, 4), INST (regex on mux cell, default umux\\d+\\.udat), OUTNAME
(SelHoldPS), CHECKVARIANT, CHECKPARTS, LEANOUT (dir for the .lean file, default LEANCELLS), SKIPFIRST (skip this many candidate latches)."""
import json, sys, os, re, glob, lzma, subprocess, itertools
from fractions import Fraction
NETF, DUMPF, UMUXF, CELLS, OUTD = sys.argv[1:6]
MAXROWS = int(os.environ.get("MAXROWS", "20")); CLOSES = int(os.environ.get("CLOSES", "4"))
INST = re.compile(os.environ.get("INST", r"umux\d+\.udat")); OUTNAME = os.environ.get("OUTNAME", "SelHoldPS")
SKIP = int(os.environ.get("SKIPFIRST", "0"))
N = json.load(open(NETF)); gates = N["gates"]; names = N["nodes"]; drv = {g["out"]: gi for gi, g in enumerate(gates)}
D = json.load(open(DUMPF))["nodes"]
RLEN = 400000
os.makedirs(OUTD, exist_ok=True)

def chain(n):
    m, ch = n, []
    while m in drv and gates[drv[m]]["k"] == 1 and gates[drv[m]]["init"] == 2:
        ch.append(drv[m]); m = gates[drv[m]]["ins"][0]
    return ch, m
def isconst(s): return s in drv and gates[drv[s]]["k"] == 0
def val(n, t):
    d = D.get(str(n)); v = d[0] if d else (bool(gates[drv[n]]["init"] & 1) if isconst(n) else False)
    for s in (d[1] if d else []):
        if s <= t: v = not v
        else: break
    return v
def nc(n, t):
    for s in D.get(str(n), [0, []])[1]:
        if s >= t: return s
    return None
bl = lambda l: "[" + ", ".join("true" if b else "false" for b in l) + "]"
nl = lambda l: "[" + ", ".join(str(x) for x in l) + "]"
def forces(g, f, w):
    k, I = g["k"], g["init"]
    return all(((I >> a) & 1) == w for a in range(1 << k) if all(((a >> i) & 1) == v for i, v in f.items()))
def ctlset(g, q, j, t0, tend=None):   # = gen_certs_ps.py's ctlset (+ statics stable on [t0, tend] in the run)
    k = g["k"]; pins = [chain(n) for n in g["ins"]]; w = val(q, t0)
    fix = {i: bool(gates[drv[s]]["init"] & 1) for i, (ch, s) in enumerate(pins) if isconst(s)}
    fb = [i for i, (ch, s) in enumerate(pins) if s == q]
    free = [i for i in range(k) if i not in fix and i not in fb and i != j and (tend is None or stable(pins[i][1], t0, tend))]
    for mem in (False, True):
        if mem and not fb: break
        for r in range(0, len(free) + 1):
            for extra in itertools.combinations(free, r):
                f = dict(fix); P = [j] + list(extra)
                for i in P: f[i] = val(pins[i][1], t0)
                if mem: f[fb[0]] = w
                if forces(g, f, w):
                    return dict(P=sorted(P), w=w, mem=mem, fb=fb[0] if mem else k, pins=pins, held=[i in fix for i in range(k)],
                                ov=[fix.get(i, False) for i in range(k)], bv=[val(pins[i][1], t0) if i in P else False for i in range(k)])
    return None
def krow_txt(q, cs):
    pins = ", ".join("(%s, %d)" % (nl(ch), s) for ch, s in cs["pins"])
    return "⟨%d, [%s], %s, %s, %s, %d, %s, %s, %s⟩" % (q, pins, nl(cs["P"]), bl(cs["bv"]), "true" if cs["w"] else "false",
                                                       cs["fb"], "true" if cs["mem"] else "false", bl(cs["held"]), bl(cs["ov"]))
def arcs_of(g, i):   # SpecChain.pinArcs: the gate's pin arc, then the copy chain's arcs
    ch, _ = chain(gates[g]["ins"][i])
    return [gates[g]["arcs"][i]] + [gates[c]["arcs"][0] for c in ch]

# LatchViewPS rows: literal + parsed
rowre = re.compile(r"^  (⟨(\d+), (\d+), (\d+), (\d+), (true|false), (true|false), \[[^\]]*\], \[[^\]]*\], \[(.*)\]⟩)[,\]]?$")
pinre = re.compile(r"\(\[([\d, ]*)\], (\d+)\)")
lat = {}
for f in sorted(glob.glob(os.path.join(CELLS, "LatchViewPS", "B*.lean"))):
    for ln in open(f):
        m = rowre.match(ln.rstrip("\n"))
        if m:
            q, e, d, j = map(int, m.groups()[1:5])
            pins = [int(s) for _, s in pinre.findall(m.group(8))]
            lat[q] = dict(lit=m.group(1), q=q, e=e, d=d, j=j, pe=m.group(6) == "true", srcs=pins)

FAN = None
def fanout():
    global FAN
    if FAN is None:
        FAN = {}
        for gi, g in enumerate(gates):
            if g["k"] == 1 and g["init"] == 2: continue
            for p, n in enumerate(g["ins"]): FAN.setdefault(chain(n)[1], []).append((gi, p))
    return FAN
def stable(n, t0, tend):
    return all(not (t0 <= s <= tend) for s in D.get(str(n), [0, []])[1])
MAXD = int(os.environ.get("MAXD", "8")); HOR = int(os.environ.get("HOR", "20000")); MAXV = int(os.environ.get("MAXV", "200000"))
def bestchain(es, t0, tf, B, earcs):
    """Structural search: simple paths es -> ... -> B (<= MAXD LUT steps) whose every step has a controlling set (path
    pin + static pins stable in the run on [t0, tf + HOR], memory row if needed) at t0; among those with margin at
    κ = 0, the one with the fewest premises (static pins + memory rows, counted per step), then the largest ratio. Returns its ctlcert-style path [(gate, pin)...] from B back to es, or None."""
    F = fanout(); dist = {es: 0}; fr = [es]
    for d in range(1, MAXD + 1):
        nx = []
        for n in fr:
            for g, p in F.get(n, []):
                if g not in dist: dist[g] = d; nx.append(g)
        fr = nx
    if B not in dist: return None, "no structural path of <= %d LUT steps" % MAXD
    memo = {}
    def cs_of(g, p):
        if (g, p) not in memo: memo[(g, p)] = ctlset(gates[g], g, p, t0, tf + HOR)
        return memo[(g, p)]
    best = [None, None]; cnt = [0]
    fx = sum(a["fmax"] for a in earcs); sx = sum(a["smax"] for a in earcs)
    def dfs(n, depth, path, fn, sn, vis, npr):
        cnt[0] += 1
        if cnt[0] > MAXV: return
        g = gates[n]
        for p in range(g["k"]):
            s = chain(g["ins"][p])[1]
            if isconst(s) or s == n: continue
            if s != es and (s not in drv or s in vis or dist.get(s, 99) > MAXD - depth - 1): continue
            cs = cs_of(n, p)
            if cs is None: continue
            npr2 = npr + len(cs["P"]) - 1 + (1 if cs["mem"] else 0)
            arcs = arcs_of(n, p); fn2 = fn + sum(a["fmin"] for a in arcs); sn2 = sn + sum(a["smin"] for a in arcs)
            if s == es:
                r = min(Fraction(fn2, fx + 1), Fraction(sn2, sx + 1))
                sc = (r > 1, -npr2, r)    # margin at κ = 0 first, then fewest premises (statics + memory rows), then margin
                if best[0] is None or sc > best[0]: best[0], best[1] = sc, path + [(n, p)]
            else: dfs(s, depth + 1, path + [(n, p)], fn2, sn2, vis | {s}, npr2)
    dfs(B, 0, [], 0, 0, {B}, 0)
    if best[1] is None: return None, "no controlling chain of <= %d LUT steps (searched %d)" % (MAXD, cnt[0])
    return best[1], "ok"

def cert(es, cv, path, t0, B, tend):
    """path: chain from B back to es [(gate, pin)...]; returns (prem_txt, rows_txt, pathArcs, nstat) or None."""
    steps = [(g, p) for g, p in reversed(path) if gates[g]["k"] > 1 or gates[g]["init"] != 2]
    if not steps or steps[-1][0] != B: return None
    statics = []; rt = []; prev = es; parcs = []
    for si, (g, p) in enumerate(steps):
        cs = ctlset(gates[g], g, p, t0, tend)
        if cs is None or chain(gates[g]["ins"][p])[1] != prev: return None
        labs = []
        for i in range(gates[g]["k"]):
            if i == p: labs.append((0, 0) if si == 0 else (2, si - 1))
            elif i in cs["P"]:
                s = cs["pins"][i][1]
                if (s, cs["bv"][i]) not in statics: statics.append((s, cs["bv"][i]))
                labs.append((1, statics.index((s, cs["bv"][i]))))
            else: labs.append((0, 0))
        rt.append("⟨%s, [%s]⟩" % (krow_txt(g, cs), ", ".join("⟨%d, %d⟩" % l for l in labs)))
        parcs += arcs_of(g, p); prev = g
    prem = "⟨%d, %s, %s, %s⟩" % (es, "true" if cv else "false", nl([s for s, v in statics]), bl([v for s, v in statics]))
    return prem, rt, parcs, len(statics), [names[g] for g, p in steps]

def ratio(parcs, earcs):
    fx = sum(a["fmax"] for a in earcs); sx = sum(a["smax"] for a in earcs)
    fn = sum(a["fmin"] for a in parcs); sn = sum(a["smin"] for a in parcs)
    r = min(Fraction(fn, fx + 1), Fraction(sn, sx + 1))
    return r.numerator, r.denominator, (fx, fn, sx, sn)

U = json.load(lzma.open(UMUXF))
cases = [o for o in U if INST.search(o["mux_cell"]) and o["select"]["src_kind"] == "latch" and o["select"]["dmax"] == 0
         and all(o[x]["src_kind"] == "latch" and o[x]["dmax"] == 0 for x in ("in0", "in1"))]
print("candidate umux latches", len(cases))
PERINST = int(os.environ.get("PERINST", "1000")); ninst = {}
rows = []; report = []
for o in cases[SKIP:]:
    if len(rows) >= MAXROWS: break
    inst = re.search(r"umux\d+", o["mux_cell"]).group(0)
    if ninst.get(inst, 0) >= PERINST: continue
    q = o["latch"]; L = lat.get(q); rep = dict(latch=q, latch_name=o["latch_name"], mux=o["mux"])
    if L is None or L["srcs"][L["d"]] != o["mux"]: rep["fail"] = "no LatchViewPS row / data pin not the mux"; report.append(rep); continue
    es = L["srcs"][L["e"]]; cv = not L["pe"]; mg = gates[o["mux"]]; ps = o["select"]["pin"]
    assert drv.get(es) == es and drv.get(o["mux"]) == o["mux"]
    closes = [s for s in D.get(str(es), [0, []])[1] if s > RLEN and val(es, s - 1) == cv]
    rep["closes"] = len(closes); why = []; done = None
    for tf in closes[:CLOSES]:
        t0 = tf - 1
        mpins = [chain(n) for n in mg["ins"]]
        fix = {i: bool(gates[drv[s]]["init"] & 1) for i, (ch, s) in enumerate(mpins) if isconst(s)}
        w = val(o["mux"], t0); pd = None
        for x in ("in0", "in1"):
            pj = o[x]["pin"]; f = dict(fix); f[ps] = val(mpins[ps][1], t0); f[pj] = val(mpins[pj][1], t0)
            if forces(mg, f, w): pd = pj; break
        if pd is None: why.append("t%d: mux not forced by select + one input" % tf); continue
        sel, dat = mpins[ps][1], mpins[pd][1]
        res = []
        for B, tag in ((sel, "sel"), (dat, "dat")):
            path, msg = bestchain(es, t0, tf, B, arcs_of(q, L["e"]))
            if path is None: res.append((None, "%s: %s" % (tag, msg))); continue
            c = cert(es, cv, path, t0, B, tf + HOR)
            res.append((c, "ok" if c else "%s: CRow build failed" % tag))
        if any(c is None for c, _ in res): why.append("t%d: " % tf + "; ".join(m for c, m in res if c is None)); continue
        held = [i in fix for i in range(mg["k"])]; ov = [fix.get(i, False) for i in range(mg["k"])]
        bv = [val(mpins[i][1], t0) if i in (ps, pd) else False for i in range(mg["k"])]
        mrow = "⟨%d, [%s], %s, %s, %s, %d, false, %s, %s⟩" % (o["mux"], ", ".join("(%s, %d)" % (nl(ch), s) for ch, s in mpins),
                                                            nl([ps, pd]), bl(bv), "true" if w else "false", mg["k"], bl(held), bl(ov))
        earcs = arcs_of(q, L["e"])
        ks = [ratio(c[2], earcs) for c, _ in res]
        if any(kA <= kB for kA, kB, _ in ks): why.append("t%d: no margin at κ = 0 %s" % (tf, [k[2] for k in ks])); continue
        done = (tf, res, mrow, ps, pd, ks, w); break
    if done is None: rep["fail"] = why or ["no close of the enable after reset"]; report.append(rep); continue
    tf, res, mrow, ps, pd, ks, w = done
    kap = [float(Fraction(kA - kB, kA + kB)) for kA, kB, _ in ks]
    i = len(rows)
    rows.append(dict(i=i, q=q, c1=res[0][0], c2=res[1][0], mrow=mrow, ps=ps, pd=pd, lit=L["lit"], ks=ks))
    rep.update(close=tf, select=names[mpins[ps][1]], selected_pin=pd, selected=names[mpins[pd][1]], mux_value=w,
               kA1=ks[0][0], kB1=ks[0][1], kA2=ks[1][0], kB2=ks[1][1], sums1=ks[0][2], sums2=ks[1][2],
               kappa1=kap[0], kappa2=kap[1], kappa=min(kap), steps1=res[0][0][4], steps2=res[1][0][4],
               statics1=res[0][0][3], statics2=res[1][0][3])
    ninst[inst] = ninst.get(inst, 0) + 1
    report.append(rep); print("row", i, o["latch_name"], "κ ≤ %.3f" % min(kap), flush=True)

json.dump(dict(note="UNTRUSTED generator report (gen_selhold_ps.py); the rows are checked in Lean", rows=report),
          open(os.path.join(OUTD, OUTNAME + "_report.json"), "w"), indent=1)
if not rows: print("no rows"); sys.exit(1)
L_ = ["import Formal.Cells.SelectHold", "",
      "/-!", "# Formal.Cells.%s — select-hold rows for THE target's umux latches (GENERATED)" % OUTNAME, "",
      "GENERATED by tools-B/select/gen_selhold_ps.py from chains found on a simb.py dump (full-width pair",
      "0x49e9c618,0x35bf992e, corner 0, mid-window, broad data rule). %d rows (`SelectHold.SelRow`): each pairs two chain" % len(rows),
      "certificates from a latch's enable source (one ending at the mux's select latch, one at the selected input latch),",
      "the mux row and the latch's LatchViewPS row, with per-chain margin ratios. Checked here by kernel decide:",
      "`certs_ok` (both `certOK`s) and `sel_ok` (`selOK`). With `SelectHold.select_hold_row`, each latch's data source",
      "keeps the mux value through `(e + 1) + hi e` (the hold half), for κ in both chains' ranges",
      "(1+κ)·kB ≤ kA·(1-κ), given the certificates' premises (cause, statics, memory rows).",
      "Latches (row: latch q / mux / select / selected): " + "; ".join("%d: %d/%s" % (r["i"], r["q"], r["mrow"].split(",")[0][1:]) for r in rows) + ".",
      "-/", "", "namespace Formal.Cells." + OUTNAME,
      "open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.LatchView Formal.Cells.SelectHold", ""]
HEAD = list(L_); BLK = []
for r in rows:
    L_ = []
    for nm, c in (("a", r["c1"]), ("b", r["c2"])):
        L_ += ["set_option maxRecDepth 100000 in",
               "/-- row %d chain %s (%d LUT steps, %d static premises): %s -/" % (r["i"], nm, len(c[1]), c[3], " → ".join(c[4])),
               "def c%02d%s : Prem × List CRow := (%s, [\n  %s])" % (r["i"], nm, c[0], ",\n  ".join(c[1])), ""]
    L_ += ["set_option maxRecDepth 100000 in",
           "def r%02d : SelRow := ⟨c%02da, c%02db, %s, %d, %d,\n  %s, %d, %d, %d, %d⟩" % (
               r["i"], r["i"], r["i"], r["mrow"], r["ps"], r["pd"], r["lit"], r["ks"][0][0], r["ks"][0][1], r["ks"][1][0], r["ks"][1][1]), "",
           "set_option maxHeartbeats 0 in", "set_option maxRecDepth 100000 in",
           "theorem r%02d_certs : (certOK r%02d.c1.1 r%02d.c1.2 && certOK r%02d.c2.1 r%02d.c2.2) = true := by decide +kernel" % ((r["i"],) * 5), "",
           "set_option maxHeartbeats 0 in", "set_option maxRecDepth 100000 in",
           "theorem r%02d_sel : selOK r%02d = true := by decide +kernel" % (r["i"], r["i"]), ""]
    BLK.append(L_)
def tail(ids):
  return ["def rows : List SelRow := [%s]" % ", ".join(ids), "",
       "theorem certs_ok : ∀ r ∈ rows, certOK r.c1.1 r.c1.2 = true ∧ certOK r.c2.1 r.c2.2 = true := by",
       "  intro r hr",
       "  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr",
       "  rcases hr with %s" % " | ".join(["rfl"] * len(ids)),
       ] + ["  · simpa only [Bool.and_eq_true] using %s_certs" % x for x in ids] + ["",
       "theorem sel_ok : ∀ r ∈ rows, selOK r = true := by",
       "  intro r hr",
       "  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr",
       "  rcases hr with %s" % " | ".join(["rfl"] * len(ids)),
       ] + ["  · exact %s_sel" % x for x in ids] + ["", "end Formal.Cells." + OUTNAME, ""]
L_ = HEAD + [x for b in BLK for x in b] + tail(["r%02d" % r["i"] for r in rows])
LO = os.environ.get("LEANOUT", CELLS)
open(os.path.join(LO, OUTNAME + ".lean"), "w").write("\n".join(L_))
print("rows", len(rows), "->", os.path.join(LO, OUTNAME + ".lean"))
if os.environ.get("CHECKVARIANT"):
    # the same file without the SelectHold import: SelectHold's definitions (SelRow .. selOK) copied verbatim, for a
    # `lake env lean` check while Formal/Cells/SelectHold.olean is not built (the rows/theorems are byte-identical)
    sh = open(os.path.join(CELLS, "SelectHold.lean")).read()
    a = sh.index("namespace Formal.Cells.SelectHold"); b = sh.index("/-- **A checked select-hold row")
    V = ["import Formal.Cells.LatchHoldCert", "", sh[a:b].rstrip(), "", "end Formal.Cells.SelectHold", ""] + L_[1:]
    open(os.environ["CHECKVARIANT"], "w").write("\n".join(V)); print("check variant ->", os.environ["CHECKVARIANT"])
    NP = int(os.environ.get("CHECKPARTS", "0"))   # also: the variant split into NP parts (row blocks verbatim)
    for k in range(NP):
        sub = [i for i in range(len(rows)) if i * NP // len(rows) == k]
        Vk = V[:5] + HEAD[1:] + [x for i in sub for x in BLK[i]] + tail(["r%02d" % rows[i]["i"] for i in sub])
        pk = os.environ["CHECKVARIANT"].replace(".lean", "_p%d.lean" % k)
        open(pk, "w").write("\n".join(Vk)); print("check part ->", pk, "rows", sub)
