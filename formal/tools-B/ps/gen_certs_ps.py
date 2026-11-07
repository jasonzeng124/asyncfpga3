#!/usr/bin/env python3
"""Shard B (UNTRUSTED generator; every certificate is checked in Lean by CertPS.certOK): hold certificates for the
RaceTablePS rows. For each row (out/target_ps_races.json), its episode path's LUT steps (cause = the storage node
itself, then outward to the gate whose pin the node reads back) become CRows. At each step: the controlling set is
the path pin plus the fewest other non-tied pins (each a STATIC premise) that fix the INIT to the gate's value just
before a flip of the storage node in a simb.py dump; the feedback pin is fixed (memory row) only if needed.
usage: gen_certs_ps.py NET.json RACES.json DUMP.json OUTDIR(Formal/Cells) [maxrows]   (env MAXC: netlist chunks per file)"""
import json, sys, itertools, os
N = json.load(open(sys.argv[1])); R = json.load(open(sys.argv[2]))["rows"]
DUMPS = [json.load(open(p))["nodes"] for p in sys.argv[3].split(",")]   # several dumps: tried in order
D = DUMPS[0]
NAME = os.environ.get("NAME", "CertRowsPS")                              # module family name
ONLY = set(open(os.environ["ONLY"]).read().split()) if os.environ.get("ONLY") else None
OUT = sys.argv[4]; MAXR = int(sys.argv[5]) if len(sys.argv) > 5 else 10 ** 9
gates = N["gates"]; drv = {g["out"]: gi for gi, g in enumerate(gates)}
RST = 186905; RLEN = 400000
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
bl = lambda l: "[" + ", ".join("true" if b else "false" for b in l) + "]"
nl = lambda l: "[" + ", ".join(str(x) for x in l) + "]"
def ctlset(g, q, j, t0):
    k, I = g["k"], g["init"]; pins = [chain(n) for n in g["ins"]]; w = val(q, t0)
    fix = {i: bool(gates[drv[s]]["init"] & 1) for i, (ch, s) in enumerate(pins) if isconst(s)}
    fb = [i for i, (ch, s) in enumerate(pins) if s == q]
    free = [i for i in range(k) if i not in fix and i not in fb and i != j]
    for mem in (False, True):
        if mem and not fb: break
        for r in range(0, len(free) + 1):
            for extra in itertools.combinations(free, r):
                f = dict(fix); P = [j] + list(extra)
                for i in P: f[i] = val(pins[i][1], t0)
                if mem: f[fb[0]] = w
                if all(((I >> a) & 1) == w for a in range(1 << k) if all(((a >> i) & 1) == v for i, v in f.items())):
                    return dict(P=sorted(P), w=w, mem=mem, fb=fb[0] if mem else k, pins=pins, held=[i in fix for i in range(k)],
                                ov=[fix.get(i, False) for i in range(k)], bv=[val(pins[i][1], t0) if i in P else False for i in range(k)])
    return None
def swrows(q0, npins, ja, jf, t0, ackw):
    """force row F (ja at the old ack value, fb free) and confirm row C (fb = new value, ja free), at the flip."""
    g = gates[q0]; k, I = g["k"], g["init"]; tf = t0 + 1
    D_ = D; wn = val(q0, tf)
    fix = {i: bool(gates[drv[s_]]["init"] & 1) for i, (ch, s_) in enumerate(npins) if isconst(s_)}
    held = [i in fix for i in range(k)]; ov = [fix.get(i, False) for i in range(k)]
    free = [i for i in range(k) if i not in fix and i not in (ja, jf)]
    def mk(base, extra_fixed):
        for r_ in range(0, len(free) + 1):
            for ex in itertools.combinations(free, r_):
                f_ = dict(fix); f_.update(extra_fixed)
                for i in ex: f_[i] = val(npins[i][1], tf)
                if all(((I >> a) & 1) == wn for a in range(1 << k) if all(((a >> i) & 1) == v for i, v in f_.items())):
                    return sorted(list(base) + list(ex)), f_
        return None
    F = mk([ja], {ja: ackw})
    C = mk([], {jf: wn})
    if F is None or C is None: return None
    def txt(P, f_, fb, mem):
        bv = [f_.get(i, False) if i in P else False for i in range(k)]
        return "⟨%d, [%s], %s, %s, %s, %d, %s, %s, %s⟩" % (q0, ", ".join("(%s, %d)" % (nl(ch), s_) for ch, s_ in npins), nl(P), bl(bv),
            "true" if wn else "false", fb, "true" if mem else "false", bl(held), bl(ov))
    return txt(F[0], F[1], k, False), txt(C[0], C[1], jf, True)

certs = []; skipped = []; PREMS = []
for row in R[:MAXR]:
  if ONLY is not None and row["node"] not in ONLY: continue
  done = None
  for D in DUMPS:
    q0 = row["gate"]
    flips = [s for s in D.get(str(q0), [0, []])[1] if s > RLEN]
    lut = [(g, p) for g, p in row["path"] if gates[g]["k"] > 1 or gates[g]["init"] != 2]
    steps = list(reversed(lut[:-1]))       # outward from the node; the last entry is the node reading its ack
    if row.get("a0pin") is not None: steps = steps + [(row["a0pin"], 0)]   # arbiters: the copy gate driving A0's pin node
    for tf in flips[:6]:
        t0 = tf - 1; crows = []; statics = []; ok = True; prev = q0
        for si, (g, p) in enumerate(steps):
            cs = ctlset(gates[g], g, p, t0)
            if cs is None or chain(gates[g]["ins"][p])[1] != prev: ok = False; break
            labs = []
            for i in range(gates[g]["k"]):
                if i == p: labs.append((0, 0) if si == 0 else (2, si - 1))
                elif i in cs["P"]:
                    s = cs["pins"][i][1]
                    if (s, cs["bv"][i]) not in statics: statics.append((s, cs["bv"][i]))
                    labs.append((1, statics.index((s, cs["bv"][i]))))
                else: labs.append((0, 0))
            crows.append((g, cs, labs)); prev = g
        if ok and steps: done = (t0, crows, statics, val(q0, t0)); break
    if done is not None: break
  if done is None: skipped.append(row["node"]); continue
  if True:
    t0, crows, statics, cv = done
    rtxt = []
    for g, cs, labs in crows:
        pins = ", ".join("(%s, %d)" % (nl(ch), s) for ch, s in cs["pins"])
        rtxt.append("⟨⟨%d, [%s], %s, %s, %s, %d, %s, %s, %s⟩, [%s]⟩" % (g, pins, nl(cs["P"]), bl(cs["bv"]), "true" if cs["w"] else "false",
                    cs["fb"], "true" if cs["mem"] else "false", bl(cs["held"]), bl(cs["ov"]), ", ".join("⟨%d, %d⟩" % l for l in labs)))
    prem = "⟨%d, %s, %s, %s⟩" % (q0, "true" if cv else "false", nl([s for s, v in statics]), bl([v for s, v in statics]))
    npins = [chain(n) for n in gates[q0]["ins"]]
    ja = row["path"][-1][1]; jf = [i for i, (ch, src) in enumerate(npins) if src == q0][0]
    sw = None if os.environ.get("CERTONLY") else swrows(q0, npins, ja, jf, t0, crows[-1][1]["w"])
    if sw is None and not os.environ.get("CERTONLY"): skipped.append(row["node"] + "(no force/confirm)"); continue
    ntxt = "⟨%d, [%s], [], [], false, 0, false, [], []⟩" % (q0, ", ".join("(%s, %d)" % (nl(ch), src) for ch, src in npins))
    certs.append((row["node"], prem, rtxt, len(statics), ntxt, ja, jf, sw))
    PREMS.append(dict(node=row["node"], gate=q0, cause_value=bool(cv), flip_time_in_dump=t0 + 1,
                      statics=[dict(node=N["nodes"][s_], value=bool(v_)) for s_, v_ in statics],
                      memory_rows=[N["nodes"][g] for g, cs, labs in crows if cs["mem"]],
                      steps=[N["nodes"][g] for g, cs, labs in crows], ack_pin=ja, feedback_pin=jf))
import os
C = 2500; MAXC = int(os.environ.get("MAXC", "10"))
def lnest(xs):
    acc = xs[0]
    for x in xs[1:]: acc = "⟨%s, %s⟩" % (acc, x)
    return acc
def chunks_of(rt):
    import re
    return {int(x) // C for x in re.findall(r"\d+", " ".join(rt)) if int(x) < 186873}
files = []; cur = []; cs = set()
for i, (nm, prem, rt, ns, _n, _a, _f, _s) in enumerate(certs):
    ch = chunks_of(rt)
    if cur and len(cs | ch) > MAXC: files.append((cur, cs)); cur = []; cs = set()
    cur.append(i); cs |= ch
if cur: files.append((cur, cs))
D = os.path.join(OUT, NAME); os.makedirs(D, exist_ok=True)
for fi, (idx, cs) in enumerate(files):
    L = ["import Formal.Cells.CertPS", "", "/-! GENERATED by tools-B/ps/gen_certs_ps.py: certificates %d-%d (%d netlist chunks). -/" % (idx[0], idx[-1], len(cs)), "",
         "namespace Formal.Cells." + NAME, "open Formal.Cells.CertPS Formal.Cells.RaceCertPS", ""]
    for i in idx:
        nm, prem, rt, ns = certs[i][:4]
        L += ["set_option maxRecDepth 100000 in", "/-- %s (%d LUT steps, %d static premises) -/" % (nm, len(rt), ns),
              "def c%03d : Prem × List CRow := (%s, [\n  %s])" % (i, prem, ",\n  ".join(rt)), ""]
    L += ["set_option maxRecDepth 100000 in", "def certs%02d : List (Prem × List CRow) := [%s]" % (fi, ", ".join("c%03d" % i for i in idx)), "",
          "set_option maxHeartbeats 0 in", "set_option maxRecDepth 100000 in",
          "theorem certs%02d_ok : certs%02d.all (fun pc => certOK pc.1 pc.2) = true := by decide +kernel" % (fi, fi), "",
          "end Formal.Cells." + NAME, ""]
    open(os.path.join(D, "B%02d.lean" % fi), "w").write("\n".join(L))
RN = NAME.replace("CertRows", "RaceAll")
if os.environ.get("CERTONLY"): RN = None
DR = os.path.join(OUT, RN or "_none")
if RN: os.makedirs(DR, exist_ok=True)
for fi, (idx, cs) in enumerate(files if RN else []):
    L = ["import Formal.Cells.%s.B%02d" % (NAME, fi), "import Formal.Cells.CertSwitchAll", "",
         "/-! GENERATED by tools-B/ps/gen_certs_ps.py: race rows for certificates %d-%d. -/" % (idx[0], idx[-1]), "",
         "namespace Formal.Cells.%s" % RN, "open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.%s" % NAME, ""]
    rows = []
    for i in idx:
        nm, prem, rt, ns, ntxt, ja, jf, sw = certs[i]
        rows.append("⟨c%03d, %s, %d, %d⟩" % (i, ntxt, ja, jf))
    L += ["set_option maxRecDepth 100000 in", "def races%02d : List RaceRow := [\n  %s]" % (fi, ",\n  ".join(rows)), "",
          "theorem races%02d_certs : races%02d.map RaceRow.pc = certs%02d := rfl" % (fi, fi, fi), "",
          "set_option maxHeartbeats 0 in", "set_option maxRecDepth 100000 in",
          "theorem races%02d_ok : races%02d.all raceOK = true := by decide +kernel" % (fi, fi), "",
          "theorem races%02d_full : ∀ r ∈ races%02d, certOK r.pc.1 r.pc.2 = true ∧ raceOK r = true := by" % (fi, fi),
          "  intro r hr",
          "  have h1 := List.mem_map_of_mem (f := RaceRow.pc) hr",
          "  rw [races%02d_certs] at h1" % fi,
          "  exact ⟨(List.all_eq_true.1 certs%02d_ok) _ h1, (List.all_eq_true.1 races%02d_ok) r hr⟩" % (fi, fi), ""]
    swl = ["⟨⟨c%03d, %s, %d, %d⟩, %s, %s⟩" % (i, certs[i][4], certs[i][5], certs[i][6], certs[i][7][0], certs[i][7][1])
           for i in idx if certs[i][7] is not None]
    L += ["set_option maxRecDepth 100000 in", "def sw%02d : List SwRow := [%s]" % (fi, ",\n  ".join(swl)), "",
          "set_option maxHeartbeats 0 in", "set_option maxRecDepth 100000 in",
          "theorem sw%02d_ok : sw%02d.all swOK = true := by decide +kernel" % (fi, fi), "",
          "theorem sw%02d_rr : sw%02d.map SwRow.rr = races%02d := rfl" % (fi, fi, fi), "",
          "theorem sw%02d_full : ∀ s ∈ sw%02d, certOK s.rr.pc.1 s.rr.pc.2 = true ∧ raceOK s.rr = true ∧ swOK s = true := by" % (fi, fi),
          "  intro s hs",
          "  have h1 := List.mem_map_of_mem (f := SwRow.rr) hs",
          "  rw [sw%02d_rr] at h1" % fi,
          "  exact ⟨(races%02d_full _ h1).1, (races%02d_full _ h1).2, (List.all_eq_true.1 sw%02d_ok) s hs⟩" % (fi, fi, fi), "",
          "end Formal.Cells.%s" % RN, ""]
    open(os.path.join(DR, "B%02d.lean" % fi), "w").write("\n".join(L))
nf = len(files)
EXCL = set(int(x) for x in os.environ.get("EXCLUDE", "").split(",") if x)   # files too large for one kernel check
KEEP = [i for i in range(nf) if i not in EXCL]
for i in sorted(EXCL):
    for d_ in (D, DR):
        p_ = os.path.join(d_, "B%02d.lean" % i)
        if os.path.exists(p_): os.remove(p_)
TR = ["import Formal.Cells.%s.B%02d" % (RN, i) for i in KEEP]
TR += ["", "/-! GENERATED by tools-B/ps/gen_certs_ps.py: all race rows of this batch. -/", "",
       "namespace Formal.Cells.%s" % RN, "open Formal.Cells.CertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll", "",
       "set_option maxRecDepth 100000 in", "def races : List RaceRow := " + " ++ ".join("races%02d" % i for i in KEEP), "",
       "set_option maxRecDepth 100000 in", "theorem races_ok : races.all raceOK = true := by",
       "  simp only [races, List.all_append, " + ", ".join("races%02d_ok" % i for i in KEEP) + ", Bool.and_self]", "",
       "theorem races_full : ∀ r ∈ races, certOK r.pc.1 r.pc.2 = true ∧ raceOK r = true := by",
       "  simp only [races, List.forall_mem_append]",
       "  exact " + lnest(["races%02d_full" % i for i in KEEP]), "",
       "/-- **Every race row of this batch, in every behaviour of THE circuit** (`CertRaceAll.target_races_of`). -/",
       "theorem target_races : type_of% (@target_races_of races races_full) := @target_races_of races races_full", "",
       "set_option maxRecDepth 100000 in", "def sws : List SwRow := " + " ++ ".join("sw%02d" % i for i in KEEP), "",
       "theorem sws_full : ∀ s ∈ sws, certOK s.rr.pc.1 s.rr.pc.2 = true ∧ raceOK s.rr = true ∧ swOK s = true := by",
       "  simp only [sws, List.forall_mem_append]",
       "  exact " + lnest(["sw%02d_full" % i for i in KEEP]), "",
       "/-- **Every storage node of this batch switches cleanly, in every behaviour of THE circuit**",
       "(`CertSwitchAll.target_switches_of`; g = 1, κ ≤ 83/200, given each row's local premises). -/",
       "theorem target_switches : type_of% (@target_switches_of sws sws_full) := @target_switches_of sws sws_full", "",
       "end Formal.Cells.%s" % RN, ""]
if RN: open(os.path.join(OUT, RN + ".lean"), "w").write("\n".join(TR))
T = ["import Formal.Cells." + NAME + ".B%02d" % i for i in KEEP]
T += ["", "/-!", "# Formal.Cells." + NAME + " — hold certificates for %d of the 185 RaceTablePS rows (GENERATED)" % len(certs), "",
      "Each certificate: the storage node's own flip as the cause, its episode path's LUT steps as rows, the fewest static",
      "premises; all checked by `CertPS.certOK` (kernel decide). With `CertPS.cert_sound`, in every behaviour each listed",
      "node's acknowledge source keeps its value for the path's summed lower window ends after the node's flip, given the",
      "premises. Skipped (no certificate from the dump used): %d rows: %s." % (len(skipped), ", ".join(skipped)),
      "Left out (one certificate spans more netlist chunks than one kernel check fits in memory here): %s." % ", ".join(certs[j][0] for i in sorted(EXCL) for j in files[i][0]), "-/", "",
      "namespace Formal.Cells." + NAME, "open Formal.Cells.CertPS", "",
      "set_option maxRecDepth 100000 in", "def certs : List (Prem × List CRow) := " + " ++ ".join("certs%02d" % i for i in KEEP), "",
      "set_option maxRecDepth 100000 in", "theorem certs_ok : certs.all (fun pc => certOK pc.1 pc.2) = true := by",
      "  simp only [certs, List.all_append, " + ", ".join("certs%02d_ok" % i for i in KEEP) + ", Bool.and_self]", "",
      "set_option maxRecDepth 100000 in", "theorem certs_length : certs.length = %d := by decide" % sum(len(files[i][0]) for i in KEEP), "",
      "end Formal.Cells." + NAME, ""]
open(os.path.join(OUT, NAME + ".lean"), "w").write("\n".join(T))
if os.environ.get("OUTJSON"):
    json.dump(dict(note="UNTRUSTED generator output: the value premises of each hold certificate (Formal.Cells.%s / %s); "
                   "the certificates themselves are checked in Lean (certOK, raceOK)." % (NAME, RN), rows=PREMS, skipped=skipped),
              open(os.environ["OUTJSON"], "w"), indent=1)
print("certificates", len(certs), "files", nf, "skipped", len(skipped), skipped[:10])
