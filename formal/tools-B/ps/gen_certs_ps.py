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
certs = []; skipped = []
for row in R[:MAXR]:
  if ONLY is not None and row["node"] not in ONLY: continue
  done = None
  for D in DUMPS:
    q0 = row["gate"]
    flips = [s for s in D.get(str(q0), [0, []])[1] if s > RLEN]
    lut = [(g, p) for g, p in row["path"] if gates[g]["k"] > 1 or gates[g]["init"] != 2]
    steps = list(reversed(lut[:-1]))       # outward from the node; the last entry is the node reading its ack
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
    certs.append((row["node"], prem, rtxt, len(statics)))
import os
C = 2500; MAXC = int(os.environ.get("MAXC", "10"))
def chunks_of(rt):
    import re
    return {int(x) // C for x in re.findall(r"\d+", " ".join(rt)) if int(x) < 186873}
files = []; cur = []; cs = set()
for i, (nm, prem, rt, ns) in enumerate(certs):
    ch = chunks_of(rt)
    if cur and len(cs | ch) > MAXC: files.append((cur, cs)); cur = []; cs = set()
    cur.append(i); cs |= ch
if cur: files.append((cur, cs))
D = os.path.join(OUT, NAME); os.makedirs(D, exist_ok=True)
for fi, (idx, cs) in enumerate(files):
    L = ["import Formal.Cells.CertPS", "", "/-! GENERATED by tools-B/ps/gen_certs_ps.py: certificates %d-%d (%d netlist chunks). -/" % (idx[0], idx[-1], len(cs)), "",
         "namespace Formal.Cells." + NAME, "open Formal.Cells.CertPS Formal.Cells.RaceCertPS", ""]
    for i in idx:
        nm, prem, rt, ns = certs[i]
        L += ["set_option maxRecDepth 100000 in", "/-- %s (%d LUT steps, %d static premises) -/" % (nm, len(rt), ns),
              "def c%03d : Prem × List CRow := (%s, [\n  %s])" % (i, prem, ",\n  ".join(rt)), ""]
    L += ["set_option maxRecDepth 100000 in", "def certs%02d : List (Prem × List CRow) := [%s]" % (fi, ", ".join("c%03d" % i for i in idx)), "",
          "set_option maxHeartbeats 0 in", "set_option maxRecDepth 100000 in",
          "theorem certs%02d_ok : certs%02d.all (fun pc => certOK pc.1 pc.2) = true := by decide +kernel" % (fi, fi), "",
          "end Formal.Cells." + NAME, ""]
    open(os.path.join(D, "B%02d.lean" % fi), "w").write("\n".join(L))
nf = len(files)
T = ["import Formal.Cells." + NAME + ".B%02d" % i for i in range(nf)]
T += ["", "/-!", "# Formal.Cells." + NAME + " — hold certificates for %d of the 185 RaceTablePS rows (GENERATED)" % len(certs), "",
      "Each certificate: the storage node's own flip as the cause, its episode path's LUT steps as rows, the fewest static",
      "premises; all checked by `CertPS.certOK` (kernel decide). With `CertPS.cert_sound`, in every behaviour each listed",
      "node's acknowledge source keeps its value for the path's summed lower window ends after the node's flip, given the",
      "premises. Skipped (no certificate from the dump used): %d rows: %s." % (len(skipped), ", ".join(skipped)), "-/", "",
      "namespace Formal.Cells." + NAME, "open Formal.Cells.CertPS", "",
      "set_option maxRecDepth 100000 in", "def certs : List (Prem × List CRow) := " + " ++ ".join("certs%02d" % i for i in range(nf)), "",
      "set_option maxRecDepth 100000 in", "theorem certs_ok : certs.all (fun pc => certOK pc.1 pc.2) = true := by",
      "  simp only [certs, List.all_append, " + ", ".join("certs%02d_ok" % i for i in range(nf)) + ", Bool.and_self]", "",
      "set_option maxRecDepth 100000 in", "theorem certs_length : certs.length = %d := by decide" % len(certs), "",
      "end Formal.Cells." + NAME, ""]
open(os.path.join(OUT, NAME + ".lean"), "w").write("\n".join(T))
print("certificates", len(certs), "files", nf, "skipped", len(skipped), skipped[:10])
