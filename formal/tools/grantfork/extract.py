#!/usr/bin/env python3
"""Probe C-10i front end (UNTRUSTED evidence): per bd_arbiter instance of a routed
design, the delays that decide the GRANT-FORK race (H_GRANT_FORK, C-12c item 3),
as integer-ps intervals per corner variant, plus the Lean data file whose
verdicts the kernel decides (Formal/Timing/GrantForkInst.lean).

    python3 -I extract.py                 # all designs below -> build/
    python3 -I extract.py --lean PATH     # also write the Lean instance file

The race, client 2 direction (client 1 is the mirror: q falls, r1 rises, g1 = r1.q
runt on O5).  q rises at T (r1 asked alone, A0 low).  r2 rises after q's feedback
copy has reached ustate's own q pin (no q runt: tier 3 excluded), but before q's
other copy reaches ugrant's q pin: ugrant reads r2 & ~q(old), g2 runs high.

Quantities (one client k; "sfx" = the part of a routed net after the point where
the two branches to ustate and ugrant split; the shared prefix cancels exactly,
H_SHARED_PREFIX, the same argument as rule J's `c` but computed exactly from the
RC tree, tcheck/extract.Prjx.split):
    dqg  q net suffix to ugrant's q pin       (route + site pin, prjxray RC tree)
    dqs  q net suffix to ustate's own q pin
    drg  r_k net suffix to ugrant's r_k pin
    drs  r_k net suffix to ustate's r_k pin
    agq  ugrant arc q pin -> O6 (k=2) / O5 (k=1)   (prjxray LUT arc, physical pin)
    agr  ugrant arc r_k pin -> same output
    asq  ustate arc q pin -> O6
    asr  ustate arc r_k pin -> O6
Transport window (B-style per-pin pure delays):  W = (dqg+agq) - (dqs+asq) - ((drg+agr) - (drs+asr))
   H_GRANT_FORK (transport) holds iff W <= 0 over the variant's box.
Inertial reading (12c: r_k reaches ustate's core no earlier than q's output edge
and late enough that ustate swallows its own reversal, i.e. within its inertial
delay dst = max(asq, asr) of q's feedback arrival):
   width = dqg - (drg - drs) - max(0, dqs - dst + 1),  threshold = min(agq, agr)
   H_GRANT_FORK (inertial) holds iff width.hi < threshold.lo.

Variants: fast = [fast_min, fast_max] per element, slow = [slow_min, slow_max]
(independent box per element, as tcheck's variants), and the four consistent
corners FMIN FMAX SMIN SMAX (every element at that column; point values), and
sdf = nextpnr's own SDF numbers (no split: full nets, point values).
Fallback: a net whose split cannot be computed (driver not a CLB, e.g. a pad)
uses the SDF guard band [.772 d, 1.155 d] of the WHOLE net per sink, without
prefix cancellation (pessimistic, flagged `fb`).
"""
import argparse
import json
import math
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
TCHECK = HERE.parent / "tcheck"
sys.path.insert(0, str(TCHECK))
import extract as E  # noqa: E402  (tcheck's extractor: Prjx, load_rules)

REPO = HERE.parent.parent.parent
DESIGNS = [(f"gcd_hw_{s}", TCHECK / f"build/tree_{s}/cells/build/hw/gcd_hw", "gcd_hw") for s in ("2", "3", "4", "d")]
DESIGNS += [(f"link_arb_s{s}", HERE.parent / "fasm2lean2/build", f"link_arb_s{s}") for s in (1, 2, 3, 4)]
CELLS = TCHECK / "build/tree_d/cells"     # tighten.py / verify for SDF parsing only
GLO, GHI = 0.772, 1.155
COLS = {"FMIN": 0, "FMAX": 1, "SMIN": 2, "SMAX": 3}


def phys(cell, logical):
    """Physical pin (A1..A6) carrying logical LUT input `logical` (I0..I5), from
    nextpnr's X_ORIG_PORT_A* attributes (the routed JSON's connections are keyed
    by PHYSICAL pin, the INIT by LOGICAL input)."""
    hits = [p for p in ("A1", "A2", "A3", "A4", "A5", "A6")
            if logical in cell["attributes"].get("X_ORIG_PORT_" + p, "").split()]
    assert len(hits) == 1, (logical, hits)
    return hits[0]


def check_init(cell, want):
    """The logical INIT (bit i = value at I0..I4 = bits of i) equals want(I0, I1, I2)
    on I3 = I4 = 0 (ugrant ties them low)."""
    bits = cell["parameters"]["INIT"][::-1]
    for m in range(8):
        a = [bool(m >> i & 1) for i in range(3)]
        assert (bits[m] == "1") == want(*a), ("INIT", cell["parameters"]["INIT"])


def iv(c, v):
    """4-corner list -> (lo, hi) for variant v (outward integer rounding)."""
    if v in COLS:
        x = c[COLS[v]]
        return (math.floor(x), math.ceil(x))
    lo, hi = (c[0], c[1]) if v == "fast" else (c[2], c[3])
    lo, hi = min(lo, hi), max(lo, hi)
    return (math.floor(lo), math.ceil(hi))


def run_design(label, odir, top, T, R, F):
    edges, *_ = T.parse_sdf(odir / f"{top}.sdf")
    sdf = {(s, d): w for s, l in edges.items() for d, w in l}
    P = E.Prjx(R, F, odir / f"{top}.fasm", odir / f"{top}_routed.json")
    cells = P.cells
    driver = {}
    for cn, c in cells.items():
        for p, d in c.get("port_directions", {}).items():
            if d == "output":
                for b in c["connections"].get(p, []):
                    driver[b] = f"{cn}/{p}"
    arbs = sorted(cn[:-len(".ustate$LUT6")] for cn in cells if cn.endswith(".ustate$LUT6"))
    rows = []
    for a in arbs:
        st = a + ".ustate$LUT6"
        qnet = cells[st]["connections"]["O6"][0]
        qsrc = f"{st}/O6"
        for k, gc, out, want in ((1, a + ".ugrant$LUT5", "O5", lambda r1, r2, q: r1 and q),
                                 (2, a + ".ugrant$LUT6", "O6", lambda r1, r2, q: r2 and not q)):
            g = cells[gc]
            check_init(g, want)
            rpin_g, qpin_g = phys(g, f"I{k - 1}"), phys(g, "I2")
            rpin_s, qpin_s = phys(cells[st], f"I{k - 1}"), phys(cells[st], "I2")
            rnet = g["connections"][rpin_g][0]
            assert g["connections"][qpin_g] == [qnet] and cells[st]["connections"][qpin_s] == [qnet], (a, k, "q")
            assert cells[st]["connections"][rpin_s] == [rnet], (a, k, "r")
            rsrc = driver[rnet]
            names = dict(qg=(qsrc, f"{gc}/{qpin_g}"), qs=(qsrc, f"{st}/{qpin_s}"),
                         rg=(rsrc, f"{gc}/{rpin_g}"), rs=(rsrc, f"{st}/{rpin_s}"))
            arcs = dict(agq=(f"{gc}/{qpin_g}", f"{gc}/{out}"), agr=(f"{gc}/{rpin_g}", f"{gc}/{out}"),
                        asq=(f"{st}/{qpin_s}", f"{st}/O6"), asr=(f"{st}/{rpin_s}", f"{st}/O6"))
            fb = []
            c4 = {}
            sq = P.split(qsrc, names["qs"][1], names["qg"][1])
            if sq is None:
                fb.append("q")
            else:
                c4["dqs"], c4["dqg"] = sq[1], sq[2]
                c4["cq"] = sq[0]
            sr = P.split(rsrc, names["rs"][1], names["rg"][1])
            if sr is None:
                fb.append("r")
            else:
                c4["drs"], c4["drg"] = sr[1], sr[2]
                c4["cr"] = sr[0]
            for key, (s_, d_) in arcs.items():
                v = P.iopath(s_, d_)
                if v is None:
                    fb.append(key)
                else:
                    c4[key] = v
            sd = {k2: sdf.get(v2) for k2, v2 in {**names, **arcs}.items()}
            row = dict(design=label, inst=a, client=k, out=out, pins=dict(
                ugrant_q=qpin_g, ugrant_r=rpin_g, ustate_q=qpin_s, ustate_r=rpin_s),
                rsrc=rsrc, fallback=fb, sdf=sd,
                c4={k2: [round(x, 1) for x in v2] for k2, v2 in c4.items()})
            V = {}
            for v in ("fast", "slow", "FMIN", "FMAX", "SMIN", "SMAX", "sdf"):
                d = {}
                for key, sname in (("dqg", "qg"), ("dqs", "qs"), ("drg", "rg"), ("drs", "rs")):
                    if v == "sdf":
                        x = sd[sname]
                        d[key] = (x, x)
                    elif key in c4:
                        d[key] = iv(c4[key], v)
                    else:      # H_FALLBACK_BAND on the whole net
                        x = sd[sname]
                        d[key] = (math.floor(GLO * x), math.ceil(GHI * x))
                for key in ("agq", "agr", "asq", "asr"):
                    if v == "sdf":
                        x = sd[key]
                        d[key] = (x, x)
                    elif key in c4:
                        d[key] = iv(c4[key], v)
                    else:
                        x = sd[key]
                        d[key] = (math.floor(GLO * x), math.ceil(GHI * x))
                Whi = (d["dqg"][1] + d["agq"][1] - d["dqs"][0] - d["asq"][0]
                       - d["drg"][0] - d["agr"][0] + d["drs"][1] + d["asr"][1])
                Wlo = (d["dqg"][0] + d["agq"][0] - d["dqs"][1] - d["asq"][1]
                       - d["drg"][1] - d["agr"][1] + d["drs"][0] + d["asr"][0])
                wid = (d["dqg"][1] - d["drg"][0] + d["drs"][1]
                       - max(0, d["dqs"][0] - max(d["asq"][1], d["asr"][1]) + 1))
                thr = min(d["agq"][0], d["agr"][0])
                V[v] = dict(iv=d, W=(Wlo, Whi), transport_ok=Whi <= 0,
                            width_hi=wid, thr_lo=thr, inertial_ok=wid < thr)
            row["V"] = V
            rows.append(row)
    return rows


LEAN_HEAD = """import Formal.Timing.GrantFork

/-!
# C-10i: H_GRANT_FORK verdicts per routed bd_arbiter instance (GENERATED)

Generated by `formal/tools/grantfork/extract.py --lean`. Every number is an
integer-ps interval (outward-rounded prjxray / SDF data, UNTRUSTED extraction,
see the notes); every verdict below is decided by the kernel (`decide`) on the
proved checkers `okT` / `okI` of `Formal.Timing.GrantFork`, whose meaning is
`okT_iff` / `okI_iff` (and through them `fork_runt_iff` / `inertial_runt_iff`).
-/

namespace Formal.Timing.GrantFork.Inst
open Formal.Timing.GrantFork

"""


def lean_name(row, v):
    d = row["design"].replace("gcd_hw_", "g").replace("link_arb_s", "l")
    i = row["inst"].replace("urig.udut.ucontrol_", "").replace(".", "_")
    return f"{d}_{i}_c{row['client']}_{v}"


def write_lean(rows, path):
    out = [LEAN_HEAD]
    nT = nI = 0
    for r in rows:
        for v, x in r["V"].items():
            d = x["iv"]
            nm = lean_name(r, v)
            box = ("{ dqg := ⟨%d, %d⟩, dqs := ⟨%d, %d⟩, drg := ⟨%d, %d⟩, drs := ⟨%d, %d⟩,\n"
                   "    agq := ⟨%d, %d⟩, agr := ⟨%d, %d⟩, asq := ⟨%d, %d⟩, asr := ⟨%d, %d⟩ }") % tuple(
                       y for k in ("dqg", "dqs", "drg", "drs", "agq", "agr", "asq", "asr") for y in d[k])
            out.append(f"def {nm} : Box :=\n  {box}\n")
            out.append(f"theorem {nm}_wf : {nm}.wf = true := by decide")
            out.append(f"theorem {nm}_T : okT {nm} = {'true' if x['transport_ok'] else 'false'} := by decide")
            out.append(f"theorem {nm}_I : okI {nm} = {'true' if x['inertial_ok'] else 'false'} := by decide\n")
            nT += x["transport_ok"]
            nI += x["inertial_ok"]
    out.append("end Formal.Timing.GrantFork.Inst\n")
    pathlib.Path(path).write_text("\n".join(out))
    return nT, nI


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean")
    ap.add_argument("--only")
    ap.add_argument("--part", help="internal: extract ONE design into build/part_LABEL.json")
    a = ap.parse_args()
    sys.argv = [sys.argv[0]]
    (HERE / "build").mkdir(exist_ok=True)
    if a.part:
        # ONE design per process: fasm2lean / ringdelay keep per-fabric state in
        # module-level caches, and a second design extracted in the same process
        # was seen to read stale state (spurious floating LV nodes, different
        # numbers).  Found 2026-10-27 by running a design alone vs. after others.
        T, R, F = E.load_rules(CELLS)
        label, odir, top = next(d for d in DESIGNS if d[0] == a.part)
        rs = run_design(label, odir, top, T, R, F)
        json.dump(rs, open(HERE / f"build/part_{label}.json", "w"))
        return
    import subprocess
    rows = []
    for label, odir, top in DESIGNS:
        if a.only and a.only not in label:
            continue
        subprocess.run([sys.executable, "-I", str(HERE / "extract.py"), "--part", label], check=True)
        rs = json.load(open(HERE / f"build/part_{label}.json"))
        rows += rs
        print(f"{label}: {len(rs)} arbiter-clients", file=sys.stderr)
    json.dump(rows, open(HERE / "build/grantfork.json", "w"), indent=1)
    with open(HERE / "build/grantfork.tsv", "w") as f:
        f.write("design\tinst\tclient\tpins(ug q,r / st q,r)\tfallback\tvariant\tW_lo\tW_hi\ttransport\twidth_hi\tthr_lo\tinertial\n")
        for r in rows:
            p = r["pins"]
            for v, x in r["V"].items():
                f.write(f"{r['design']}\t{r['inst']}\t{r['client']}\t{p['ugrant_q']},{p['ugrant_r']}/{p['ustate_q']},{p['ustate_r']}"
                        f"\t{','.join(r['fallback']) or '-'}\t{v}\t{x['W'][0]}\t{x['W'][1]}\t"
                        f"{'ok' if x['transport_ok'] else 'FAIL'}\t{x['width_hi']}\t{x['thr_lo']}\t"
                        f"{'ok' if x['inertial_ok'] else 'FAIL'}\n")
    if a.lean:
        nT, nI = write_lean(rows, a.lean)
        print(f"lean: {len(rows) * 7} boxes, transport ok {nT}, inertial ok {nI}", file=sys.stderr)


if __name__ == "__main__":
    main()
