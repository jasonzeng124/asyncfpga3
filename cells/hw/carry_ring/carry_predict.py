#!/usr/bin/env python3
"""carry_predict.py -- per-ring period of carry_ro_top as a function of the band.

    python3 cells/hw/carry_ring/carry_predict.py XRAY.sdf [--check-gen] > predicted.tsv

XRAY.sdf is cells/gls/fid/xray_delay.py's prjxray SDF of the route (the
routed JSON's instance names; (FAST_MIN : SLOW_MIN : SLOW_MAX) per arc).

The loop walk is ring_predict.py's (start at <ring>inv/O6, stay inside the
ring's instance prefix, sum every IOPATH and INTERCONNECT once around; period
= 2 x loop), generalised to a DFS because a CARRY4's CIN has arcs to all eight
outputs and only CO3 continues: the walk must find exactly ONE cycle back to
the start.

Every arc on the cycle is put in one of three classes, the way cells/gls/gen.py
annotates it under GLS_SDF_FIELD=band:
    carry  IOPATH of a CARRY4 instance      -> GLS_SDF_BAND_CELL CARRY4=y
    f7     IOPATH of a SELMUX2_1 instance   -> GLS_SDF_BAND_CELL SELMUX2_1=y
    rest   every other IOPATH and every INTERCONNECT -> GLS_SDF_BAND=x
so  P(x, yc, yf) = LO + x*R + yc*C + yf*F  exactly (up to gen.py's per-arc
rounding), with LO the FAST_MIN period and R, C, F the SLOW_MAX-FAST_MIN
spans of each class.  --check-gen recomputes P at three (x, y) points through
gen.py's own read_sdf (the code a GLS run annotates with) and fails if any
ring differs by more than 1 ps per arc.

Columns: ring g b kind n lo_ps R_ps C_ps F_ps arcs flags, then P at
(x=0.288, y=0.2), (0.288, 1.0), FAST_MIN (0,0) and SLOW_MAX (1,1).
flags: 'nonxray' when an arc on the loop is not from prjxray (xray_delay kept
nextpnr's number: all three columns equal, e.g. a CO3->CIN across the
Y49/Y50 clock-region boundary), else 'ok'.
"""
import importlib.util
import os
import re
import subprocess
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
GLS = os.path.abspath(os.path.join(HERE, "..", "..", "gls"))

B, G = 8, 8
KINDS = ["L8", "C1", "C4", "F8", "C16", "L16", "C32", "F16"]   # KIND[(g+b)%8], carry_ro_top.v


def kind(g, b):
    return KINDS[(g + b) % 8]


RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_CT = re.compile(r'\(CELLTYPE\s+"?([^")]+)"?\)')
RE_IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")


def unesc(s):
    return s.replace("\\", "")


def parse(path):
    """-> {src pin: [(dst pin, (lo, smin, hi), class)]}"""
    E = defaultdict(list)
    inst = ct = None
    for line in open(path):
        m = RE_IC.search(line)
        if m:
            E[unesc(m.group(1))].append((unesc(m.group(2)),
                                         tuple(int(m.group(k)) for k in (3, 4, 5)), "rest"))
            continue
        m = RE_CT.search(line)
        if m:
            ct = m.group(1)
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1))
            continue
        m = RE_IO.search(line)
        if m and inst is not None:
            cls = {"CARRY4": "carry", "SELMUX2_1": "f7"}.get(ct, "rest")
            E["%s/%s" % (inst, m.group(1))].append(
                ("%s/%s" % (inst, m.group(2)), tuple(int(m.group(k)) for k in (3, 4, 5)), cls))
    return E


def inst_of(pin):
    return pin.rpartition("/")[0]


def cycles(E, pref):
    """every simple path from <pref>inv/O6 back to itself inside the prefix"""
    start = pref + "inv/O6"
    out = []
    stack = [(start, [])]
    while stack:
        pin, path = stack.pop()
        for d, w, cls in E.get(pin, ()):
            if not inst_of(d).startswith(pref):
                continue
            if d == start:
                out.append(path + [(pin, d, w, cls)])
                continue
            if any(p == d for p, _, _, _ in path) or len(path) > 2000:
                continue
            stack.append((d, path + [(pin, d, w, cls)]))
    return out


def ring_terms(E, g, b):
    pref = "grp[%d].ro[%d]." % (g, b)
    cyc = cycles(E, pref)
    if len(cyc) != 1:
        return None, "%d cycles" % len(cyc)
    lo = 0
    span = {"rest": 0, "carry": 0, "f7": 0}
    ncls = {"rest": 0, "carry": 0, "f7": 0}
    flag = "ok"
    for _s, _d, (a, _m, c), cls in cyc[0]:
        lo += a
        span[cls] += c - a
        ncls[cls] += 1
        # prjxray charges a CO3->CIN link 0 ps (9 ps across the HCLK row); a
        # link it could not resolve keeps nextpnr's 110 ps in every column
        if cls == "rest" and a == c and a > 50 and _s.endswith("/CO3") and _d.endswith("/CIN"):
            flag = "nonxray"
    # period = 2 x loop
    return dict(lo=2 * lo, R=2 * span["rest"], C=2 * span["carry"], F=2 * span["f7"],
                arcs=len(cyc[0]), ncarry=ncls["carry"], nf7=ncls["f7"], flag=flag,
                path=cyc[0]), None


def period(t, x, yc, yf):
    return t["lo"] + x * t["R"] + yc * t["C"] + yf * t["F"]


def load_all(sdf):
    E = parse(sdf)
    res, bad = {}, []
    for g in range(G):
        for b in range(B):
            t, err = ring_terms(E, g, b)
            if t is None:
                bad.append((g, b, err))
            else:
                res[(g, b)] = t
    return res, bad


def gen_periods(sdf, x, y):
    """periods through gen.py's read_sdf (child process: gen.py reads its env at import)"""
    env = {k: v for k, v in os.environ.items() if not k.startswith("GLS_")}
    env.update(GLS_SDF_FIELD="band", GLS_SDF_BAND=repr(x),
               GLS_SDF_BAND_CELL="CARRY4=%r,SELMUX2_1=%r" % (y, y))
    r = subprocess.run([sys.executable, __file__, "--gen-child", sdf], env=env,
                       capture_output=True, text=True)
    if r.returncode:
        sys.exit("gen child failed:\n" + r.stderr[-3000:])
    out = {}
    for ln in r.stdout.splitlines():
        if ln.startswith("P "):
            _, g, b, p = ln.split()
            out[(int(g), int(b))] = int(p)
    return out


def gen_child(sdf):
    import tempfile
    work = tempfile.mkdtemp(prefix="carry_gen_")
    os.symlink(os.path.abspath(sdf), os.path.join(work, "routed.sdf"))
    os.environ["GLS_WORK"] = work
    spec = importlib.util.spec_from_file_location("gen", os.path.join(GLS, "gen.py"))
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    iop, ic, *_ = gen.read_sdf(gen.SDF)
    E = defaultdict(list)
    for s, d, ps in ic:
        E[s].append((d, (ps, ps, ps), "rest"))
    for inst, lst in iop.items():
        for a, z, ps in lst:
            E["%s/%s" % (inst, a)].append(("%s/%s" % (inst, z), (ps, ps, ps), "rest"))
    for g in range(G):
        for b in range(B):
            t, _ = ring_terms(E, g, b)
            if t:
                print("P %d %d %d" % (g, b, t["lo"]))


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--gen-child":
        gen_child(sys.argv[2])
        return 0
    sdf = sys.argv[1]
    res, bad = load_all(sdf)
    for g, b, err in bad:
        print("# WALK FAILED grp[%d].ro[%d] (%s): %s" % (g, b, kind(g, b), err), file=sys.stderr)
    print("ring\tg\tb\tkind\tn\tlo_ps\tR_ps\tC_ps\tF_ps\tarcs\tncarry\tnf7\tflag\t"
          "P_x288_y02\tP_x288_y10\tP_fastmin\tP_slowmax")
    for (g, b), t in sorted(res.items()):
        k = kind(g, b)
        print("g%d.b%d\t%d\t%d\t%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%s\t%.0f\t%.0f\t%.0f\t%.0f" % (
            g, b, g, b, k[0], k[1:], t["lo"], t["R"], t["C"], t["F"], t["arcs"], t["ncarry"], t["nf7"],
            t["flag"], period(t, 0.288, 0.2, 0.2), period(t, 0.288, 1.0, 1.0),
            period(t, 0, 0, 0), period(t, 1, 1, 1)))
    rc = 1 if bad else 0
    if "--check-gen" in sys.argv:
        worst = 0
        for x, y in ((0.288, 0.2), (0.25, 1.0), (1.0, 0.5)):
            gp = gen_periods(sdf, x, y)
            for k, t in res.items():
                d = abs(gp.get(k, -10 ** 9) - period(t, x, y, y))
                worst = max(worst, d - t["arcs"])     # 0.5 ps rounding per arc, x2 for the period
        print("# check-gen: gen.py read_sdf vs linear terms, worst excess over 1 ps/arc: %.1f ps -> %s"
              % (worst, "OK" if worst <= 0 else "MISMATCH"), file=sys.stderr)
        rc = rc or (worst > 0)
    return rc


if __name__ == "__main__":
    sys.exit(main())
