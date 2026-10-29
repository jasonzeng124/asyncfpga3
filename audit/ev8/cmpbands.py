#!/usr/bin/env python3
"""ev8: compare the formal input bands (net.json + bands_<corner>.json, as committed in
formal/tools-A/xaudit) with my own xrc arcs, for the 4 arcs of each arbiter ENTRY race,
and recompute the ENTRY margin from the FORMAL bands with my own formula (no formal code).

    python3 cmpbands.py BUILD_DIR NET.json BANDS_DIR [--lv2] [--nomux]
"""
import os, re, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import entry  # noqa: E402  (its --lv2/--nomux switches act on import)
xrc = entry.xrc

bd, netf, bdir = [a for a in sys.argv[1:] if not a.startswith("--")]
R = xrc.Route(bd)
C = R.cells
N = list(json.load(open(netf))["modules"].values())[0]
drv = {}
for cn, c in N["cells"].items():
    for p, d in c["port_directions"].items():
        if d == "output":
            for b in c["connections"][p]:
                drv[b] = cn


def fpin(dst, src):
    c = N["cells"][dst]
    ps = [p for p, bb in c["connections"].items() if c["port_directions"][p] == "input" and bb and drv.get(bb[0]) == src]
    return ps[0] if len(ps) == 1 else None


def rdrv(cn, port):
    bl = C[cn]["connections"].get(port) or [None]
    d = R.driver.get(bl[0])
    return d[0] if d else None


def rpin(dst, src):
    ps = [p for p in C[dst]["connections"] if re.fullmatch(r"A[1-6]", p) and rdrv(dst, p) == src]
    return ps[0] if len(ps) == 1 else None


B = {c: json.load(open(os.path.join(bdir, f"bands_d_{c}.json"))) for c in ("slow", "fast", "gb")}
print("# arc: formal band | mine (corner band)   per corner; then ENTRY atomic from formal bands vs mine")
for cn in sorted(C):
    m = re.fullmatch(r"(.*\.uarb\d+)\.ua([12])\.u", cn)
    if not m:
        continue
    st = m.group(1) + ".ustate$LUT6"
    ins = [rdrv(cn, p) for p in C[cn]["connections"] if re.fullmatch(r"A[1-6]", p)]
    g = [d for d in ins if d and d.startswith(m.group(1) + ".ugrant")]
    a0 = [d for d in ins if d and "_f.u.genblk1" in d]
    if st not in C or len(g) != 1 or len(a0) != 1:
        continue
    g, a0 = g[0], a0[0]
    arcs = [("A0->ua", a0, cn), ("A0->ustate", a0, st), ("ustate->ugrant", st, g), ("ugrant->ua", g, cn)]
    for corner in ("slow", "fast", "gb"):
        b = B[corner]
        fb, mb = {}, {}
        for nm, s, d in arcs:
            fp, rp = fpin(d, s), rpin(d, s)
            fb[nm] = b["arcs"].get(f"{d}/{fp}")
            n, sk = R.sink_of_cellpin(d, rp)
            mb[nm] = [round(x) for x in entry.band(sk["d"], corner)]
        Fst, Fg = b["cells"][st][0], b["cells"][g][0]
        f_ent = fb["A0->ustate"][0] + Fst + fb["ustate->ugrant"][0] + Fg + fb["ugrant->ua"][0] - fb["A0->ua"][1]
        f_pp = f_ent + b["cells"][cn][0] - b["cells"][cn][1]
        print(f"{corner:4s} {cn.replace('urig.udut.', ''):30s} " + " ".join(f"{k}:{fb[k]}|{mb[k]}" for k, _, _ in arcs)
              + f"  ENTRY(formal bands, my formula) atomic {f_ent} perpin {f_pp}")
