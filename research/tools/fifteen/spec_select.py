#!/usr/bin/env python3
"""spec_select.py SDF INST [--glo 0.97 --ghi 1.03] -- the select race inside a BDC_SPEC_INC cell (bdc/emit.py).

The cell's request mux is LUT3 uspec: z_req = abort ? z_long : z_short, abort = a LUT on the unit's input data.  If
abort = 1 arrives after z_short rises, z_req rises on the short line: the long case is cut short.  The shape is rule E
(a select against a request): from each upstream bd_link's C node (the common start, as in corner_audit's rule A'),
  t_sel = LATEST arrival at uspec's abort pin (through the link's latch, the data, the abort LUT),
  t_req = EARLIEST arrival at uspec's short-line pin (through the link's DELAY, the join, udly_s; fast-fall arcs off),
  margin = GLO * t_req - GHI * t_sel  (skew.py's rule-E form; corner_audit's measured-residual guards by default).
SDF: a corner_audit out/soak.sdf (already scaled to the corner).  Pins are found from the SDF: the abort pin is the
uspec input driven by neither delay line.  Prints one row per upstream link C node, then the worst.
"""
import argparse, collections, pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
VERIFY = HERE.parents[2] / "cells" / "verify"

ap = argparse.ArgumentParser()
ap.add_argument("sdf")
ap.add_argument("inst", help="full instance path of the fused unit, e.g. bridge_i.udut.uaddi0")
ap.add_argument("--glo", type=float, default=0.97)
ap.add_argument("--ghi", type=float, default=1.03)
a = ap.parse_args()
sys.path.insert(0, str(VERIFY))
sys.argv = [sys.argv[0], a.sdf]
import skew                     # noqa: E402  (imports tighten with argv = [prog, sdf])
import tighten as T             # noqa: E402

edges, back, stops = T.routed_graph(pathlib.Path(a.sdf))
binc, srcs_of = collections.defaultdict(list), collections.defaultdict(set)
for s, lst in edges.items():
    for d, w in lst:
        binc[d].append((s, w))
        srcs_of[d].add(s)
feed = {(o, ip) for o in stops for ip, _ in binc.get(o, ()) if o in srcs_of[ip]}
side = T.fastfall_side_arcs(edges)
early = {s: [(d, w) for d, w in lst if (s, d) not in side] for s, lst in edges.items()}

U = a.inst + ".uspec"
pins = sorted({d for d in binc if T.pin_split(d)[0] == U and not T.is_output(d)})
if not pins:
    sys.exit("spec_select: no %s in %s" % (U, a.sdf))
def driver(p):
    return {T.pin_split(s)[0] for s, _ in binc[p]}
short = [p for p in pins if any(".udly_s." in i for i in driver(p))]
longp = [p for p in pins if any(".udly." in i for i in driver(p))]
sel = [p for p in pins if p not in short and p not in longp]
if len(short) != 1 or len(sel) != 1:
    sys.exit("spec_select: cannot tell the pins of %s apart: short %s long %s other %s" % (U, short, longp, sel))
short, sel = short[0], sel[0]
print("uspec pins: abort %s (from %s), short %s" % (sel, sorted(driver(sel)), short))

ups = T.upstream_bd_links(T.cell_boundary(edges, back, stops, a.inst))
def at(levels, pin):
    for k, tab in enumerate(levels):
        if pin in tab:
            return tab[pin], k
    return None
worst = None
for link in ups:
    for c in (link + ".ctl.u.u/O6", link + ".ctl.ub/O6"):
        if c not in stops:
            continue
        we = skew.walk(early, stops, binc, feed, c, False)[0]
        wl = skew.walk(edges, stops, binc, feed, c, True)[0]
        r = at(we, short)
        if r is None:
            continue
        s = at(wl[:r[1] + 2], sel)     # the data may cross the link's latch: one storage node more than the request
        if s is None:
            print("  %s: abort pin not reached within %d crossings" % (c, r[1] + 1))
            continue
        m = int(a.glo * r[0] - a.ghi * s[0])
        print("  from %s: short req %d ps (%dx)  abort %d ps (%dx)  margin %+d" % (c, r[0], r[1], s[0], s[1], m))
        if worst is None or m < worst[0]:
            worst = (m, c, r[0], s[0])
if worst is None:
    sys.exit("spec_select: no upstream link reaches both pins")
print("SELECT %s margin %+d ps (req %d, abort %d, from %s, guards %.2f/%.2f)"
      % (a.inst.split(".")[-1], worst[0], worst[2], worst[3], worst[1], a.glo, a.ghi))
