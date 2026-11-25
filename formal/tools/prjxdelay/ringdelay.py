#!/usr/bin/env python3
"""Ring-oscillator periods from the full prjxray model, next to the SDF's.

    python3 formal/tools/prjxdelay/ringdelay.py BUILD_DIR TOP [--json OUT]

BUILD_DIR is one route made by route.sh (TOP.fasm, TOP_routed.json, TOP.sdf).
TOP is ro_many_top (128 rings, grp[g].ro[b].) or ro_top (5 rings, ro[i].).

For every ring it computes the loop delay two ways:

  SDF   exactly what the repo used for its predictions: the walk of
        cells/hw/ro_many_measure.py / ro_measure.py ring_loop_ps over
        cells/verify/tighten.py parse_sdf (both imported, read-only).
        Period = 2 x loop (one rise and one fall traversal).

  PRJX  per stage: the LUT arc of prjxray-db timings/slicel|slicem.sdf for the
        PHYSICAL input pin and output (O6/O5), plus the routed net from the
        predecessor's site output pin to that physical pin, built as an RC tree
        out of prjxray/prjxray/timing.py's own classes (Outpin, Wire, Buffer,
        PassTransistor, Inpin; PythonMathModel) over the pips that are ON in
        the FASM (explicit features + prjxray ppips 'always'/'default' when no
        explicit pip drives the node).  The whole net is in the tree (every
        branch, every site pin on every node), so fanout loading is included.
        Per sink: sum of intrinsic delays (Outpin, every pip, the site input
        pin) at each of fast_min, fast_max, slow_min, slow_max, plus the sum of
        the Elmore terms (R*C, corner-independent in the db).

The physical pin per stage is read from the routed JSON (the cell's port
names are physical pins after nextpnr's permutation) and CROSS-CHECKED by
walking the FASM's active pips backwards from that pin with fasm2lean's
Extract.walk: the walk must arrive at the predecessor's site output pin.
A mismatch exits 1.

No rise/fall split exists in prjxray-db (pips, site pins), and the LUT arcs'
two triples are fast and slow, so a period is 2 x loop at every corner.
"""
import argparse
import json
import math
import os
import pathlib
import re
import statistics
import sys
from collections import defaultdict

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parent.parent.parent
TC = os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain"))
sys.path.insert(0, str(HERE.parent / "fasm2lean"))
sys.path.insert(0, os.path.join(TC, "openxc7-src/prjxray"))
sys.path.insert(0, str(REPO / "cells/verify"))
sys.path.insert(0, str(REPO / "cells/hw"))

import fasm2lean as F                      # noqa: E402
from prjxray import timing as T            # noqa: E402
import tighten                             # noqa: E402



class PythonMath:
    """prjxray/math_models.py's PythonMathModel, verbatim.  Upstream declares
    it with `def PythonMathModel(object):` (a function, not a class), so it
    cannot be instantiated; this is the class it was meant to be."""
    def sum(self, elems): return sum(elems)                # noqa: E704
    def divide(self, a, b): return a / b                   # noqa: E704
    def plus(self, a, b): return a + b                     # noqa: E704
    def multiply(self, a, b): return a * b                 # noqa: E704


M = PythonMath()
CORNERS = ["fast_min", "fast_max", "slow_min", "slow_max"]
SITE_LUT_SDF_DELAY = 25   # ps: what nextpnr charges a site-entry / LUT-perm pip


def corners_obj(d):
    if not d:
        d = [0, 0, 0, 0]
    return T.fast_slow_tuple_to_corners(d)


def pick(delays, k):
    """IntristicDelay dict -> ns at corner k."""
    if delays is None:
        return 0.0
    c = delays[T.PvtCorner.FAST if k < 2 else T.PvtCorner.SLOW]
    return c.min if k % 2 == 0 else c.max


# ----------------------------------------------------------- LUT cell arcs

def lut_arcs(db):
    """(slice type, 'O6'|'O5', 'A1'..'A6') -> [fast_min, fast_max, slow_min,
    slow_max] ns, max/min over every instance variant in timings/slice?.sdf."""
    out = {}
    for st in ("slicel", "slicem"):
        txt = open(os.path.join(db, "timings", st + ".sdf")).read()
        inst = None
        for line in txt.splitlines():
            m = re.search(r"\(INSTANCE\s+(\S+)\)", line)
            if m:
                inst = m.group(1)
                continue
            m = re.search(r"\(IOPATH\s+(A[1-6])\s+(O[56])\s+\(([\d.]*)::([\d.]*)\)\(([\d.]*)::([\d.]*)\)\)", line)
            if m and inst and re.search(r"/[A-D]?[56]LUT$", inst):
                pin, o = m.group(1), m.group(2)
                v = [float(x) for x in m.groups()[2:]]
                key = (st, o, pin)
                if key in out:
                    old = out[key]
                    v = [min(old[0], v[0]), max(old[1], v[1]), min(old[2], v[2]), max(old[3], v[3])]
                out[key] = v
    return out


# ----------------------------------------------------------- RC tree

class Net:
    """Forward RC tree from one site output pin over the ON pips."""

    def __init__(self, fab, ex, tile, wire, site_pin_info):
        self.fab, self.ex = fab, ex
        self.inpins = {}          # (tile, wire) -> Inpin
        self.n_implicit = 0
        self.seen = set()
        out = T.Outpin(resistance=float(site_pin_info.get("res") or 0) / 1e3,
                       delays=corners_obj(site_pin_info.get("delay")))
        out.set_sink_wire(self.build(self.fab.node(tile, wire)))
        out.propigate_delays(M)
        self.root = out

    def by_src(self, ttype):
        j = self.fab.tt(ttype)
        if "_by_src" not in j:
            j["_by_src"] = defaultdict(list)
            for p in j["pips"].values():
                j["_by_src"][p["src_wire"]].append(p)
        return j

    def build(self, node):
        key = frozenset(node)
        assert key not in self.seen, "routing loop"
        self.seen.add(key)
        rcs = []
        for t, w in node:
            rc = self.fab.tt(self.fab.ttype(t))["wires"].get(w)
            if rc:
                rcs.append(T.RcElement(float(rc["res"]) / 1e3, float(rc["cap"]) / 1e3))
        wire = T.Wire(rcs, M)
        for t, w in sorted(node):
            j = self.by_src(self.fab.ttype(t))
            sp = j["_sitepin"].get(w)
            if sp and "cap" in sp[2]:
                ip = T.Inpin(capacitance=float(sp[2]["cap"]) / 1e3,
                             delays=corners_obj(sp[2].get("delay")), name=(t, w))
                wire.add_child(ip)
                self.inpins[(t, w)] = ip
            for p in j["_by_src"].get(w, ()):
                d = p["dst_wire"]
                on = (d, w) in self.ex.active[t]
                if not on and (d, w) in j["_implicit"] and p["is_pseudo"] != "1":
                    dnode = self.fab.node(t, d)
                    if not self.ex.drivers(dnode):
                        on = True
                        self.n_implicit += 1
                if not on:
                    continue
                s2d = p.get("src_to_dst") or {}
                dl = corners_obj(s2d.get("delay"))
                res = float(s2d.get("res") or 0) / 1e3
                if p["is_pass_transistor"]:
                    sw = T.PassTransistor(drive_resistance=res, delays=dl)
                else:
                    sw = T.Buffer(internal_capacitance=float(s2d.get("in_cap") or 0) / 1e3,
                                  drive_resistance=res, delays=dl)
                sw.set_sink_wire(self.build(self.fab.node(t, d)))
                wire.add_child(sw)
        return wire

    def sink(self, tile, wire):
        """[4 corners] ps (intrinsic + rc), intrinsic-only [4], rc ps,
        site-pin intrinsic [4] ps, n pips."""
        ip = self.inpins.get((tile, wire))
        if ip is None:
            return None
        els = ip.get_delays()
        rc = sum(e.get_rc_delay() or 0.0 for e in els) * 1e3
        intr = [sum(pick(e.get_intrinsic_delays(), k) for e in els) * 1e3 for k in range(4)]
        sitep = [pick(ip.get_intrinsic_delays(), k) * 1e3 for k in range(4)]
        npips = sum(isinstance(e, (T.Buffer, T.PassTransistor)) for e in els)
        return [x + rc for x in intr], intr, rc, sitep, npips


# ----------------------------------------------------------- the design

def ring_cells(cells, top):
    """{ring id: [cell names]} for ring LUTs."""
    rings = defaultdict(list)
    pat = re.compile(r"^(grp\[(\d+)\]\.ro\[(\d+)\])\." if top == "ro_many_top" else r"^(ro\[(\d+)\])\.")
    for name, c in cells.items():
        m = pat.match(name)
        if m and c["type"] == "SLICE_LUTX":
            rid = (int(m.group(2)), int(m.group(3))) if top == "ro_many_top" else int(m.group(2))
            rings[rid].append(name)
    return rings


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("build")
    ap.add_argument("top")
    ap.add_argument("--json")
    a = ap.parse_args()
    bd = pathlib.Path(a.build)
    top = a.top
    fasm, routed, sdf = bd / f"{top}.fasm", bd / f"{top}_routed.json", bd / f"{top}.sdf"

    # ---- the repo's SDF prediction, by the repo's own code
    edges, _ct, _a, _b = tighten.parse_sdf(sdf)
    if top == "ro_many_top":
        import ro_many_measure as RM
        sdf_loop = lambda rid: RM.ring_loop_ps(edges, rid[0], rid[1])   # noqa: E731
        ring_len = lambda rid: RM.ring_len(*rid)                         # noqa: E731
    else:
        import ro_measure as RO
        sdf_loop = lambda rid: RO.ring_loop_ps(edges, _ct, rid)         # noqa: E731
        ring_len = lambda rid: [7, 15, 31, 63, 127][rid]                 # noqa: E731

    feats, vecs = F.read_fasm(str(fasm))
    fab = F.Fabric(F.DB)
    ex = F.Extract(fab, feats, vecs, {})
    arcs = lut_arcs(F.DB)

    # site name -> (tile, tile-type site dict)
    site_at = {}
    for tile, g in fab.grid.items():
        if not g["type"].startswith("CLB"):
            continue
        for s in fab.tt(g["type"])["sites"]:
            site_at[fab.site_name(tile, s)] = (tile, s)

    j = json.load(open(routed))
    mod = list(j["modules"].values())[0]
    cells = mod["cells"]
    rings = ring_cells(cells, top)

    def bel(c):
        site, b = cells[c]["attributes"]["NEXTPNR_BEL"].split("/")
        return site, b[0], b[1:]          # SLICE_X.., 'A', '6LUT'

    def out_pins(c):
        """site output pins that can carry cell c's output: the direct pin for
        an O6 (A..D), and ?MUX when the FASM sets ?OUTMUX to this LUT's output."""
        site, L, kind = bel(c)
        tile, s = site_at[site]
        pre = "%s.%s_X%d" % (tile, s["type"], s["x_coord"])
        o = "O6" if kind == "6LUT" else "O5"
        pins = [L] if o == "O6" else []
        if "%s.%sOUTMUX.%s" % (pre, L, o) in feats:
            pins.append(L + "MUX")
        return tile, s, pins

    nets = {}

    # bit -> ROUTING string of the net, for the pre-patch SDF emulation
    routing_of = {}
    for nn, v in mod["netnames"].items():
        rt = v["attributes"].get("ROUTING")
        if rt and len(v["bits"]) == 1:
            routing_of[v["bits"][0]] = rt

    def tile_xy(site):
        g = fab.grid[site_at[site][0]]
        return g["grid_x"], g["grid_y"]

    def prepatch_ic(c, pin, pc, routed_ic):
        """What the SDF said before patches/nextpnr-xilinx-lut-perm-sink.patch
        (2026-09-20): a sink reached through a NON-identity LUT permutation pip
        (tile pin A<x> -> site wire A<y>, x != y) got predictDelay(), the
        placer estimate (patches/README.md): same site and LUT letter 0 ps,
        same tile 150 ps, else 450 + 90|dy| + 45|dx| ps (tile grid).  Returns
        (delay, permuted)."""
        site, L, _k = bel(c)
        rt = routing_of.get(cells[c]["connections"][pin][0], "")
        m = re.search(r"CLB\w+_%s(\d)->SITEWIRE/%s/%s(\d)" % (L, re.escape(site), L), rt)
        if not m:
            raise SystemExit(f"{c}/{pin}: no LUT permutation pip in the net's ROUTING")
        if m.group(1) == m.group(2):
            return routed_ic, False
        psite, PL, _pk = bel(pc)
        if psite == site and PL == L:
            return 0, True
        (x0, y0), (x1, y1) = tile_xy(psite), tile_xy(site)
        if (x0, y0) == (x1, y1):
            return 150, True
        return 450 + 90 * abs(y1 - y0) + 45 * abs(x1 - x0), True

    def net_of(tile, s, pin):
        k = (tile, s["type"], s["x_coord"], pin)
        if k not in nets:
            nets[k] = Net(fab, ex, tile, s["site_pins"][pin]["wire"], s["site_pins"][pin])
        return nets[k]

    results = []
    bad = 0
    for rid in sorted(rings):
        names = rings[rid]
        bits_out = {}
        for c in names:
            o = [k for k in cells[c]["connections"] if k in ("O6", "O5")]
            bits_out[cells[c]["connections"][o[0]][0]] = c
        total = [0.0] * 4
        comp = defaultdict(float)     # slow_max components
        stages = []
        old_loop = 0
        n_perm = 0
        for c in names:
            site, L, kind = bel(c)
            tile, s = site_at[site]
            preds = [(p, bits_out[b[0]]) for p, b in cells[c]["connections"].items()
                     if re.match(r"^A[1-6]$", p) and b and b[0] in bits_out]
            if len(preds) != 1:
                print(f"{rid} {c}: {len(preds)} in-ring inputs", file=sys.stderr)
                bad += 1
                break
            pin, pc = preds[0]
            # cross-check the physical pin against the bits
            ptile, psite, ppins = out_pins(pc)
            pinwire = s["site_pins"][L + pin[1]]["wire"]
            try:
                src, _p = ex.walk(tile, pinwire, f"{c}/{pin}")
            except SystemExit:
                src = None
            if not (src and src[0] == "slice" and src[1] == ptile and src[3] in ppins
                    and src[2]["type"] == psite["type"] and src[2]["x_coord"] == psite["x_coord"]):
                print(f"{rid} {c}/{pin}: FASM walk reaches {src and src[:2]} {src and src[3:]}, "
                      f"routed JSON says {pc} ({ptile} {ppins})", file=sys.stderr)
                sys.exit(1)
            ppin = src[3]
            n = net_of(ptile, psite, ppin)
            r = n.sink(tile, pinwire)
            if r is None:
                print(f"{rid} {c}/{pin}: sink not in the forward tree", file=sys.stderr)
                sys.exit(1)
            dly, intr, rc, sitep, npips = r
            o = "O6" if kind == "6LUT" else "O5"
            arc = [x * 1e3 for x in arcs[(s["type"].lower(), o, pin)]]
            for k in range(4):
                total[k] += dly[k] + arc[k]
            comp["lut_arc"] += arc[3]
            comp["site_pin"] += sitep[3]
            comp["pips_and_outpin"] += intr[3] - sitep[3]
            comp["rc"] += rc
            comp["npips"] += npips
            ic = [w for k2 in ("O6", "O5") for d2, w in edges.get(f"{pc}/{k2}", ()) if d2 == f"{c}/{pin}"]
            la = [w for d2, w in edges.get(f"{c}/{pin}", ()) if d2.startswith(c + "/O")]
            if len(ic) != 1 or len(la) != 1:
                raise SystemExit(f"{c}/{pin}: SDF arcs {ic} {la}")
            oic, perm = prepatch_ic(c, pin, pc, ic[0])
            old_loop += oic + la[0]
            n_perm += perm
            stages.append({"sdf_ic": ic[0], "sdf_lut": la[0], "prepatch_ic": oic, "permuted": perm,
                           "cell": c, "bel": f"{site}/{L}{kind}", "pin": pin, "pred": pc,
                           "net_ps": [round(x, 1) for x in dly], "rc_ps": round(rc, 1),
                           "sitepin_ps": [round(x, 1) for x in sitep], "lut_ps": arc, "npips": npips})
        else:
            loop, err = sdf_loop(rid)
            if loop is None:
                print(f"{rid}: SDF walk: {err}", file=sys.stderr)
                bad += 1
                continue
            if sum(st["sdf_ic"] + st["sdf_lut"] for st in stages) != loop:
                raise SystemExit(f"{rid}: per-stage SDF arcs do not sum to the repo's loop {loop}")
            pins = [st["pin"] for st in stages]
            results.append({"ring": rid, "links": ring_len(rid), "n_luts": len(names),
                            "sdf_period_ps": 2 * loop,
                            "sdf_prepatch_period_ps": 2 * old_loop, "n_permuted": n_perm,
                            "prjx_period_ps": [round(2 * x, 1) for x in total],
                            "slowmax_components_ps": {k: round(2 * v, 1) for k, v in comp.items()},
                            "pins": pins, "stages": stages})
    if bad:
        print(f"{bad} rings not walked", file=sys.stderr)
        sys.exit(1)

    impl = sum(n.n_implicit for n in nets.values())
    print(f"# {bd.name}: {len(results)} rings, {len(nets)} nets, {impl} implicit pips taken")
    print("ring          links  SDF_ps   fmin    fmax    smin    smax  smax/SDF  rc_ps  sitepin_ps  pins")
    for r in results:
        p = r["prjx_period_ps"]
        cp = r["slowmax_components_ps"]
        print(f"{str(r['ring']):12s} {r['links']:5d} {r['sdf_period_ps']:7d} " +
              " ".join(f"{x:7.0f}" for x in p) +
              f"  {p[3] / r['sdf_period_ps']:7.3f} {cp['rc']:6.0f} {cp['site_pin']:8.0f}   " +
              "".join(x[1] for x in r["pins"]))
    if a.json:
        json.dump({"build": str(bd), "rings": results}, open(a.json, "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
