#!/usr/bin/env python3
"""pinbands.py -- a nextpnr-xilinx ROUTED LUT netlist -> an xevents2pin netlist + per-PIN band file.

    python3 -I pinbands.py ROUTED.json --xray-arcs ARCS.tsv --corner slow|fast|indep
            --out NET.json --bands BANDS.json [--db PRJXRAY_DB/zynq7] [--unit-ps 1] [--report R.txt]

WHY (formal/notes/A-events2pin.md).  routed2x.py writes one band per LUT (the min/max over
its pins' IOPATH rows) and puts each pin's site-pin delay inside that pin's routed arc
(xray_delay.py charges the prjxray Inpin to the INTERCONNECT row).  The per-pin model
(Events2Strict.BehP, xevents2pin) wants, for every LUT input pin, ITS OWN arc to the LUT
output.  This script writes, per LUT input:

  arcs[cell/I<l>]     the route alone: the IC row of (driver pin -> cell/A<k>) minus the
                      prjxray site-pin intrinsic of A<k> at the same corner column
                      (IC = sum of intrinsics + one RC term; the Inpin has C = 0, so the
                      subtraction is exact column by column);
  pins[cell/I<l>]     the pin arc: site-pin intrinsic of A<k> + the IOPATH row A<k> -> O
                      (O6 or O5) of that cell;
  sitepins[cell/I<l>] the site-pin intrinsic alone (report only);
  cells[cell]         the atomic LUT band [min lo, max hi] over the used pins (routed2x's).

THE PLACER'S PIN PERMUTATION.  nextpnr may bring a net in on any physical pin A1..A6 and
permute the INIT (patches/README.md, lut-perm-sink).  The routed JSON records, per physical
pin A<k>, the LOGICAL input(s) it carries in X_ORIG_PORT_A<k> (cells/verify/fasm_audit.py
checks that record against the FASM), and its INIT is the LOGICAL INIT.  The netlist written
here is in LOGICAL pin order (I0..I<K-1>, the logical INIT), so xevents2pin recognises the
bd_ce.v layout; logical input l gets the net AND THE DELAYS of the physical pin A<k> that
carries it.  A physical pin carrying two logical inputs gives both the same net and band
(the per-pin model then lets them be read at different instants: more behaviours, sound).
A logical input on no physical pin must not matter to the INIT (checked) and is tied 0.

SITE-PIN DELAYS.  prjxray-db tile_type_<TT>.json site_pins[<L><k>].delay, the 4-tuple
[FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX] (ns) of the site (tilegrid.json gives tile and
site index).  CHECKED against the TSV: for every resolved IC row into a LUT pin the
SLOW_MAX site-pin intrinsic must equal the row's inpin_smax_ps column (xray_delay.py's own
Inpin), else the script stops: that is the check that the physical pin is the one the
route entered (xray_delay.py's sink_wire follows the tile pin, i.e. the permutation).

CORNERS (as routed2x.py): slow [SLOW_MIN, SLOW_MAX], fast [FAST_MIN, FAST_MAX],
indep [FAST_MIN, SLOW_MAX] (the mixed band).

SCOPE.  SLICE_LUTX cells only (the xevents2 domain: C-elements, latches, buffers), IOB input
buffers become free inputs (named by their top-level port), output buffers are readers outside
the netlist, constant nets fold to 0/1.  Any other cell type stops the script.
"""
import argparse
import collections
import json
import math
import re
import sys

COLS = {"indep": (4, 7), "slow": (6, 7), "fast": (4, 5)}
DCOL = {"indep": (0, 3), "slow": (2, 3), "fast": (0, 1)}     # into the prjxray 4-tuple
RE_I = re.compile(r"I(\d+)")
OK_OTHER = {"IOB33_OUTBUF", "PAD", "PSEUDO_GND", "PSEUDO_VCC", "IOB33_INBUF_EN"}


def die(m):
    print("pinbands: " + m, file=sys.stderr)
    sys.exit(1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("routed")
    ap.add_argument("--xray-arcs", required=True)
    ap.add_argument("--corner", default="slow", choices=sorted(COLS))
    ap.add_argument("--out", required=True)
    ap.add_argument("--bands", required=True)
    ap.add_argument("--db", default=None)
    ap.add_argument("--unit-ps", type=int, default=1)
    ap.add_argument("--report")
    ap.add_argument("--atomic-bands", help="also write routed2x-style bands (site pin inside the route, "
                    "one band per LUT) for xevents2 / xevents2strict: the H_ATOMIC_LUT comparison")
    a = ap.parse_args()
    db = a.db or (__import__("os").path.expanduser("~/dev2/lib/fpgatoolchain/openxc7/share/nextpnr/prjxray-db/zynq7"))
    lo_c, hi_c = COLS[a.corner]
    dlo, dhi = DCOL[a.corner]

    ic, io, inpin_smax = {}, collections.defaultdict(dict), {}
    with open(a.xray_arcs) as f:
        assert f.readline().startswith("kind\tsrc\tdst")
        for line in f:
            r = line.rstrip("\n").split("\t")
            if r[0] == "IC":
                ic[(r[1], r[2])] = (int(r[lo_c]), int(r[hi_c]), r[10])
                inpin_smax[(r[1], r[2])] = int(r[12])
            else:
                io[r[2]][r[1].rsplit("/", 1)[1]] = (int(r[lo_c]), int(r[hi_c]))
    tilegrid = json.load(open(db + "/xc7z010/tilegrid.json"))
    site_tile = {}
    for t, v in tilegrid.items():
        ss = sorted(v.get("sites", {}), key=lambda s: int(re.search(r"X(\d+)", s).group(1)))
        for i, s in enumerate(ss):
            site_tile[s] = (v["type"], i)
    ttcache = {}

    def site_pin(site, pin):
        """prjxray 4-tuple (ps) of site pin `pin` of `site`."""
        tt, idx = site_tile[site]
        if tt not in ttcache:
            ttcache[tt] = json.load(open("%s/tile_type_%s.json" % (db, tt)))
        for s in ttcache[tt]["sites"]:
            if s["x_coord"] == idx:
                dl = s["site_pins"][pin]["delay"]
                return [int(round(float(x) * 1000)) for x in dl]
        die("no site %d in %s" % (idx, tt))

    j = json.load(open(a.routed))
    m = j["modules"].get("top") or next(iter(j["modules"].values()))
    cells = m["cells"]
    nname = {}
    for nn, v in m["netnames"].items():
        for i, b in enumerate(v["bits"]):
            if isinstance(b, int) and (b not in nname or not v.get("hide_name", 0)):
                nname[b] = nn if len(v["bits"]) == 1 else "%s[%d]" % (nn, i)
    portbit = {}
    for pn, p in m["ports"].items():
        for i, b in enumerate(p["bits"]):
            portbit[b] = pn if len(p["bits"]) == 1 else "%s[%d]" % (pn, i)
    drv = {}
    for cn, c in cells.items():
        for p, dd in c["port_directions"].items():
            if dd == "output":
                for b in c["connections"].get(p, []):
                    drv[b] = (cn, p)
    const = {}
    free = {}
    for b, (cn, p) in drv.items():
        t = cells[cn]["type"]
        if t == "PSEUDO_GND":
            const[b] = "0"
        elif t == "PSEUDO_VCC":
            const[b] = "1"
        elif t == "IOB33_INBUF_EN":
            free[b] = portbit.get(cells[cn]["connections"]["PAD"][0], nname.get(b, "in%d" % b))
    for cn, c in cells.items():
        if c["type"] not in OK_OTHER and c["type"] != "SLICE_LUTX":
            die("cell %s type %s: outside pinbands.py's scope (LUT netlists only)" % (cn, c["type"]))

    out_cells, b_cells, b_arcs, b_pins, b_site = {}, {}, {}, {}, {}
    used = set()
    rep = []
    checked = 0
    perm = collections.Counter()

    def bit(b):
        if b in const:
            return const[b]
        used.add(b)
        return b

    for cn in sorted(cells):
        c = cells[cn]
        if c["type"] != "SLICE_LUTX":
            continue
        init_s = c["parameters"]["INIT"]
        W = len(init_s)
        K = int(round(math.log2(W)))
        if 1 << K != W:
            die("%s: INIT width %d" % (cn, W))
        init = int(init_s, 2)
        outp = [p for p in ("O6", "O5") if c["connections"].get(p)]
        if len(outp) != 1:
            die("%s: outputs %s" % (cn, outp))
        op = outp[0]
        site, bel = c["attributes"]["NEXTPNR_BEL"].split("/")[:2]
        L = bel[0]
        phys = {}      # logical index -> physical pin number k
        for k in range(1, 7):
            for l in map(int, RE_I.findall(c["attributes"].get("X_ORIG_PORT_A%d" % k, ""))):
                if l in phys:
                    die("%s: logical I%d on two physical pins" % (cn, l))
                phys[l] = k
        conns, arcs, pins, sites = {}, {}, {}, {}
        lohi = []
        for l in range(K):
            if l not in phys:
                # the INIT must not depend on l
                for adr in range(W):
                    if not (adr >> l) & 1 and ((init >> adr) & 1) != ((init >> (adr | 1 << l)) & 1):
                        die("%s: logical I%d on no physical pin but the INIT depends on it" % (cn, l))
                conns["I%d" % l] = ["0"]
                continue
            k = phys[l]
            perm["identity" if k == l + 1 else "permuted"] += 1
            nb = c["connections"]["A%d" % k][0]
            conns["I%d" % l] = [bit(nb)]
            if nb in const:
                continue
            d = drv.get(nb)
            if d is None:
                die("%s/A%d: no driver" % (cn, k))
            key = ("%s/%s" % d, "%s/A%d" % (cn, k))
            if key not in ic:
                die("no IC row %s -> %s" % key)
            lo, hi, flag = ic[key]
            if flag != "ok":
                die("IC row %s -> %s flagged %s (nextpnr's number, no site pin): refuse" % (key + (flag,)))
            sp = site_pin(site, "%s%d" % (L, k))
            if sp[3] != inpin_smax[key]:
                die("%s/A%d: site pin SLOW_MAX %d ps != xray_delay's Inpin %d ps (wrong physical pin?)"
                    % (cn, k, sp[3], inpin_smax[key]))
            checked += 1
            iob = io["%s/%s" % (cn, op)].get("A%d" % k)
            if iob is None:
                die("no IOPATH %s/A%d -> %s" % (cn, k, op))
            s_lo, s_hi = sp[dlo], sp[dhi]
            arcs["I%d" % l] = [lo - s_lo, hi - s_hi]
            pins["I%d" % l] = [s_lo + iob[0], s_hi + iob[1]]
            sites["I%d" % l] = [s_lo, s_hi]
            lohi.append(iob)
            if lo - s_lo < 0:
                die("%s/A%d: negative route after removing the site pin" % (cn, k))
        conns["O"] = [bit(c["connections"][op][0])]
        out_cells[cn] = {"type": "LUT%d" % K, "parameters": {"INIT": init_s},
                         "port_directions": dict({("I%d" % i): "input" for i in range(K)}, O="output"),
                         "connections": conns}
        if lohi:
            b_cells[cn] = [min(x[0] for x in lohi), max(x[1] for x in lohi)]
        for pin, v in arcs.items():
            b_arcs["%s/%s" % (cn, pin)] = v
            b_pins["%s/%s" % (cn, pin)] = pins[pin]
            b_site["%s/%s" % (cn, pin)] = sites[pin]
    ports = {}
    for b, pn in free.items():
        if b in used:
            ports[pn] = {"direction": "input", "bits": [b]}
    netnames = {}
    for b in sorted(used):
        nm = free.get(b) or nname.get(b, "n%d" % b)
        if nm in netnames:
            nm = "%s#%d" % (nm, b)
        netnames[nm] = {"hide_name": 0, "bits": [b]}
    top = {"attributes": {"top": "00000000000000000000000000000001"}, "ports": ports,
           "cells": out_cells, "netnames": netnames}
    json.dump({"creator": "pinbands.py", "modules": {"top": top}}, open(a.out, "w"), indent=1)
    allr = list(b_arcs.values())
    json.dump({"comment": "per-pin bands from %s, corner %s (pinbands.py)" % (a.xray_arcs, a.corner),
               "unit_ps": a.unit_ps, "lut": [45, 124], "route": [0, max(v[1] for v in allr)],
               "cells": b_cells, "arcs": b_arcs, "pins": b_pins, "sitepins": b_site},
              open(a.bands, "w"), indent=1)
    if a.atomic_bands:
        at = {k: [v[0] + b_site[k][0], v[1] + b_site[k][1]] for k, v in b_arcs.items()}
        json.dump({"comment": "ATOMIC bands (site pin in the route) from %s, corner %s (pinbands.py)"
                   % (a.xray_arcs, a.corner), "unit_ps": a.unit_ps, "lut": [45, 124],
                   "route": [0, max(v[1] for v in at.values())], "cells": b_cells, "arcs": at},
                  open(a.atomic_bands, "w"), indent=1)
    rep.append("pinbands: %s corner %s -> %s, %s" % (a.routed, a.corner, a.out, a.bands))
    rep.append("LUTs %d, pin arcs %d (site pin checked against xray_delay's Inpin on %d), "
               "logical->physical pins: %s, free inputs %s"
               % (len(out_cells), len(b_pins), checked, dict(perm), sorted(ports)))
    for k in sorted(b_pins):
        rep.append("  %-40s route %-12s site %-12s pin arc %s" % (k, b_arcs[k], b_site[k], b_pins[k]))
    txt = "\n".join(rep) + "\n"
    if a.report:
        open(a.report, "w").write(txt)
    sys.stdout.write(txt)


if __name__ == "__main__":
    main()
