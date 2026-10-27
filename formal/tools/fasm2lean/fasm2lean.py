#!/usr/bin/env python3
"""FASM (the bits the board runs) -> a physical LUT netlist -> Lean terms.

    python3 formal/tools/fasm2lean/fasm2lean.py FASM XDC --ns NAME [--out F.lean] [--json F.json]

Reads ONLY the FASM and prjxray-db (tilegrid, tile_type_*.json, tileconn).
It does not read nextpnr's routed JSON or SDF, and it does not read yosys:
those are what the bitstream is to be checked against, so they must not be
inputs to the extraction (CLAUDE.md: three of the four worst bugs were in the
bits while netlist, SDF and every simulation were correct).  The XDC is read
only to label IOB sites with port names (package pin -> IOB site via
package_pins.csv); nothing else in the design is taken from it.

What it recovers, per used LUT site (a `*.?LUT.INIT[63:0]` feature):
  * the physical INIT, addressed by the PHYSICAL pins A6..A1 (A1 = bit 0),
    i.e. after the placer's pin permutation and the FASM writer's re-encoding;
  * for each physical pin A1..A6, the net source it is wired to, found by
    walking the ACTIVE pips of the FASM backwards from the pin's tile wire
    through prjxray's wire->node connectivity (tileconn), across CLB-internal
    pips (CLBLM_IMUXn -> CLBLM_M_A1), INT pips (IMUX, singles/doubles/hexes,
    bounces, GFAN ties) and IOI site-routing pips, until it reaches a site
    output pin (SLICE A..D / AMUX..DMUX, IOB I) or a tie (GND_WIRE/VCC_WIRE);
  * every pip on the way, with prjxray-db's buffered / pass-transistor flag,
    its intrinsic delay at the four corners [fast_min fast_max slow_min
    slow_max] (ns) and its drive R / input C, plus the site-pin delays.
Per output port: the same walk from the IOB's O pin.

Checks made while walking (each exits 1 with a message): a node with two
active drivers (a short), a LUT pin with no driver (floating), a source the
tool does not model (FF Q, carry, F7/F8 mux, an OUTMUX other than O6/O5).
Implicit pips (no config bits: prjxray-db ppips 'always'/'default', and the
tile json's pseudo pips such as the ILOGIC/OLOGIC combinational bypass) are
never printed by bit2fasm, so they are inferred: taken only for a node with
no active pip, and only when exactly one candidate's source is itself driven.
That inference is hypothesis H_IMPLICIT (notes/C-11b-fasm.md).

Lean output: one namespace with `luts : List PLut` (index = order of the LUT
sites, sorted), `outs : List (String x Src)`, `ports`, and `pinDelay`
intrinsic-sum intervals in ps.  Semantics in Formal/Net/Fasm/Basic.lean.
"""
import argparse
import csv
import json
import os
import re
import sys
from collections import defaultdict

TC = os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain"))
DB = os.path.join(TC, "openxc7/share/nextpnr/prjxray-db/zynq7")
PART = "xc7z010"
PKG = "xc7z010clg400-1"

RE_VEC = re.compile(r"^(\S+)\[(\d+):(\d+)\]\s*=\s*(\d+)'b([01]+)$")
RE_LUT = re.compile(r"^(\S+)\.(SLICE[LM]_X[01])\.([A-D])LUT\.INIT$")
SLICE_OUT = {"A", "B", "C", "D", "AMUX", "BMUX", "CMUX", "DMUX",
             "AQ", "BQ", "CQ", "DQ", "AMUX", "COUT"}


def die(msg, code=1):
    print("fasm2lean: " + msg, file=sys.stderr)
    sys.exit(code)


def read_fasm(path):
    feats, vecs = set(), {}
    with open(path) as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            m = RE_VEC.match(line)
            if m:
                name, hi, lo, _w, bits = m.groups()
                if int(lo) != 0 or len(bits) != int(hi) + 1:
                    die("cannot read %r" % line, 2)
                vecs[name] = int(bits, 2)
            elif "=" in line:
                name, val = (s.strip() for s in line.split("=", 1))
                if val not in ("1", "1'b1"):
                    die("cannot read %r" % line, 2)
                feats.add(name)
            else:
                feats.add(line)
    return feats, vecs


class Fabric:
    """prjxray-db, loaded lazily per tile type."""

    def __init__(self, db=DB, part=PART):
        self.db = db
        with open(os.path.join(db, part, "tilegrid.json")) as f:
            self.grid = json.load(f)
        self.at = {(t["grid_x"], t["grid_y"]): n for n, t in self.grid.items()}
        with open(os.path.join(db, part, "tileconn.json")) as f:
            tc = json.load(f)
        # (type, wire) -> [(dx, dy, other type, other wire)]
        self.conn = defaultdict(list)
        for e in tc:
            (dx, dy), (t1, t2) = e["grid_deltas"], e["tile_types"]
            for w1, w2 in e["wire_pairs"]:
                self.conn[(t1, w1)].append((dx, dy, t2, w2))
                self.conn[(t2, w2)].append((-dx, -dy, t1, w1))
        self._tt = {}

    def ttype(self, tile):
        return self.grid[tile]["type"]

    def tt(self, ttype):
        if ttype not in self._tt:
            p = os.path.join(self.db, "tile_type_%s.json" % ttype)
            if os.path.exists(p):
                with open(p) as f:
                    j = json.load(f)
            else:
                j = {"pips": {}, "sites": [], "wires": {}}
            # pips by dst wire, and by (dst, src) name
            j["_by_dst"] = defaultdict(list)
            j["_by_name"] = {}
            for k, p in j["pips"].items():
                j["_by_dst"][p["dst_wire"]].append(p)
                j["_by_name"][(p["dst_wire"], p["src_wire"])] = p
            # prjxray-db ppips: pips with NO configuration bits.  'always' and
            # 'default' ones conduct without any FASM feature (bit2fasm never
            # prints them; nextpnr's FASM writer prints some); 'hint' ones
            # (LUT route-throughs) need site configuration and are not taken.
            j["_implicit"] = set()
            pp = os.path.join(self.db, "ppips_%s.db" % ttype.lower())
            if os.path.exists(pp):
                with open(pp) as f:
                    for line in f:
                        w = line.split()
                        if len(w) == 2 and w[1] in ("always", "default"):
                            _t, dst, src = w[0].split(".", 2)
                            j["_implicit"].add((dst, src))
            for p in j["pips"].values():
                if p["is_pseudo"] == "1":
                    j["_implicit"].add((p["dst_wire"], p["src_wire"]))
            # site pin wires
            j["_sitepin"] = {}
            for s in j["sites"]:
                for pin, v in s["site_pins"].items():
                    if v and v.get("wire"):
                        j["_sitepin"][v["wire"]] = (s, pin, v)
            self._tt[ttype] = j
        return self._tt[ttype]

    def node(self, tile, wire):
        """All (tile, wire) electrically one node with (tile, wire)."""
        seen = {(tile, wire)}
        todo = [(tile, wire)]
        while todo:
            t, w = todo.pop()
            g = self.grid[t]
            for dx, dy, t2, w2 in self.conn.get((g["type"], w), ()):
                o = self.at.get((g["grid_x"] + dx, g["grid_y"] + dy))
                if o and self.grid[o]["type"] == t2 and (o, w2) not in seen:
                    seen.add((o, w2))
                    todo.append((o, w2))
        return seen

    def site_name(self, tile, site):
        """tile-type site (relative x_coord/y_coord) -> tilegrid site name."""
        prefix = site["prefix"]
        cands = [s for s in self.grid[tile]["sites"] if s.startswith(prefix + "_")]

        def xy(s):
            m = re.search(r"_X(\d+)Y(\d+)$", s)
            return int(m.group(1)), int(m.group(2))
        cands.sort(key=lambda s: (xy(s)[0], xy(s)[1]))
        xs = sorted({xy(s)[0] for s in cands})
        ys = sorted({xy(s)[1] for s in cands})
        for s in cands:
            if xs.index(xy(s)[0]) == site["x_coord"] and ys.index(xy(s)[1]) == site["y_coord"]:
                return s
        die("cannot place site %s/%s in tile %s" % (prefix, site["name"], tile), 2)


def corners(d):
    """prjxray [fast_min, fast_max, slow_min, slow_max] ns -> ps ints."""
    if not d:
        return [0, 0, 0, 0]
    return [int(round(float(x) * 1000)) for x in d]


class Extract:
    def __init__(self, fab, feats, vecs, port_of_site):
        self.fab, self.feats, self.vecs = fab, feats, vecs
        self.port_of_site = port_of_site
        # active pips: tile -> {(dst, src)}
        self.active = defaultdict(set)
        self.site_feats = []
        for f in feats:
            parts = f.split(".")
            if len(parts) == 3 and parts[0] in fab.grid:
                tile, dst, src = parts
                j = fab.tt(fab.ttype(tile))
                if (dst, src) in j["_by_name"]:
                    self.active[tile].add((dst, src))
                    continue
            self.site_feats.append(f)
        self.used_pips = set()

    def drivers(self, node):
        out = []
        for t, w in node:
            j = self.fab.tt(self.fab.ttype(t))
            for p in j["_by_dst"].get(w, ()):
                if (w, p["src_wire"]) in self.active[t]:
                    out.append((t, p, False))
        return out

    # Pseudo pips that a SITE mux selects: (dst regex, src regex, feature).
    # prjxray fuzzers/035-iob-ilogic/generate.py: IDELMUXE3.P1 = 'direct'
    # (D -> O), P0 = 'idelay' (DDLY -> O).  ILOGIC<k> wires are FASM ILOGIC_Y<k>.
    SITE_MUX = [(r"IOI_ILOGIC(\d)_O$", r"_ILOGIC\d_D$", "ILOGIC_Y{0}.IDELMUXE3.P1"),
                (r"IOI_ILOGIC(\d)_O$", r"_ILOGIC\d_DDLY$", "ILOGIC_Y{0}.IDELMUXE3.P0")]

    def site_mux_ok(self, t, p):
        for rd, rs, feat in self.SITE_MUX:
            m = re.search(rd, p["dst_wire"])
            if m and re.search(rs, p["src_wire"]):
                return "%s.%s" % (t, feat.format(*m.groups())) in self.feats
        return True

    def pseudo_drivers(self, node):
        out = []
        for t, w in node:
            j = self.fab.tt(self.fab.ttype(t))
            for p in j["_by_dst"].get(w, ()):
                if ((w, p["src_wire"]) in j["_implicit"] and (w, p["src_wire"]) not in self.active[t]
                        and self.site_mux_ok(t, p)):
                    out.append((t, p, True))
        return out

    def source_pin(self, node):
        """A site OUTPUT pin on the node, or a tie."""
        for t, w in node:
            if w in ("GND_WIRE", "VCC_WIRE"):
                return ("const", w == "VCC_WIRE")
        for t, w in node:
            j = self.fab.tt(self.fab.ttype(t))
            sp = j["_sitepin"].get(w)
            if not sp:
                continue
            site, pin, v = sp
            if site["type"] in ("SLICEL", "SLICEM") and pin in SLICE_OUT:
                return ("slice", t, site, pin)
            if site["type"].startswith("IOB") and pin == "I":
                return ("iob", t, site, pin)
        return None

    def walk(self, tile, wire, what):
        """Backwards from a sink wire to its source.  Returns (src, pips)."""
        pips = []
        node = self.fab.node(tile, wire)
        for _ in range(200):
            src = self.source_pin(node)
            if src:
                return src, pips
            d = self.drivers(node)
            if len(d) > 1:
                die("%s: node %s has %d active drivers (a short): %s" % (
                    what, sorted(node)[0], len(d),
                    ["%s.%s.%s" % (t, p["dst_wire"], p["src_wire"]) for t, p, _ in d]))
            if not d:
                cand = [(t, p, ps) for t, p, ps in self.pseudo_drivers(node)
                        if self.is_driven(self.fab.node(t, p["src_wire"]))]
                if len(cand) != 1:
                    die("%s: node %s is floating (no active pip; %d pseudo candidates)"
                        % (what, sorted(node)[0], len(cand)))
                d = cand
            t, p, ps = d[0]
            pips.append((t, p, ps))
            self.used_pips.add((t, p["dst_wire"], p["src_wire"]))
            node = self.fab.node(t, p["src_wire"])
        die("%s: route longer than 200 pips" % what, 2)

    def is_driven(self, node, depth=8):
        """Has a source: a site output, an active pip, or (up to `depth`
        implicit pips back) an implicit pip from a driven node."""
        if self.source_pin(node) or self.drivers(node):
            return True
        if depth == 0:
            return False
        return any(self.is_driven(self.fab.node(t, p["src_wire"]), depth - 1)
                   for t, p, _ in self.pseudo_drivers(node))


def lut_output(fab, ex, src, lut_index):
    """A SLICE output pin -> ('lut', index, 'O6'|'O5')."""
    _, tile, site, pin = src
    pre = "%s.%s_X%d" % (tile, site["type"], site["x_coord"])
    if pin in ("A", "B", "C", "D"):
        return lut_index.get((pre, pin), None), "O6"
    if pin.endswith("MUX"):
        L = pin[0]
        for o in ("O6", "O5"):
            if "%s.%sOUTMUX.%s" % (pre, L, o) in ex.feats:
                return lut_index.get((pre, L), None), o
        die("%s.%s: OUTMUX source not modelled (only O6/O5)" % (pre, pin))
    die("%s.%s: source not modelled (FF / carry)" % (pre, pin))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("fasm")
    ap.add_argument("xdc")
    ap.add_argument("--ns", required=True, help="Lean namespace suffix")
    ap.add_argument("--out", help="write Lean here")
    ap.add_argument("--json", help="write the extracted netlist (with route data) here")
    ap.add_argument("--db", default=DB)
    a = ap.parse_args()

    feats, vecs = read_fasm(a.fasm)
    fab = Fabric(a.db)

    # ports: xdc PACKAGE_PIN -> package_pins.csv site
    pin_site = {}
    with open(os.path.join(a.db, PKG, "package_pins.csv")) as f:
        for r in csv.DictReader(f):
            pin_site[r["pin"]] = r["site"]
    port_of_site = {}
    with open(a.xdc) as f:
        for line in f:
            m = re.match(r"\s*set_property\s+PACKAGE_PIN\s+(\S+)\s+\[get_ports\s+\{?(\S+?)\}?\]", line)
            if m:
                port_of_site[pin_site[m.group(1)]] = m.group(2)

    ex = Extract(fab, feats, vecs, port_of_site)

    # used LUT sites
    lut_sites = []
    for name, val in vecs.items():
        m = RE_LUT.match(name)
        if m:
            lut_sites.append((m.group(1), m.group(2), m.group(3), val))
    lut_sites.sort()
    lut_index = {("%s.%s" % (t, s), L): i for i, (t, s, L, _) in enumerate(lut_sites)}
    # A LUT site whose INIT is all zero writes no INIT feature: it is invisible
    # here.  Such a LUT computes constant 0 on O6, and anything reading it
    # would show up as a SLICE source with no LUT -- caught below.

    def src_term(src, what):
        kind = src[0]
        if kind == "const":
            return {"k": "const", "v": src[1]}
        if kind == "iob":
            _, tile, site, _pin = src
            sname = fab.site_name(tile, site)
            port = port_of_site.get(sname)
            if port is None:
                die("%s: driven by IOB %s, which the XDC does not name" % (what, sname))
            return {"k": "port", "name": port, "site": sname}
        i, o = lut_output(fab, ex, src, lut_index)
        if i is None:
            die("%s: driven by a LUT with no INIT feature (all-zero LUT?)" % what)
        return {"k": "lut", "i": i, "out": o}

    def pipdata(t, p, pseudo):
        s2d = p.get("src_to_dst") or {}
        return {"tile": t, "dst": p["dst_wire"], "src": p["src_wire"],
                "pass": bool(p["is_pass_transistor"]), "pseudo": pseudo,
                "delay_ps": corners(s2d.get("delay")),
                "res": s2d.get("res"), "in_cap": s2d.get("in_cap")}

    luts = []
    for i, (tile, sl, L, init) in enumerate(lut_sites):
        j = fab.tt(fab.ttype(tile))
        x = int(sl[-1])
        site = [s for s in j["sites"] if s["type"].startswith("SLICE") and s["x_coord"] == x][0]
        pins = []
        for k in range(1, 7):
            v = site["site_pins"]["%s%d" % (L, k)]
            what = "%s.%s.%sLUT pin %s%d" % (tile, sl, L, L, k)
            src, path = ex.walk(tile, v["wire"], what)
            pins.append({"pin": "%s%d" % (L, k), "src": src_term(src, what),
                         "sitepin_delay_ps": corners(v.get("delay")),
                         "pips": [pipdata(*q) for q in reversed(path)]})
        luts.append({"tile": tile, "slice": sl, "lut": L,
                     "site": fab.site_name(tile, site), "init": init, "pins": pins})

    # outputs: every IOB whose site the XDC names and that has an output buffer
    outs = []
    for sname, port in sorted(port_of_site.items(), key=lambda kv: kv[1]):
        tile = [t for t, g in fab.grid.items() if sname in g.get("sites", {})][0]
        j = fab.tt(fab.ttype(tile))
        site = [s for s in j["sites"] if fab.site_name(tile, s) == sname][0]
        # prjxray's own rule (fuzzers/030-iob/check_results.py): IOB_Y<site Y % 2>
        fy = "%s.IOB_Y%d" % (tile, int(re.search(r"Y(\d+)$", sname).group(1)) % 2)
        has_drive = any(f.startswith(fy + ".") and ".DRIVE." in f for f in feats)
        has_in = any(f.startswith(fy + ".") and f.endswith(".IN") for f in feats)
        if not has_drive:
            if not has_in:
                die("port %s (%s): no IN and no DRIVE feature at %s" % (port, sname, fy))
            continue
        what = "port %s" % port
        src, path = ex.walk(tile, site["site_pins"]["O"]["wire"], what)
        outs.append({"port": port, "site": sname, "src": src_term(src, what),
                     "pips": [pipdata(*q) for q in reversed(path)]})

    unused = [(t, d, s) for t in ex.active for d, s in ex.active[t] if (t, d, s) not in ex.used_pips]
    ports_in = sorted({p["src"]["name"] for l in luts for p in l["pins"] if p["src"]["k"] == "port"})

    res = {"fasm": os.path.abspath(a.fasm), "luts": luts, "outs": outs,
           "inputs": ports_in, "unused_pips": sorted(unused),
           "site_features": sorted(ex.site_feats)}
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=1)
    lean = emit_lean(res, a.ns)
    if a.out:
        with open(a.out, "w") as f:
            f.write(lean)
    else:
        sys.stdout.write(lean)
    print("fasm2lean: %d LUTs, %d outputs, inputs %s, %d active pips (%d not on any "
          "traced path)" % (len(luts), len(outs), ports_in,
                            sum(len(v) for v in ex.active.values()), len(unused)),
          file=sys.stderr)
    for u in unused:
        print("  untraced pip %s.%s.%s" % u, file=sys.stderr)


def emit_lean(res, ns):
    inputs = res["inputs"]

    def src(s):
        if s["k"] == "const":
            return "(.const %s)" % ("true" if s["v"] else "false")
        if s["k"] == "port":
            return "(.port %d)" % inputs.index(s["name"])
        return "(.lut %d .%s)" % (s["i"], s["out"].lower())

    def ivl(pins_pips, sitepin):
        lo = sum(p["delay_ps"][0] for p in pins_pips) + sitepin[0]
        hi = sum(p["delay_ps"][3] for p in pins_pips) + sitepin[3]
        return lo, hi

    L = []
    L.append("import Formal.Net.Fasm.Basic")
    L.append("")
    L.append("/-! Generated by formal/tools/fasm2lean/fasm2lean.py from")
    L.append("    %s" % os.path.relpath(res["fasm"], os.path.join(os.path.dirname(__file__), "../../..")))
    L.append("    Do not edit; regenerate.  Inputs (port index order): %s." % ", ".join(inputs))
    L.append("    Physical pins are A1..A6 (A1 = INIT address bit 0). -/")
    L.append("")
    L.append("namespace Formal.Net.Fasm.%s" % ns)
    L.append("open Formal.Net.Fasm")
    L.append("")
    L.append("/-- Input ports, in `Src.port` index order. -/")
    L.append("def ports : List String := [%s]" % ", ".join('"%s"' % p for p in inputs))
    L.append("")
    for i, l in enumerate(res["luts"]):
        L.append("/-- LUT %d: %s (%s.%s.%sLUT).  Pins A1..A6:" % (i, l["site"], l["tile"], l["slice"], l["lut"]))
        for p in l["pins"]:
            chain = " <- ".join("%s%s" % (q["src"], "(pt)" if q["pass"] else "") for q in p["pips"]) or "(direct)"
            L.append("    %s <- %s : %s" % (p["pin"], src(p["src"]), chain))
        L.append("-/")
        L.append("def lut%d : PLut :=" % i)
        L.append("  ⟨\"%s\", 0x%016X, [%s]⟩" % (l["site"], l["init"], ", ".join(src(p["src"]) for p in l["pins"])))
        L.append("")
    L.append("def net : PNet :=")
    L.append("  ⟨[%s], [%s]⟩" % (", ".join("lut%d" % i for i in range(len(res["luts"]))),
                              ", ".join('("%s", %s)' % (o["port"], src(o["src"])) for o in res["outs"])))
    L.append("")
    L.append("/-- Per LUT pin, the sum of prjxray-db intrinsic delays on its route plus")
    L.append("    the site-pin delay: (fast_min, slow_max) in ps.  NOT an Elmore delay:")
    L.append("    the RC term (wire R/C, pip drive R, fanout) is not included. -/")
    L.append("def pinIntrinsic : List (List (Nat × Nat)) := [")
    rows = []
    for l in res["luts"]:
        rows.append("  [%s]" % ", ".join("(%d, %d)" % ivl(p["pips"], p["sitepin_delay_ps"]) for p in l["pins"]))
    L.append(",\n".join(rows))
    L.append("]")
    L.append("")
    L.append("/-- Number of pass-transistor pips on each LUT pin's route. -/")
    L.append("def pinPassPips : List (List Nat) := [")
    L.append(",\n".join("  [%s]" % ", ".join(str(sum(q["pass"] for q in p["pips"])) for p in l["pins"])
                        for l in res["luts"]))
    L.append("]")
    L.append("")
    L.append("end Formal.Net.Fasm.%s" % ns)
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    main()
