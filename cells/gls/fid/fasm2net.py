#!/usr/bin/env python3
"""
fasm2net.py -- the netlist the BOARD runs, rebuilt from its configuration bits.

    fasm2net.py --bit  gcd_hw.bit  --out DIR [--names gcd_hw_routed.json --sdf gcd_hw.sdf]
    fasm2net.py --fasm gcd_hw.fasm --out DIR [...]

Why this exists.  Three of the four worst bugs in this project were in the
bitstream while the routed JSON, the SDF and every simulation of them were
correct (patches/README.md: lut-pinmap, dsp-constpins, dsp-areg).  cells/gls/
simulates nextpnr's routed JSON, i.e. what the tool MEANT to build.  This
script reads what it actually WROTE -- the FASM, or better the .bit decoded back
to FASM by prjxray's bit2fasm -- and rebuilds the design from prjxray-db alone:

  * routing, pip by pip.  Every active pip (a FASM feature `TILE.DST.SRC`),
    every always-on pseudo pip (`ppips_*.db` "always", which carry no bits),
    every tile-to-tile wire join (`tileconn.json`), and the "default" pseudo
    pip (an IMUX/BYP_ALT/FAN_ALT input with no pip set reads VCC).  Each sink
    pin is traced UPSTREAM through these to the one thing that drives it.  Two
    active drivers on one node, a node nothing drives, or a route that ends on
    a site output nothing in the decoded site produces, are all errors.
  * sites, from their configuration bits: SLICEL/SLICEM (LUT6/LUT5 INIT,
    F7/F8, CARRY4 with PRECYINIT and CY0, FF/5FF with ZINI/ZRST/FFSYNC/
    CEUSEDMUX/SRUSEDMUX/CLKINV, OUTMUX/FFMUX), BUFGCTRL, BSCAN, OLOGIC
    D1->OQ, IOB33 output.  Anything the board would run that is not modelled is
    REFUSED (LATCH, CLKINV, async SR, LUTRAM/SRL, DSP, BRAM...), and every
    configured feature this script did not consume is listed in report.txt.
  * which bels exist is decided by the bits, not by the netlist: a LUT exists
    because something the board configured consumes its output.

Output (DIR):
  fasm_routed.json  nextpnr-shaped routed JSON (cells named by BEL), so
                    cells/gls/gen.py turns it into netlist.v unchanged
  fasm.sdf          --sdf re-keyed onto those cells (see README.md: naming)
  routes.tsv        one row per sink: driver, sink, the pip path (prjxray names)
  report.txt        counts, every refusal / unconsumed feature / anomaly

The site models follow prjxray-db's segbits names and were cross-read against
f4pga-xc-fasm2bels (fasm2bels/models/clb_models.py, Apache-2.0); no code is
copied from it.  Delay is NOT this script's business: it only names things so
an SDF (nextpnr's now, workstream F1's later) can be put on them.
"""
import argparse, collections, json, os, re, subprocess, sys, tempfile

TC = os.environ.get("TC", "/root/dev2/lib/fpgatoolchain")
PRJXRAY = os.environ.get("PRJXRAY_SRC", os.path.join(TC, "openxc7-src/prjxray"))
# The db the BUILD used for fasm2frames (build_hw.sh PRJXRAY_DB), so the bits
# are decoded with the same segbits they were encoded with.
DB_ROOT = os.environ.get("PRJXRAY_DB", os.path.join(TC, "openxc7/share/nextpnr/prjxray-db/zynq7"))
PART = os.environ.get("PART", "xc7z010clg400-1")
sys.path.insert(0, PRJXRAY)
from prjxray.db import Database  # noqa: E402

CONST_WIRES = {"VCC_WIRE": 1, "GND_WIRE": 0}
LUTS = "ABCD"


# =============================================================== the fabric

class Fabric:
    """prjxray-db for one part: tile grid, tile-to-tile wire joins (nodes),
    per-tile-type pips, pseudo pips and sites.  Nodes are built lazily, only
    for wires a route actually touches."""

    def __init__(self, db_root, part):
        self.db = Database(db_root, part)
        self.db._read_tilegrid()
        self.db._read_tileconn()
        self.grid = self.db.grid()
        tg = self.db.tilegrid
        self.ttype = {t: i["type"] for t, i in tg.items()}
        self.loc = {t: (i["grid_x"], i["grid_y"]) for t, i in tg.items()}
        self.at = {v: k for k, v in self.loc.items()}
        self.conn = collections.defaultdict(list)
        for rule in self.db.tileconn:
            (dx, dy), (t0, t1) = rule["grid_deltas"], rule["tile_types"]
            for w0, w1 in rule["wire_pairs"]:
                self.conn[(t0, w0)].append((dx, dy, t1, w1))
                self.conn[(t1, w1)].append((-dx, -dy, t0, w0))
        self._tt = {}
        self.w2n = {}
        self.nodes = []          # node id -> [(tile, wire), ...]
        nw = json.load(open(os.path.join(db_root, self.db.fabric, "node_wires.json")))
        self.specific = set(nw["specific_node_wires"])
        self.pattern = {k: set(v) for k, v in nw["node_pattern_wires"].items()}

    def tt(self, tile_type):
        """pips by (dst, src), always/default ppips by dst, sites."""
        if tile_type not in self._tt:
            j = json.load(open(os.path.join(DB_ROOT, "tile_type_%s.json" % tile_type)))
            pips = {(p["dst_wire"], p["src_wire"]): p for p in j["pips"].values()}
            always, default, hint = (collections.defaultdict(list) for _ in range(3))
            fn = os.path.join(DB_ROOT, "ppips_%s.db" % tile_type.lower())
            if os.path.exists(fn):
                for line in open(fn):
                    name, kind = line.split()
                    _, dst, src = name.split(".", 2)
                    {"always": always, "default": default, "hint": hint}[kind][dst].append(src)
            self._tt[tile_type] = dict(pips=pips, always=always, default=default,
                                       hint=hint, sites=j["sites"])
        return self._tt[tile_type]

    def node(self, tile, wire):
        k = (tile, wire)
        n = self.w2n.get(k)
        if n is not None:
            return n
        members, stack, seen = [k], [k], {k}
        while stack:
            t, w = stack.pop()
            x, y = self.loc[t]
            for dx, dy, ott, ow in self.conn.get((self.ttype[t], w), ()):
                ot = self.at.get((x + dx, y + dy))
                if ot is None or self.ttype[ot] != ott:
                    continue
                kk = (ot, ow)
                if kk not in seen:
                    seen.add(kk)
                    stack.append(kk)
                    members.append(kk)
        n = len(self.nodes)
        self.nodes.append(sorted(members))
        for kk in members:
            self.w2n[kk] = n
        return n

    def node_name(self, n):
        """prjxray NodeModel's naming rule (specific_node_wires, then
        node_pattern_wires), else the first member -- always 'TILE/WIRE'."""
        m = self.nodes[n]
        for t, w in m:
            if "%s/%s" % (t, w) in self.specific:
                return "%s/%s" % (t, w)
        for t, w in m:
            if w in self.pattern.get(self.ttype[t], ()):
                return "%s/%s" % (t, w)
        return "%s/%s" % m[0]

    def sites(self, tile):
        """[(tile-type site dict, instance site name)] in tile-type order."""
        gi = self.grid.gridinfo_at_tilename(tile)
        tto = self.db.get_tile_type(self.ttype[tile])
        inst = list(tto.get_instance_sites(gi))
        js = self.tt(self.ttype[tile])["sites"]
        out = []
        for s in js:
            for i in inst:
                if i.prefix == s["prefix"] and i.type == s["type"] and \
                        (i.x - s["x_coord"], i.y - s["y_coord"]) == \
                        (inst[0].x - js[0]["x_coord"], inst[0].y - js[0]["y_coord"]) and \
                        i.name not in [o[1] for o in out]:
                    out.append((s, i.name))
                    break
        # get_instance_sites keeps tile-type order; fall back to it if the
        # coordinate match above was ambiguous.
        if len(out) != len(js):
            out = list(zip(js, [i.name for i in inst]))
        return out


# =============================================================== FASM

RE_ML = re.compile(r"^(\S+?)\[(\d+):(\d+)\]\s*=\s*(\d+)'b([01_]+)$")
RE_SB = re.compile(r"^(\S+?)\[(\d+)\]$")
RE_EQ = re.compile(r"^(\S+?)\s*=\s*(\d+)'b([01_]+)$")


def parse_fasm(path):
    """-> {tile: {feature: int}}.  Multi-bit features are integers; a plain
    feature is 1.  Both nextpnr's FASM and bit2fasm's output parse here."""
    feats = collections.defaultdict(dict)
    for line in open(path):
        line = line.split("#", 1)[0].strip()
        if not line or line.startswith("{"):
            continue
        m = RE_ML.match(line)
        if m:
            name, hi, lo, _w, bits = m.groups()
            tile, f = name.split(".", 1)
            v = int(bits.replace("_", ""), 2) << int(lo)
            feats[tile][f] = feats[tile].get(f, 0) | v
            continue
        m = RE_SB.match(line)
        if m:
            tile, f = m.group(1).split(".", 1)
            feats[tile][f] = feats[tile].get(f, 0) | (1 << int(m.group(2)))
            continue
        m = RE_EQ.match(line)
        if m:
            tile, f = m.group(1).split(".", 1)
            v = int(m.group(3).replace("_", ""), 2)
            if v:
                feats[tile][f] = feats[tile].get(f, 0) | v
            continue
        tile, f = line.split(".", 1)
        feats[tile][f] = 1
    return feats


def bit_to_fasm(bit, out_fasm):
    """The .bit the board was programmed with -> FASM, via prjxray's own
    bitread + fasm disassembler (utils/bit2fasm.py), with the build's db."""
    env = dict(os.environ)
    env["PYTHONPATH"] = PRJXRAY + ":" + os.path.join(TC, "openxc7/lib/python")
    with open(out_fasm, "w") as f:
        subprocess.check_call(
            [sys.executable, os.path.join(PRJXRAY, "utils/bit2fasm.py"),
             "--db-root", DB_ROOT, "--part", PART,
             "--bitread", os.path.join(TC, "openxc7/bin/bitread"), bit],
            stdout=f, stderr=subprocess.DEVNULL, env=env)


# =============================================================== the design

class Cell:
    def __init__(self, name, ctype, root=False):
        self.name, self.type, self.root = name, ctype, root
        self.ins = {}      # pin -> ('route', tile, wire) | ('int', drvkey) | ('const', v)
        self.outs = []     # output pins
        self.params, self.attrs = {}, {}


class Design:
    def __init__(self, fab, feats):
        self.fab, self.feats = fab, feats
        self.cells = {}
        self.siteout = {}            # (tile, wire) -> drvkey  (site output pin)
        self.sitepin_of = {}         # (tile, wire) -> (site, pin name)
        self.used = set()            # (tile, feature) consumed
        self.problems = collections.Counter()
        self.examples = collections.defaultdict(list)
        self.notes = []

    def problem(self, kind, ex):
        self.problems[kind] += 1
        if len(self.examples[kind]) < 8:
            self.examples[kind].append(ex)

    def sout(self, tile, pins, site, pin, drvkey):
        """register a site OUTPUT pin: its tile wire is driven by drvkey"""
        self.siteout[(tile, pins[pin])] = drvkey
        self.sitepin_of[(tile, pins[pin])] = (site, pin)

    def add(self, cell):
        assert cell.name not in self.cells, cell.name
        self.cells[cell.name] = cell
        return cell

    def has(self, tile, f):
        if self.feats.get(tile, {}).get(f):
            self.used.add((tile, f))
            return True
        return False

    def val(self, tile, f):
        v = self.feats.get(tile, {}).get(f)
        if v is not None:
            self.used.add((tile, f))
        return v or 0

    # ------------------------------------------------------------- routing
    def collect_pips(self):
        """Active pips from the FASM, indexed by the node they drive."""
        self.pipdrv = collections.defaultdict(set)   # node -> {(tile, dst, src)}
        n = 0
        for tile, fs in self.feats.items():
            info = self.fab.tt(self.fab.ttype[tile])
            for f in fs:
                if "[" in f or f.count(".") != 1:
                    continue
                dst, src = f.split(".")
                rev = info["pips"].get((src, dst))
                if (dst, src) in info["pips"] or (rev and rev.get("is_directional") == "0"):
                    # a bidirectional pip (LV/LH long lines) is listed once in
                    # the db; the FASM feature's DST.SRC order gives the direction
                    self.used.add((tile, f))
                    self.pipdrv[self.fab.node(tile, dst)].add((tile, dst, src))
                    n += 1
        self.n_active_pips = n

    def drivers(self, nid):
        """Every candidate driver of node nid:
           ('pip', tile, dst, src, kind)  kind = 'bits' | 'always'
           ('site', tile, wire, drvkey)   a decoded site output pin
           ('const', v, tile, wire)       a tile's VCC_WIRE / GND_WIRE"""
        fab = self.fab
        out = [("pip", t, d, s, "bits") for t, d, s in sorted(self.pipdrv.get(nid, ()))]
        seen = {(t, d, s) for t, d, s in self.pipdrv.get(nid, ())}
        for t, w in fab.nodes[nid]:
            info = fab.tt(fab.ttype[t])
            for s in info["always"].get(w, ()):
                if (t, w, s) not in seen:
                    out.append(("pip", t, w, s, "always"))
            if (t, w) in self.siteout:
                out.append(("site", t, w, self.siteout[(t, w)]))
            if w in CONST_WIRES:
                out.append(("const", CONST_WIRES[w], t, w))
        return out

    def default_of(self, nid):
        for t, w in self.fab.nodes[nid]:
            for s in self.fab.tt(self.fab.ttype[t])["default"].get(w, ()):
                if s in CONST_WIRES:
                    return CONST_WIRES[s], (t, w, s)
        return None

    def resolve(self, nid, _stack=None):
        """-> (root, pips) for node nid.  root is ('drv', drvkey) or
        ('const', v, how) or ('float',) ; pips is the list of pip ids
        'TILE.DST.SRC' from the root down to nid."""
        memo = self._memo
        if nid in memo:
            return memo[nid]
        stack = _stack if _stack is not None else set()
        if nid in stack:
            return ("float",), []           # a loop drives nothing
        stack.add(nid)
        cands = []
        for d in self.drivers(nid):
            if d[0] == "site":
                cands.append((("drv", d[3], (d[1], d[2])), [], d))
            elif d[0] == "const":
                cands.append((("const", d[1], "tile"), [], d))
            else:
                _, t, dst, src, kind = d
                root, pips = self.resolve(self.fab.node(t, src), stack)
                if root[0] == "float" and kind == "always":
                    continue                # a dangling always-on ppip drives nothing
                pid = "%s.%s.%s" % (t, dst, src)
                cands.append((root, pips + [pid], d))
        stack.discard(nid)
        live = [c for c in cands if c[0][0] != "float"]
        if not cands or not live:
            if cands:
                # Only explicit bit-pips from floating nodes are left: that is a
                # configured pip from nothing.
                self.problem("pip driven from a floating node", self.fab.node_name(nid))
            dflt = self.default_of(nid)
            res = (("const", dflt[0], "default"), []) if dflt else (("float",), [])
        else:
            sites = [c for c in live if c[2][0] == "site"]
            if len(live) > 1 and len(sites) == 1 and \
                    all(c[2][0] == "pip" and c[2][4] == "always" for c in live if c is not sites[0]):
                # a decoded site output shadows an always-on ppip that models
                # the same site's route-through (e.g. BUFGCTRL O <- *_IN)
                self.problem("always-ppip shadowed by a used site output",
                             self.fab.node_name(nid))
                live = sites
            if len(live) > 1:
                self.problem("CONTENTION: more than one active driver on a node",
                             "%s <- %s" % (self.fab.node_name(nid), [c[2] for c in live]))
            res = (live[0][0], live[0][1])
        memo[nid] = res
        return res

    # ------------------------------------------------------------- sites
    def decode(self):
        for tile in sorted(self.feats):
            tt = self.fab.ttype[tile]
            if tt.startswith("CLBL"):
                self.decode_clb(tile)
            elif tt.startswith("CLK_BUFG") and not tt.startswith("CLK_BUFG_REBUF"):
                self.decode_bufg(tile)
            elif tt.startswith("CFG_CENTER"):
                self.decode_cfg(tile)
            elif tt in ("RIOB33", "LIOB33", "RIOB33_SING", "LIOB33_SING"):
                self.decode_iob(tile)
            elif tt.startswith("CLK_HROW"):
                self.decode_hrow(tile)
            elif tt.startswith("RIOI3") or tt.startswith("LIOI3"):
                self.decode_ioi(tile)

    def sitepins(self, tile, sname):
        for s, name in self.fab.sites(tile):
            if name == sname:
                return {p: (v["wire"] if v else None) for p, v in s["site_pins"].items()}
        raise KeyError((tile, sname))

    def decode_clb(self, tile):
        fs = self.feats[tile]
        for s, sname in self.fab.sites(tile):
            pfx = "%s_X%d." % (s["type"], s["x_coord"])
            if not any(f.startswith(pfx) for f in fs):
                continue
            self.decode_slice(tile, sname, pfx, s["type"],
                              {p: v["wire"] for p, v in s["site_pins"].items() if v})

    def decode_slice(self, tile, site, pfx, stype, pins):
        has = lambda f: self.has(tile, pfx + f)
        val = lambda f: self.val(tile, pfx + f)
        R = lambda p: ("route", tile, pins[p], site, p)
        K = lambda cell, pin: ("int", ("%s/%s" % (site, cell), pin))
        for f in self.feats[tile]:
            if f.startswith(pfx) and re.search(r"\.(RAM|SMALL|SRL)$|WA[78]USED|WEMUX|DI1MUX", f) \
                    and self.feats[tile][f]:
                if "DI1MUX" in f:
                    self.used.add((tile, f))        # LUTRAM data mux: unused unless RAM/SRL
                    continue
                self.problem("REFUSED: LUTRAM/SRL configured", "%s.%s" % (tile, f))
        if has("LATCH"):
            self.problem("REFUSED: slice in LATCH mode (prims.v has no latch bel)", "%s %s" % (tile, site))
        clkinv = has("CLKINV")
        has("NOCLKINV")
        ffsync = has("FFSYNC")
        ceused, srused = has("CEUSEDMUX"), has("SRUSEDMUX")
        # ---- LUTs: one cell per output; both see the same six physical pins.
        for L in LUTS:
            init = val("%sLUT.INIT" % L)
            for out, bel, width in (("O6", "%s6LUT" % L, 64), ("O5", "%s5LUT" % L, 32)):
                # A LUT6 whose upper half is configured exists even if nothing
                # reads it (nextpnr keeps dead LUTs; so does the die).  Any
                # other LUT exists only if something the bits configure reads it.
                c = Cell("%s/%s" % (site, bel), "SLICE_LUTX",
                         root=(out == "O6" and (init >> 32) != 0))
                for i in range(1, 7):
                    c.ins["A%d" % i] = R("%s%d" % (L, i))
                c.outs = [out]
                tbl = init & ((1 << width) - 1)
                c.params["INIT"] = format(tbl, "0%db" % width)
                for i in range(1, 7 if width == 64 else 6):
                    c.attrs["X_ORIG_PORT_A%d" % i] = "I%d" % (i - 1)
                self.add(c)
        # ---- wide muxes
        for name, d0, d1, s in (("F7AMUX", K("B6LUT", "O6"), K("A6LUT", "O6"), "AX"),
                                ("F7BMUX", K("D6LUT", "O6"), K("C6LUT", "O6"), "CX"),
                                ("F8MUX", K("F7BMUX", "OUT"), K("F7AMUX", "OUT"), "BX")):
            c = Cell("%s/%s" % (site, name), "SELMUX2_1")
            c.ins.update({"0": d0, "1": d1, "S0": R(s)})
            c.outs = ["OUT"]
            self.add(c)
        # ---- CARRY4
        pre = [p for p in ("AX", "CIN", "C1", "C0") if has("PRECYINIT." + p)]
        if len(pre) > 1:
            self.problem("PRECYINIT decodes to more than one value", "%s %s %s" % (tile, site, pre))
        pre = pre[0] if pre else "C0"        # C0 is the all-zero encoding
        c = Cell("%s/CARRY4" % site, "CARRY4")
        if pre == "CIN":
            c.ins["CIN"] = R("CIN")
        elif pre == "AX":
            c.ins["CYINIT"] = R("AX")
        else:
            c.params["PRECYINIT_CONST"] = pre[1]
        for i, L in enumerate(LUTS):
            c.ins["S%d" % i] = K("%s6LUT" % L, "O6")
            c.ins["DI%d" % i] = K("%s5LUT" % L, "O5") if has("CARRY4.%sCY0" % L) else R(L + "X")
        c.outs = ["O%d" % i for i in range(4)] + ["CO%d" % i for i in range(4)]
        self.add(c)
        # ---- flops
        def ff(name, d, zini, zrst):
            c = Cell("%s/%s" % (site, name), "SLICE_FFX", root=True)
            c.ins["CK"] = R("CLK")
            c.ins["D"] = d
            c.ins["CE"] = R("CE") if ceused else ("const", 1)
            c.ins["SR"] = R("SR") if srused else ("const", 0)
            c.outs = ["Q"]
            c.params["INIT"] = "0" if zini else "1"
            c.attrs["X_ORIG_PORT_SR"] = "R" if zrst else "S"
            c.attrs["X_FFSYNC"] = "1" if ffsync else "0"
            if clkinv:
                self.problem("REFUSED: inverted slice clock (CLKINV)", "%s %s" % (tile, c.name))
            if srused and not ffsync:
                self.problem("REFUSED: asynchronous SR (FDCE/FDPE) -- prims.v is synchronous",
                             "%s %s" % (tile, c.name))
            self.add(c)
        for i, L in enumerate(LUTS):
            srcs = {"%sX" % L: R(L + "X"), "O6": K("%s6LUT" % L, "O6"), "O5": K("%s5LUT" % L, "O5"),
                    "CY": K("CARRY4", "CO%d" % i), "XOR": K("CARRY4", "O%d" % i)}
            if L == "A":
                srcs["F7"] = K("F7AMUX", "OUT")
            if L == "C":
                srcs["F7"] = K("F7BMUX", "OUT")
            if L == "B":
                srcs["F8"] = K("F8MUX", "OUT")
            sel = [k for k in srcs if has("%sFFMUX.%s" % (L, k))]
            if len(sel) > 1:
                self.problem("FFMUX decodes to more than one value", "%s %s %s" % (tile, site, sel))
            if sel:
                ff("%sFF" % L, srcs[sel[0]], has("%sFF.ZINI" % L), has("%sFF.ZRST" % L))
                self.sout(tile, pins, site, L + "Q", ("%s/%sFF" % (site, L), "Q"))
            sel5 = [k for k, src in (("IN_A", K("%s5LUT" % L, "O5")), ("IN_B", R(L + "X")))
                    if has("%s5FFMUX.%s" % (L, k))]
            if sel5:
                ff("%s5FF" % L, K("%s5LUT" % L, "O5") if sel5[0] == "IN_A" else R(L + "X"),
                   has("%s5FF.ZINI" % L), has("%s5FF.ZRST" % L))
            # site outputs
            self.sout(tile, pins, site, L, ("%s/%s6LUT" % (site, L), "O6"))
            outsel = dict(srcs)
            outsel.pop("%sX" % L)
            outsel["%s5Q" % L] = K("%s5FF" % L, "Q")
            sel = [k for k in outsel if has("%sOUTMUX.%s" % (L, k))]
            if len(sel) > 1:
                self.problem("OUTMUX decodes to more than one value", "%s %s %s" % (tile, site, sel))
            if sel:
                self.sout(tile, pins, site, L + "MUX", outsel[sel[0]][1])
        self.sout(tile, pins, site, "COUT", ("%s/CARRY4" % site, "CO3"))

    def decode_bufg(self, tile):
        for s, sname in self.fab.sites(tile):
            if s["type"] != "BUFGCTRL":
                continue
            pfx = "BUFGCTRL.BUFGCTRL_X%dY%d." % (s["x_coord"], s["y_coord"])   # tile-relative
            if not self.has(tile, pfx + "IN_USE"):
                continue
            pins = {p: v["wire"] for p, v in s["site_pins"].items() if v}
            c = Cell("%s/BUFGCTRL" % sname, "BUFGCTRL", root=True)
            for p in ("I0", "I1", "S0", "S1", "CE0", "CE1", "IGNORE0", "IGNORE1"):
                c.ins[p] = ("route", tile, pins[p], sname, p)
            c.outs = ["O"]
            inv = {"S0": not self.has(tile, pfx + "ZINV_S0"), "S1": not self.has(tile, pfx + "ZINV_S1"),
                   "CE0": not self.has(tile, pfx + "ZINV_CE0"), "CE1": not self.has(tile, pfx + "ZINV_CE1"),
                   "IGNORE0": self.has(tile, pfx + "IS_IGNORE0_INVERTED"),
                   "IGNORE1": self.has(tile, pfx + "IS_IGNORE1_INVERTED")}
            for p, v in inv.items():
                if v:
                    c.params["IS_%s_INVERTED" % p] = "1"
            for f in ("INIT_OUT", "PRESELECT_I1", "ZPRESELECT_I0"):
                self.has(tile, pfx + f)
            c._inv = inv
            self.add(c)
            self.sout(tile, pins, sname, "O", (c.name, "O"))

    def decode_hrow(self, tile):
        """BUFHCE is a buffer the clock passes THROUGH (prjxray models I->O as
        an always-on ppip); it passes only if configured IN_USE with CE=1.
        check_clock_enables() holds every routed path through one to that."""
        self.bufhce = getattr(self, "bufhce", {})
        for s, sname in self.fab.sites(tile):
            if s["type"] != "BUFHCE":
                continue
            pfx = "BUFHCE.BUFHCE_X%dY%d." % (s["x_coord"], s["y_coord"])   # tile-relative
            pins = {p: v["wire"] for p, v in s["site_pins"].items() if v}
            self.bufhce[(tile, pins["I"])] = (sname, self.has(tile, pfx + "IN_USE"),
                                              not self.has(tile, pfx + "ZINV_CE"), pins["CE"])
            self.has(tile, pfx + "CE_TYPE.ASYNC")
            self.has(tile, pfx + "INIT_OUT")
        for f in self.feats[tile]:
            if re.match(r"CLK_HROW_R_CK_GCLK\d+_ACTIVE$", f):
                self.used.add((tile, f))

    def decode_cfg(self, tile):
        for f in list(self.feats[tile]):
            m = re.match(r"BSCAN\.JTAG_CHAIN_(\d)$", f)
            if not m:
                continue
            self.used.add((tile, f))
            n = int(m.group(1))
            for s, sname in self.fab.sites(tile):
                if s["type"] == "BSCAN" and s["site_pins"]["TDO"]["wire"].endswith("BSCAN%d_TDO" % n):
                    pins = {p: v["wire"] for p, v in s["site_pins"].items() if v}
                    c = Cell("%s/BSCAN" % sname, "BSCAN", root=True)
                    c.ins["TDO"] = ("route", tile, pins["TDO"], sname, "TDO")
                    c.outs = ["CAPTURE", "DRCK", "RESET", "RUNTEST", "SEL", "SHIFT",
                              "TCK", "TDI", "TMS", "UPDATE"]
                    c.params["JTAG_CHAIN"] = format(n, "032b")
                    self.add(c)
                    for p in c.outs:
                        self.sout(tile, pins, sname, p, (c.name, p))
        for f in self.feats[tile]:
            if f.startswith("ALWAYS_ON_PROP"):
                self.used.add((tile, f))

    def decode_ioi(self, tile):
        """OLOGIC used as a plain output path (OMUX.D1, OQUSED): D1 -> OQ.  An
        ILOGIC/IDELAY default feature set (bit2fasm prints the all-zero
        encodings) is accepted only if no ILOGIC output is routed anywhere."""
        self.ologic = getattr(self, "ologic", {})
        n_ol = sum(1 for s, _ in self.fab.sites(tile) if s["type"] == "OLOGICE3")
        for s, sname in self.fab.sites(tile):
            if s["type"] != "OLOGICE3":
                continue
            # FASM's _Y<n> counts from the TOP of the tile pair (Y0 = the site
            # with the larger y, wires *OLOGIC0*), as in fasm2bels get_ioi_site
            pfx = "OLOGIC_Y%d." % (n_ol - 1 - s["y_coord"])
            if not self.has(tile, pfx + "OQUSED"):
                continue
            pins = {p: v["wire"] for p, v in s["site_pins"].items() if v}
            if not self.has(tile, pfx + "OMUX.D1"):
                self.problem("REFUSED: OLOGIC OQ not from D1 (OSERDES/ODDR mode)", "%s %s" % (tile, sname))
                continue
            self.has(tile, pfx + "OSERDES.DATA_RATE_TQ.BUF")
            # D1 -> OQ is then a plain wire: prjxray-db models it as an
            # always-on ppip, so the route walk passes through it.
            # check_path_configs() holds every path through that ppip to an
            # OLOGIC configured exactly like this.  The pad's output enable is
            # TQ = T1 (BUF mode), T1 inverted unless ZINV_T1.
            self.ologic[(tile, pins["OQ"])] = (sname, ("route", tile, pins["T1"]),
                                               not self.has(tile, pfx + "ZINV_T1"))
        for f in self.feats[tile]:
            if re.match(r"(ILOGIC|IDELAY)_Y\d\.", f) and \
                    re.search(r"IDELMUXE3\.P1|IFF\.SRTYPE\.ASYNC|ISERDES\.(MODE\.MASTER|NUM_CE\.N1)|"
                              r"IDELAY_TYPE_FIXED|ZINV_|IFFDELMUXE3\.P0|IDELMUXE3\.P0", f):
                self.used.add((tile, f))        # all-zero default encodings; no input used

    def decode_iob(self, tile):
        n_iob = len(self.fab.sites(tile))
        for s, sname in self.fab.sites(tile):
            pfx = "IOB_Y%d." % (n_iob - 1 - s["y_coord"])     # Y0 = IOB33M, the upper site
            drive = [f for f in self.feats[tile] if f.startswith(pfx) and ".DRIVE." in f]
            for f in self.feats[tile]:
                if f.startswith(pfx):
                    self.used.add((tile, f))    # electrical settings: no logic meaning
            if not drive:
                continue
            pins = {p: v["wire"] for p, v in s["site_pins"].items() if v}
            ob = Cell("%s/IOB33/OUTBUF" % sname, "IOB33_OUTBUF", root=True)
            ob.ins["IN"] = ("route", tile, pins["O"], sname, "O")
            ob.outs = ["OUT"]
            self.add(ob)
            pad = Cell("%s/IOB33/PAD" % sname, "PAD", root=True)
            pad.ins["PAD"] = ("int", (ob.name, "OUT"))
            self.add(pad)

    # ------------------------------------------------------------- build
    def build(self):
        self.collect_pips()
        self.decode()
        self._memo = {}
        # every routed input pin of every candidate cell
        self.sink_root = {}
        for c in self.cells.values():
            for p, src in c.ins.items():
                if src[0] == "route":
                    nid = self.fab.node(src[1], src[2])
                    self.sink_root[(c.name, p)] = self.resolve(nid)
        # liveness: a non-root cell exists only if a live cell consumes it
        live = set(self.cells)
        while True:
            consumed = set()
            for cn in live:
                c = self.cells[cn]
                for p, src in c.ins.items():
                    d = self.driver_of(c, p)
                    if d and d[0] == "drv":
                        consumed.add(d[1][0])
            nl = {cn for cn in live if self.cells[cn].root or cn in consumed}
            if nl == live:
                break
            live = nl
        self.live = live
        for cn in sorted(set(self.cells) - live):
            del self.cells[cn]
        # every consumed driver must exist
        for c in self.cells.values():
            for p in list(c.ins):
                d = self.driver_of(c, p)
                if d and d[0] == "drv" and d[1][0] not in self.cells:
                    self.problem("sink driven by a bel that is not configured", "%s/%s <- %s" % (c.name, p, d))
                if d and d[0] == "float" and (c.type, p) == ("BUFGCTRL", "I1"):
                    # unused clock input of a BUFGCTRL; check_bufg() proves the
                    # control pins deselect it, so it is left unconnected
                    self.notes.append("%s/I1 is not driven (deselected: see check_bufg)" % c.name)
                    c.ins.pop(p)
                    continue
                if d and d[0] == "float":
                    self.problem("FLOATING input: nothing drives this pin's node", "%s/%s" % (c.name, p))

    def driver_of(self, c, p):
        src = c.ins[p]
        if src[0] == "route":
            root, _ = self.sink_root[(c.name, p)]
            if root[0] == "drv":
                return ("drv", root[1])
            if root[0] == "const":
                return ("const", root[1], root[2])
            return ("float",)
        if src[0] == "int":
            return ("drv", src[1])
        return ("const", src[1], "site")

    # ------------------------------------------------------------- checks
    def check_bufg(self):
        for c in self.cells.values():
            if c.type != "BUFGCTRL":
                continue
            eff = {}
            for p in ("S0", "S1", "CE0", "CE1", "IGNORE0", "IGNORE1"):
                d = self.driver_of(c, p)
                if d[0] != "const":
                    self.problem("REFUSED: BUFGCTRL control pin is not a constant", "%s/%s" % (c.name, p))
                    continue
                eff[p] = d[1] ^ int(c._inv[p])
            if eff.get("S0") == 1 and eff.get("CE0") == 1 and (eff.get("S1") == 0 or eff.get("CE1") == 0):
                continue
            self.problem("REFUSED: BUFGCTRL does not reduce to O = I0", "%s %s" % (c.name, eff))

    def check_outputs(self):
        for sname, t1, inv in getattr(self, "ologic", {}).values():
            root, _ = self.resolve(self.fab.node(t1[1], t1[2]))
            if root[0] == "const":
                if root[1] ^ int(inv):
                    self.problem("output pad tristated (T=1)", sname)
            else:
                self.problem("output pad enable not constant", sname)

    def check_clock_enables(self, sinkpaths):
        """Clock-spine buffers need a configuration bit besides the pip."""
        need = collections.Counter()
        for pips in sinkpaths:
            for pid in pips:
                tile, dst, src = pid.split(".")
                tt = self.fab.ttype[tile]
                if re.match(r"[LR]IOI_OLOGIC\d_OQ$", dst) and (tile, dst) not in getattr(self, "ologic", {}):
                    need["%s OLOGIC route-through %s<-%s without OQUSED+OMUX.D1" % (tile, dst, src)] += 1
                m = re.match(r"HCLK_CK_BUFHCLK(\d+)$", src)
                if tt.startswith("HCLK_") and m:
                    f = "ENABLE_BUFFER.HCLK_CK_BUFHCLK%s" % m.group(1)
                    if not self.has(tile, f):
                        need["%s.%s" % (tile, f)] += 1
                m = re.match(r"CLK_HROW_R_CK_GCLK(\d+)$", src)
                if tt.startswith("CLK_HROW") and m:
                    f = "CLK_HROW_R_CK_GCLK%s_ACTIVE" % m.group(1)
                    if not self.has(tile, f):
                        need["%s.%s" % (tile, f)] += 1
                if (tile, src) in getattr(self, "bufhce", {}) and dst.startswith("CLK_HROW_CK_HCLK_OUT"):
                    sname, inuse, ceinv, cepin = self.bufhce[(tile, src)]
                    root, _ = self.resolve(self.fab.node(tile, cepin))
                    ce = root[1] ^ int(ceinv) if root[0] == "const" else None
                    if not inuse or ce != 1:
                        need["%s %s IN_USE=%s CE=%s" % (tile, sname, inuse, ce)] += 1
                m = re.match(r"CLK_BUFG_REBUF_R_CK_GCLK(\d+)_(TOP|BOT)$", src)
                if tt == "CLK_BUFG_REBUF" and m:
                    f = "GCLK%s_ENABLE_%s" % (m.group(1), "BELOW" if m.group(2) == "TOP" else "ABOVE")
                    if not self.has(tile, f):
                        need["%s.%s" % (tile, f)] += 1
        for tile, fs in self.feats.items():
            for f in fs:
                if re.match(r"GCLK\d+_ENABLE_(ABOVE|BELOW)$|HCLK_CMT_CK_BUFHCLK\d+_USED$", f):
                    self.used.add((tile, f))
        for k, v in need.items():
            self.problem("clock buffer used without its enable bit", "%s (%d sinks)" % (k, v))


# =============================================================== emit

def emit(des, out_dir, names_json=None, sdf_in=None):
    fab = des.fab
    cells = des.cells
    # ---- nets: one per driver
    drvkeys = set()
    conns = {}
    for c in cells.values():
        for p in c.ins:
            d = des.driver_of(c, p)
            if d[0] == "drv":
                k = d[1]
            elif d[0] == "const":
                k = ("$const", d[1])
            else:
                continue
            conns[(c.name, p)] = k
            drvkeys.add(k)
    for c in cells.values():
        for p in c.outs:
            drvkeys.add((c.name, p))
    const_cells = {1: ("$VCC", "PSEUDO_VCC"), 0: ("$GND", "PSEUDO_GND")}
    order = sorted(drvkeys, key=lambda k: (str(k[0]), str(k[1])))
    bit = {k: i + 2 for i, k in enumerate(order)}

    def netname(k):
        if k[0] == "$const":
            return "$const%d" % k[1]
        return "%s/%s" % k

    jcells = {}
    for c in sorted(cells.values(), key=lambda c: c.name):
        if c.type == "ROUTETHRU":
            continue
        jc = {"type": c.type, "parameters": dict(c.params),
              "attributes": dict(c.attrs, NEXTPNR_BEL=c.name, FASM2NET="1"),
              "port_directions": {}, "connections": {}}
        for p in c.ins:
            k = conns.get((c.name, p))
            # a route-through is a wire, not a cell: look through it
            while k and k[0] in cells and cells[k[0]].type == "ROUTETHRU":
                k = conns.get((k[0], "I"))
            jc["connections"][p] = [bit[k]] if k else []
            jc["port_directions"][p] = "input"
        for p in c.outs:
            jc["connections"][p] = [bit[(c.name, p)]]
            jc["port_directions"][p] = "output"
        jcells[c.name] = jc
    used_consts = {k[1] for k in conns.values() if k[0] == "$const"}
    for v in sorted(used_consts):
        n, t = const_cells[v]
        jcells[n] = {"type": t, "parameters": {}, "attributes": {"NEXTPNR_BEL": n, "FASM2NET": "1"},
                     "port_directions": {"Y": "output"}, "connections": {"Y": [bit[("$const", v)]]}}

    # ---- routes: per sink, the pip path, in prjxray names
    rows, sinkpaths = [], []
    routing = collections.defaultdict(dict)
    pipname = {}                 # (src node, dst node) -> prjxray pip TILE.DST.SRC
    for (cn, p), (root, pips) in sorted(des.sink_root.items()):
        if cn not in cells:
            continue
        k = conns.get((cn, p))
        if k is None:
            continue
        sinkpaths.append(pips)
        rows.append("%s\t%s/%s\t%s\t%s" % (netname(k), cn, p,
                                          root[2] if root[0] == "const" else "", " ".join(pips)))
        # ROUTING, in nextpnr's own grammar ("dst;src->dst;strength" triples,
        # a wire named by its prjxray NODE, site pins as SITEWIRE/<site>/<pin>)
        # so whatever reads nextpnr's ROUTING (gen.py's wire scatter, F1's
        # delay calculator) reads the BOARD's route the same way.
        r = routing[k]
        if root[0] == "drv" and len(root) > 2 and root[2] in des.sitepin_of:
            st, sp = des.sitepin_of[root[2]]
            src = "SITEWIRE/%s/%s" % (st, sp)
            n0 = fab.node_name(fab.node(*root[2]))
            r.setdefault(src, "")
            r.setdefault(n0, "%s->%s" % (src, n0))
        for pid in pips:
            t, d, s_ = pid.split(".")
            sn, dn = fab.node_name(fab.node(t, s_)), fab.node_name(fab.node(t, d))
            r[dn] = "%s->%s" % (sn, dn)
            pipname[(sn, dn)] = pid
        src_ = cells[cn].ins[p]
        if src_[0] == "route" and len(src_) > 3:
            sw = "SITEWIRE/%s/%s" % (src_[3], src_[4])
            r[sw] = "%s->%s" % (fab.node_name(fab.node(src_[1], src_[2])), sw)
    des.check_clock_enables(sinkpaths)
    # configured pips on no live sink's path: routing to a bel that the bits
    # do not otherwise use (nextpnr keeps dead cells and routes to them), or a
    # stub.  Listed, so the routing comparison can tell them from a mis-route.
    on_path = {pid for pips in sinkpaths for pid in pips}
    stubs = {"%s.%s.%s" % k for v in des.pipdrv.values() for k in v
             if "%s.%s.%s" % k not in on_path}
    # ...and the always-on ppips a stub continues into (they carry no bits)
    work = list(stubs)
    while work:
        t0, d0, _ = work.pop().split(".")
        for t, w in fab.nodes[fab.node(t0, d0)]:
            for dst, srcs in fab.tt(fab.ttype[t])["always"].items():
                pid = "%s.%s.%s" % (t, dst, w)
                if w in srcs and pid not in stubs and pid not in on_path:
                    stubs.add(pid)
                    work.append(pid)
    stubs = sorted(stubs)
    with open(os.path.join(out_dir, "stubs.tsv"), "w") as f:
        f.write("# configured pip on no live sink path\tits destination node\n")
        for pid in stubs:
            t, d, _ = pid.split(".")
            f.write("%s\t%s\n" % (pid, fab.node_name(fab.node(t, d))))
    des.notes.append("%d configured pips lie on no live sink's path (stubs.tsv)" % len(stubs))

    netnames = {}
    for k in order:
        nn = {"bits": [bit[k]], "hide_name": 0, "attributes": {}}
        if k in routing:
            nn["attributes"]["ROUTING"] = ";".join(
                "%s;%s;1" % (w, pip) for w, pip in sorted(routing[k].items()))
        netnames[netname(k)] = nn

    # ---- aliases: the routed JSON's net names, attached BY DRIVER BEL PIN, so
    # the testbenches can find hk_fb, rig_lap ... on the board's own nets.
    alias_n = alias_miss = 0
    bel_of = {}
    if names_json:
        top = json.load(open(names_json))["modules"]["top"]
        jdrv = {}
        for cname, c in top["cells"].items():
            bel = c["attributes"].get("NEXTPNR_BEL", "")
            bel_of[cname] = bel
            for p, bl in c["connections"].items():
                if c.get("port_directions", {}).get(p) == "output" and bl:
                    jdrv[bl[0]] = (cname, p, c["type"])
        for name, nn in top["netnames"].items():
            if len(nn["bits"]) != 1 or not isinstance(nn["bits"][0], int):
                continue
            d = jdrv.get(nn["bits"][0])
            if d is None:
                continue
            if d[2] == "PSEUDO_VCC":
                k = ("$const", 1)
            elif d[2] == "PSEUDO_GND":
                k = ("$const", 0)
            else:
                k = (bel_of[d[0]], d[1])
            if k in bit and name not in netnames:
                netnames[name] = {"bits": [bit[k]], "hide_name": 0,
                                  "attributes": {"FASM2NET_ALIAS": "by driver %s/%s" % k}}
                alias_n += 1
            elif k not in bit:
                alias_miss += 1
    des.notes.append("aliases: %d routed-JSON net names attached by driver bel pin, "
                     "%d whose driver has no net here" % (alias_n, alias_miss))

    with open(os.path.join(out_dir, "pipnames.tsv"), "w") as f:
        f.write("# ROUTING pip (src node -> dst node)\tprjxray tile pip TILE.DST.SRC\n")
        for (sn, dn), pid in sorted(pipname.items()):
            f.write("%s->%s\t%s\n" % (sn, dn, pid))
    j = {"creator": "fasm2net.py", "modules": {"top": {
        "attributes": {}, "ports": {}, "cells": jcells, "netnames": netnames}}}
    json.dump(j, open(os.path.join(out_dir, "fasm_routed.json"), "w"))
    with open(os.path.join(out_dir, "routes.tsv"), "w") as f:
        f.write("# net(driver)\tsink\tconst-source\tpips (prjxray TILE.DST.SRC, driver -> sink)\n")
        f.write("\n".join(rows) + "\n")

    if sdf_in:
        rekey_sdf(des, jcells, bit, conns, names_json, sdf_in,
                  os.path.join(out_dir, "fasm.sdf"))
    return jcells


RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+(\(.*)$")
RE_CT = re.compile(r'\(CELLTYPE "([^"]*)"\)')


def rekey_sdf(des, jcells, bit, conns, names_json, sdf_in, sdf_out):
    """nextpnr's SDF names nextpnr CELLS; this netlist names BELS.  Cell arcs
    move to the cell on the same bel.  An INTERCONNECT is keyed by its SINK
    (bel/pin) and its source is rewritten to THIS netlist's driver of that
    sink -- so the delay of a wire is carried, and the connectivity always
    comes from the bits.  Where the two disagree on the driver it is counted:
    the number is then a delay for a route the board does not have."""
    top = json.load(open(names_json))["modules"]["top"]
    bel = {}
    for cname, c in top["cells"].items():
        b = c["attributes"].get("NEXTPNR_BEL", "")
        if c["type"] == "PSEUDO_VCC":
            b = "$VCC"
        elif c["type"] == "PSEUDO_GND":
            b = "$GND"
        bel[cname] = b
    unesc = lambda s: s.replace("\\", "")
    blocks = []      # (celltype, inst, [lines])
    ic = {}
    cur = None
    for line in open(sdf_in):
        m = RE_IC.search(line)
        if m:
            src, dst = unesc(m.group(1)), unesc(m.group(2))
            dc, _, dp = dst.rpartition("/")
            sc, _, sp = src.rpartition("/")
            key = (bel.get(dc, "?" + dc), dp)
            ic[key] = ((bel.get(sc, "?" + sc), sp), m.group(3).strip().rstrip(")").strip())
            continue
        m = RE_CT.search(line)
        if m:
            cur = [m.group(1), None, []]
            blocks.append(cur)
        m = RE_INST.search(line)
        if m and cur is not None:
            cur[1] = unesc(m.group(1))
            continue
        if cur is not None and ("IOPATH" in line or "SETUPHOLD" in line or "SETUP" in line or "HOLD" in line):
            cur[2].append(line.rstrip())
    S = ["(DELAYFILE", '  (SDFVERSION "3.0")', '  (DESIGN "top")', '  (VENDOR "fasm2net")',
         '  (PROGRAM "fasm2net.py re-key of %s")' % os.path.basename(sdf_in),
         "  (DIVIDER /)", "  (TIMESCALE 1ps)"]
    st = collections.Counter()
    for ct, inst, lines in blocks:
        if not inst or ct == "top":
            continue
        b = bel.get(inst)
        if b not in jcells:
            st["cell arcs for a bel this netlist does not have"] += 1
            continue
        S.append('  (CELL (CELLTYPE "%s") (INSTANCE %s)' % (ct, b))
        io = [l for l in lines if "IOPATH" in l]
        tc = [l for l in lines if "IOPATH" not in l]
        if io:
            S.append("    (DELAY (ABSOLUTE")
            S.extend(io)
            S.append("    ))")
        if tc:
            S.append("    (TIMINGCHECK")
            S.extend(tc)
            S.append("    )")
        S.append("  )")
        st["cells re-keyed"] += 1
    S.append('  (CELL (CELLTYPE "top") (INSTANCE )')
    S.append("    (DELAY (ABSOLUTE")
    for cn, jc in sorted(jcells.items()):
        for p, bl in sorted(jc["connections"].items()):
            if jc["port_directions"].get(p) != "input" or not bl:
                continue
            k = conns.get((cn, p))
            while k and k[0] in des.cells and des.cells[k[0]].type == "ROUTETHRU":
                k = conns.get((k[0], "I"))
            drv = "$VCC" if k == ("$const", 1) else "$GND" if k == ("$const", 0) else k[0]
            dpin = "Y" if k[0] == "$const" else k[1]
            e = ic.get((cn, p))
            if e is None and jc["type"] == "SLICE_LUTX":
                # the same physical pin seen from the sibling LUT bel
                sib = cn[:-4] + ("5LUT" if cn.endswith("6LUT") else "6LUT")
                e = ic.get((sib, p))
                if e is not None:
                    st["interconnect taken from the sibling LUT bel (same physical pin)"] += 1
            if e is None:
                st["sinks with no nextpnr interconnect (0 ps)"] += 1
                delay = "(0:0:0) (0:0:0)"
            else:
                (sb, sp), delay = e
                if (sb, sp) != (drv, dpin) and not (drv[0] == "$" and sb in ("$VCC", "$GND")):
                    st["DRIVER MISMATCH: nextpnr's arc has another source"] += 1
                    des.problem("SDF interconnect source differs from the bitstream's driver",
                                "%s/%s: sdf %s/%s, bits %s/%s" % (cn, p, sb, sp, drv, dpin))
                st["interconnects re-keyed"] += 1
            S.append("        (INTERCONNECT %s/%s %s/%s %s" % (drv, dpin, cn, p, delay
                                                              if delay.endswith(")") else delay + ")"))
    S.append("    ))")
    S.append("  )")
    S.append(")")
    open(sdf_out, "w").write("\n".join(S) + "\n")
    des.sdf_stats = st


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--bit", help="the bitstream (decoded with prjxray bit2fasm)")
    g.add_argument("--fasm", help="a FASM file (nextpnr's, or bit2fasm's)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--names", help="routed JSON: ONLY for naming (aliases, SDF re-key)")
    ap.add_argument("--sdf", help="SDF to re-key onto this netlist (needs --names)")
    ap.add_argument("--allow", action="store_true", help="write outputs despite REFUSED items")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    fasm = a.fasm
    if a.bit:
        fasm = os.path.join(a.out, "board.fasm")
        bit_to_fasm(a.bit, fasm)
    fab = Fabric(DB_ROOT, PART)
    des = Design(fab, parse_fasm(fasm))
    des.build()
    des.check_bufg()
    des.check_outputs()
    emit(des, a.out, a.names, a.sdf)

    unused = collections.Counter()
    unused_ex = collections.defaultdict(list)
    for tile, fs in des.feats.items():
        for f, v in fs.items():
            if v and (tile, f) not in des.used:
                k = "%s.%s" % (fab.ttype[tile], re.sub(r"\d+", "N", f))
                unused[k] += 1
                if len(unused_ex[k]) < 3:
                    unused_ex[k].append("%s.%s" % (tile, f))
    # all-zero encodings bit2fasm prints for every occupied tile are not configuration
    zero_ok = re.compile(r"PRECYINIT\.C0$|NOCLKINV$|\.ZINV_|DI1MUX\.")
    R = []
    tcount = collections.Counter(c["type"] for c in json.load(
        open(os.path.join(a.out, "fasm_routed.json")))["modules"]["top"]["cells"].values())
    R.append("source: %s" % (a.bit or a.fasm))
    R.append("db: %s  part: %s" % (DB_ROOT, PART))
    R.append("active pips (bits or listed ppips): %d   nodes touched: %d" % (des.n_active_pips, len(fab.nodes)))
    R.append("cells: %d  %s" % (sum(tcount.values()), dict(sorted(tcount.items()))))
    R.append("sinks traced: %d" % len(des.sink_root))
    roots = collections.Counter(r[0][0] + ("/" + r[0][2] if r[0][0] == "const" else "")
                                for k, r in des.sink_root.items() if k[0] in des.cells)
    R.append("sink roots: %s" % dict(roots))
    for k, v in sorted(getattr(des, "sdf_stats", {}).items()):
        R.append("sdf: %-70s %d" % (k, v))
    R.append("")
    R.append("PROBLEMS (%d kinds):" % len(des.problems))
    for k, v in sorted(des.problems.items()):
        R.append("  %6d  %s" % (v, k))
        for e in des.examples[k]:
            R.append("            e.g. %s" % (e,))
    R.append("")
    real_unused = {k: v for k, v in unused.items() if not zero_ok.search(k)}
    R.append("CONFIGURED FEATURES NOT CONSUMED: %d kinds (%d all-zero encodings ignored)"
             % (len(real_unused), len(unused) - len(real_unused)))
    for k, v in sorted(real_unused.items(), key=lambda kv: -kv[1]):
        R.append("  %6d  %s   e.g. %s" % (v, k, unused_ex[k][0]))
    R.append("")
    R.extend("note: " + n for n in des.notes)
    open(os.path.join(a.out, "report.txt"), "w").write("\n".join(R) + "\n")
    print("\n".join(R[:60]))
    refused = [k for k in des.problems if k.startswith(("REFUSED", "CONTENTION", "FLOATING"))]
    if refused and not a.allow:
        sys.exit("fasm2net: %d refused/contention/floating kinds -- see report.txt" % len(refused))


if __name__ == "__main__":
    main()
