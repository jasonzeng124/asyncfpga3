#!/usr/bin/env python3
"""
xray_delay.py -- a prjxray-based delay calculator for a nextpnr-xilinx route.

    PYTHONPATH=$PRJXRAY python3 cells/gls/fid/xray_delay.py \
        --routed build/hw/gcd_hw/gcd_hw_routed.json \
        --sdf    build/hw/gcd_hw/gcd_hw.sdf \
        --out    build/hw/gcd_hw/gcd_hw_xray.sdf  [--arcs arcs.tsv]

WHAT IT REPLACES.  nextpnr's routed SDF charges every pip one number,
getPipDelay() in xilinx/arch.h:  the pip's SLOW_MAX intrinsic plus
(src_len * R_srcwire + R_pip) * C_pip, where src_len is a Manhattan GUESS of
the upstream wire's length and C_pip is the pip's OWN input capacitance, not
what it drives.  No fanout loading, no site-pin delays, no fast corner, LUT
route-throughs a flat 300 ps and every site pip 25 ps.

WHAT THIS DOES INSTEAD.  For every routed net it rebuilds the RC tree the
route actually forms, from prjxray-db (tile_type_*.json: per-pip intrinsic
delay at four corners, pip drive R and input C, per-tile-wire R and C, per
site-pin delay and R/C), and evaluates it with prjxray's own Elmore model,
prjxray/timing.py (Outpin / Wire / Buffer / PassTransistor / Inpin).  The
tree is built the way prjxray's reference user of that model,
utils/create_timing_worksheet_db.py, builds it (which is the code whose output
prjxray compared against Vivado: +/-1.5% except clock nets,
minitests/timing/README.md):
  - a WIRE is a prjxray NODE, its R and C the sum over the node's tile wires
    (LV nodes: only two tile wires' RC, the worksheet's workaround);
  - a buffered pip is a Buffer(R = pip res, C = pip in_cap), a pass-transistor
    pip a PassTransistor(R = pip res);
  - the root is the site OUTPUT pin (Outpin: drive R, pin delay), each leaf a
    site INPUT pin (Inpin: pin C, pin delay);
  - a sink's delay is the sum, along its path, of every element's intrinsic
    delay (per corner) plus every element's RC (Elmore) term.
The Elmore terms see the whole downstream subtree, so the same pip costs more
on a net with more fanout: that is the loading nextpnr does not model.

UNITS.  prjxray-db stores R in ohms and C in fF; prjxray/tile.py divides both
by 1e3, so R*C is in ns, the same unit as the intrinsic delays.  Everything is
summed in ns and written in ps.

CORNERS.  prjxray-db's 4-tuples are [FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX]
(fuzzers/074-dump_all/get_speed_model.tcl writes them in that order;
prjxray/timing.py fast_slow_tuple_to_corners reads them so), for speed grade
-1 (settings/zynq7.sh: xc7z020clg484-1; the board is xc7z010clg400-1, same
fabric and grade).  These are Vivado SIGN-OFF bounds, not one chip's delay.
The SDF written here carries, per arc,
        (FAST_MIN : SLOW_MIN : SLOW_MAX)        in ps,
so "min" is the fast-corner minimum, "max" the slow-corner maximum, and "typ"
is NOT a typical value -- it is the slow-corner minimum, the only other
well-defined column.  The RC term has one value (prjxray has one R and one C
per element) and is added to every column.  --arcs writes all four columns.
prjxray has no rise/fall split for routing or for cell arcs (the two
parenthesised groups in timings/*.sdf are FAST and SLOW, not rise and fall --
fuzzers/007-timing/bel's sdfwrite emits 'fast' then 'slow'; nextpnr's
parse_sdf.py reads them as rising/falling, which is why nextpnr's cell arcs
are the slow-corner max).  So rise and fall are written equal.

CELL ARCS come from prjxray-db timings/<TILE_TYPE>.sdf by site type and bel
(LUT6/LUT5 per <SITE>/<bel>, SELMUX2_1 per F7AMUX/F7BMUX/F8MUX, FF_INIT CLK->Q,
CARRY4, BUFGCTRL, DSP48E1 by its register configuration).  An arc the
database does not have keeps nextpnr's number (scaled into all three
columns) and is counted.

SITE-INTERNAL PIPS.  prjxray models the slice output mux as the tile pseudo-
pip  X ->> XMUX  (e.g. CLBLL_L_C->>CLBLL_L_CMUX, 166..205 ps).  It is charged
when the route takes an xOUTMUX from the 6-LUT's O6 (or DOUTMUX from COUT),
since the LUT6 cell arc ends at O6.  An O5 or CARRY4 output through the OUTMUX
is charged 0: the database's LUT5/CARRY4 arcs are the arcs to the site pin
and there is no separate pseudo-pip for them.  Every other site pip (FFMUX,
CY0, CLKINV, CEUSEDMUX, SRUSEDMUX, ...) is 0 -- the FF/CARRY timing checks and
arcs include them in Vivado's model.  This is the weakest modelling choice in
the file; --sitepip-ps overrides it with a flat number for a sensitivity run.

WHAT IT KEEPS FROM nextpnr.  The SDF's structure, instance names, SETUPHOLD
checks and every arc list: the input SDF is the template and only numbers are
replaced, so cells/gls/gen.py reads the output exactly as it reads nextpnr's
(set GLS_SDF_FIELD=min|typ|max to pick a column; gen.py's default reads min).

NAME MAPPING (the crux).  nextpnr-xilinx names a routing wire after the FIRST
tile wire of its node in the chipdb, and bbaexport.py lists a node's INT-tile
wires first, so INT_R_X19Y46/SS2A0 is the node {INT_R_X19Y47/SS2BEG0,
INT_R_X19Y46/SS2A0, INT_R_X19Y45/SS2END0}.  A pip is named
'<src node name>-><dst node name>' with no tile; it is resolved by finding the
tile, among those both nodes touch, whose tile type has a pip between a tile
wire of each (prjxray node model from tileconn.json, db.node_model()).  Site
pins appear as pips  TILE/wire->SITEWIRE/...  and  SITEWIRE/...->TILE/wire;
the tile wire is the site pin's wire.  Every failure to resolve is counted and
the arc keeps nextpnr's number; the run fails if any routed tile pip does not
resolve.
"""
import argparse
import collections
import json
import math
import os
import re
import sys
import time

from prjxray.db import Database
from prjxray.timing import (Outpin, Inpin, Wire, Buffer, PassTransistor,
                            RcElement, PvtCorner)
from prjxray.tile import OutPinTiming, InPinTiming

FAST, SLOW = PvtCorner.FAST, PvtCorner.SLOW
COLS = ("FAST_MIN", "FAST_MAX", "SLOW_MIN", "SLOW_MAX")
ZERO4 = (0.0, 0.0, 0.0, 0.0)

DB_ROOT = os.environ.get("XRAY_DB", "/root/dev2/lib/xray/prjxray-db/zynq7")
PART = os.environ.get("XRAY_PART", "xc7z010clg400-1")
NEGCTL = os.environ.get("XRAY_NEGCTL_WRONG_PIP", "0") == "1"


class FloatMath(object):
    """prjxray/math_models.py's PythonMathModel is declared with `def`, not
    `class` (`def PythonMathModel(object):`), so it cannot be instantiated;
    this is the five-method equivalent it was meant to be."""
    def sum(self, elems):
        return sum(elems)

    def plus(self, a, b):
        return a + b

    def divide(self, a, b):
        return a / b

    def multiply(self, a, b):
        return a * b

    def eval(self, e):
        return e


MATH = FloatMath()


def d4(delays):
    """prjxray corner dict (or None) -> (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX)."""
    if delays is None:
        return ZERO4
    return (delays[FAST].min, delays[FAST].max, delays[SLOW].min, delays[SLOW].max)


def add4(a, b):
    return tuple(x + y for x, y in zip(a, b))


# ----------------------------------------------------------------- database

class XrayDb(object):
    def __init__(self, db_root=DB_ROOT, part=PART, log=sys.stderr):
        t0 = time.time()
        self.db = Database(db_root, part)
        self.grid = self.db.grid()
        self.tt_cache = {}
        self.pipmap_cache = {}
        self.sitepin_cache = {}
        log.write("xray_delay: building prjxray node model (tileconn) ...\n")
        nm = self.db.node_model()
        nm._build_wire_to_node_map()
        self.nodes = nm.nodes                    # node name -> [(tile, wire)]
        self.w2n = nm.wire_to_node_map           # (tile, wire) -> node name
        log.write("xray_delay: %d nodes in %.0f s\n" % (len(self.nodes), time.time() - t0))
        self.timing_dir = os.path.join(db_root, "timings")

    def tile_type(self, tile):
        return self.grid.gridinfo_at_tilename(tile).tile_type

    def tt(self, tile_type):
        if tile_type not in self.tt_cache:
            self.tt_cache[tile_type] = self.db.get_tile_type(tile_type)
        return self.tt_cache[tile_type]

    def pipmap(self, tile_type):
        """(src wire, dst wire) -> (Pip, backward?) for one tile type."""
        if tile_type not in self.pipmap_cache:
            m = {}
            for p in self.tt(tile_type).get_pips():
                m[(p.net_from, p.net_to)] = (p, False)
                if not p.is_directional:
                    m.setdefault((p.net_to, p.net_from), (p, True))
            self.pipmap_cache[tile_type] = m
        return self.pipmap_cache[tile_type]

    def site_pin(self, tile, wire):
        """The site pin whose tile wire is `wire` in `tile`, or None."""
        tt = self.tile_type(tile)
        key = (tt, wire)
        if key not in self.sitepin_cache:
            found = None
            for s in self.tt(tt).get_sites():
                for sp in s.site_pins:
                    if sp.wire == wire:
                        found = sp
            self.sitepin_cache[key] = found
        return self.sitepin_cache[key]

    def site_pin_wires(self, tile, site):
        """site pin name -> tile wire, for one site instance."""
        key = (tile, site)
        if key not in self.sitepin_cache:
            gi = self.grid.gridinfo_at_tilename(tile)
            m = {}
            for s in self.tt(gi.tile_type).get_instance_sites(gi):
                if s.name == site:
                    m = {sp.name: sp.wire for sp in s.site_pins}
            self.sitepin_cache[key] = m
        return self.sitepin_cache[key]

    def node_of(self, tile, wire):
        return self.w2n.get((tile, wire))

    def node_rc(self, node):
        """RcElements of a node: every tile wire's R/C (prjxray/tile.py units).
        LV nodes: the worksheet keeps only the first two wires' RC because
        part of it is lumped into the LV switch timing; prjxray's node order is
        a set, so take two of the (identical, 2.8 ohm / 13 fF) LV wires."""
        wires = self.nodes[node]
        out = []
        is_lv = any(w.startswith("LV") for _, w in wires)
        for t, w in wires:
            rc = self.tt(self.tile_type(t)).get_wires().get(w)
            if rc is None or (rc.resistance == 0 and rc.capacitance == 0):
                continue
            out.append(rc)
        if is_lv:
            out = out[:2]
        return out

    def resolve_pip(self, src_node, dst_node):
        """-> (tile, Pip, backward) for the tile pip joining two nodes."""
        dst_by_tile = collections.defaultdict(list)
        for t, w in self.nodes[dst_node]:
            dst_by_tile[t].append(w)
        hits = []
        for t, ws in self.nodes[src_node]:
            if t not in dst_by_tile:
                continue
            pm = self.pipmap(self.tile_type(t))
            for wd in dst_by_tile[t]:
                hit = pm.get((ws, wd))
                if hit:
                    hits.append((t, hit[0], hit[1]))
        if not hits:
            return None
        # prefer a forward, non-pseudo pip if there is a choice
        hits.sort(key=lambda h: (h[2], h[1].is_pseudo))
        if NEGCTL:
            # negative control: a WRONG pip -- another pip of the same tile
            # leaving the same source wire.  The nextpnr-emulation match
            # (nextpnr_emulated_ps == nextpnr_ps) must collapse under it.
            t, p, b = hits[0]
            alts = [q for q in self.tt(self.tile_type(t)).get_pips()
                    if q.net_from == p.net_from and q.name != p.name and not q.is_pseudo]
            if alts:
                return t, alts[hash(p.name) % len(alts)], False
        return hits[0]


# --------------------------------------------------------------- cell arcs

RE_CELL = re.compile(r'\(CELL\s*\(CELLTYPE "([^"]*)"\)\s*\(INSTANCE\s*([^)]*)\)')
RE_IOP = re.compile(r'\(IOPATH\s+(\(\w+\s+)?(\S+?)\)?\s+(\S+)\s+\(([-\d.]*):[-\d.]*:([-\d.]*)\)\s*\(([-\d.]*):[-\d.]*:([-\d.]*)\)')


def read_timing_sdf(path):
    """prjxray-db timings/*.sdf -> {(celltype, instance): {(from, to): 4-tuple ns}}.
    Each IOPATH there is (FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)."""
    out = {}
    cur = None
    for line in open(path):
        m = RE_CELL.search(line)
        if m:
            cur = out.setdefault((m.group(1), m.group(2).strip()), {})
            continue
        if "(CELLTYPE" in line:
            ct = re.search(r'"([^"]*)"', line).group(1)
            cur = None
            pend = ct
            continue
        if "(INSTANCE" in line and cur is None:
            inst = re.search(r"\(INSTANCE\s*([^)]*)\)", line).group(1).strip()
            cur = out.setdefault((pend, inst), {})
            continue
        m = RE_IOP.search(line)
        if m and cur is not None:
            f = lambda s: float(s) if s else 0.0
            cur[(m.group(2), m.group(3))] = (f(m.group(4)), f(m.group(5)),
                                             f(m.group(6)), f(m.group(7)))
    return out


class CellArcs(object):
    def __init__(self, xdb):
        self.xdb = xdb
        self.cache = {}

    def sdf(self, tile_type):
        if tile_type not in self.cache:
            p = os.path.join(self.xdb.timing_dir, tile_type + ".sdf")
            self.cache[tile_type] = read_timing_sdf(p) if os.path.exists(p) else {}
        return self.cache[tile_type]

    def site_info(self, site):
        """site name -> (tile, tile_type, site_type)."""
        if not hasattr(self, "_site"):
            self._site = {}
            for tile in self.xdb.grid.tiles():
                gi = self.xdb.grid.gridinfo_at_tilename(tile)
                for s, st in gi.sites.items():
                    self._site[s] = (tile, gi.tile_type, st)
        return self._site.get(site)

    def lookup(self, ctype, bel, attrs, params, a, z):
        """-> 4-tuple ns or None."""
        if "/" not in bel:
            return None
        site, b = bel.split("/")[:2]
        si = self.site_info(site)
        if si is None:
            return None
        tile, tt, st = si
        S = self.sdf(tt)
        if ctype == "SLICE_LUTX":
            # a SLICEM's LUTs are filed under LUT_OR_MEM{5,6}LRAM (the
            # combinational A->O arcs are the same numbers as SLICEL's LUT6/5)
            n = "6" if b.endswith("6LUT") else "5"
            for ct in ("LUT" + n, "LUT_OR_MEM%sLRAM" % n):
                arcs = S.get((ct, "%s/%s" % (st, b)))
                if arcs and (a, z) in arcs:
                    return arcs[(a, z)]
            return None
        if ctype == "SELMUX2_1":
            arcs = S.get(("SELMUX2_1", "%s/%s" % (st, b)))
            return arcs.get((a, z)) if arcs else None
        if ctype == "SLICE_FFX":
            if (a, z) == ("CK", "Q"):
                arcs = S.get(("FF_INIT", st)) or {}
                return arcs.get(("CLK", "Q"))
            return None
        if ctype == "CARRY4":
            arcs = S.get(("CARRY4", st)) or {}
            r = arcs.get((a, z))
            if r is None and a.startswith("DI"):
                for v in ("CARRY4_AX", "CARRY4_BX", "CARRY4_CX", "CARRY4_DX"):
                    r = (S.get((v, st)) or {}).get((a, z))
                    if r:
                        break
            return r
        if ctype == "BUFGCTRL":
            arcs = S.get(("BUFGCTRL", "BUFGCTRL")) or {}
            return arcs.get(("I" if a.startswith("I") else a, z))
        if ctype == "DSP48E1_DSP48E1":
            return self.dsp(S, params, a, z)
        return None

    def dsp(self, S, params, a, z):
        """Combinational DSP48E1 (all *REG=0, USE_MULT=MULTIPLY): pick the
        timings/DSP_*.sdf cell whose name encodes that configuration and take
        the group arc (the SDF there is per bus, e.g. A -> P)."""
        g_in = re.sub(r"\d+$", "", a)
        g_out = re.sub(r"\d+$", "", z)
        a_in = params.get("A_INPUT", "DIRECT")
        b_in = params.get("B_INPUT", "DIRECT")
        best = None
        for (ct, inst), arcs in S.items():
            if not ct.startswith("DSP48E1"):
                continue
            # combinational configuration only: no register stage, no D port,
            # static multiply (gen.py/dsp_config refuses anything else)
            if re.search(r"REG_[12]", ct) or "USE_DPORT_TRUE" in ct or \
                    "USE_MULT_DYNAMIC" in ct or "USE_MULT_NONE" in ct:
                continue
            if "A_INPUT" in ct and ("A_INPUT_" + a_in) not in ct:
                continue
            if "B_INPUT" in ct and ("B_INPUT_" + b_in) not in ct:
                continue
            for (f, t), v in arcs.items():
                f0, t0 = re.sub(r"\[.*\]|\d+$", "", f), re.sub(r"\[.*\]|\d+$", "", t)
                if f0 == g_in and t0 == g_out:
                    if best is None or v[3] > best[3]:
                        best = v
        return best


# --------------------------------------------------------------- the route

def parse_routing(r):
    f = r.split(";")
    return {f[i]: f[i + 1] for i in range(0, len(f) - 2, 3)}


def pip_parent(pip):
    """nextpnr pip name -> its source wire name (None for a SITEPIP, whose
    source is SITEWIRE/<site>/<last component>)."""
    if pip.startswith("SITEPIP/"):
        _, site, bel, src = pip.split("/", 3)
        return "SITEWIRE/%s/%s" % (site, src)
    return pip.split("->")[0]


OUTMUX_PSEUDO = re.compile(r"^([A-D])OUTMUX$")


class NetTiming(object):
    """The prjxray RC tree of one routed net, and per site wire the elements
    reaching it."""

    def __init__(self, xdb, par, sitepip_ps, stats):
        self.xdb = xdb
        self.par = par
        self.stats = stats
        self.sitepip_ps = sitepip_ps
        self.children = collections.defaultdict(list)
        root = None
        for w, p in par.items():
            if p == "":
                root = w if root is None else root
            else:
                self.children[pip_parent(p)].append(w)
        self.root = root
        self.outpins = []
        # per nextpnr wire: ('rc', Inpin-or-None, site_extra 4-tuple, info)
        self.arrive = {}
        self.unresolved = 0
        self.global_net = False
        self.npips = {}
        # nextpnr's own getPipDelay() re-derived from the pip each element
        # resolved to (see npr_pip_ps) -- a cross-check of the name mapping
        self.npcost = {}
        if root is not None:
            self.walk_site(root, ZERO4, (0, 0, 0))
            for op in self.outpins:
                op.propigate_delays(MATH)

    # -- site-internal part (root side and sink side)
    def sitepip_delay(self, pip):
        """Delay of one site pip (see the module docstring)."""
        _, site, bel, src = pip.split("/", 3)
        if self.sitepip_ps is not None:
            return (self.sitepip_ps / 1000.0,) * 4
        m = OUTMUX_PSEUDO.match(bel)
        if m and (src.endswith("6LUT_O6") or src == "CARRY4_COUT"):
            L = m.group(1)
            info = CELLARCS.site_info(site)
            if info is None:
                return ZERO4
            tile, tt, st = info
            pins = self.xdb.site_pin_wires(tile, site)
            srcpin = pins.get("COUT" if src == "CARRY4_COUT" else L)
            hit = self.xdb.pipmap(tt).get((srcpin, pins.get(L + "MUX")))
            if hit and hit[0].timing is not None:
                self.stats["sitepip_outmux_charged"] += 1
                return d4(hit[0].timing.delays)
            self.stats["sitepip_outmux_nopseudo"] += 1
        return ZERO4

    def walk_site(self, w, extra, npips):
        """w is a SITEWIRE on the source side (before any tile routing)."""
        self.arrive[w] = (None, extra, npips)
        for c in self.children.get(w, ()):
            p = self.par[c]
            self.npcost[c] = 25
            if p.startswith("SITEPIP/"):
                self.walk_site(c, add4(extra, self.sitepip_delay(p)), (npips[0], npips[1], npips[2] + 1))
            elif c.startswith("SITEWIRE/"):
                self.walk_site(c, extra, npips)           # site wire alias
            else:
                # site output pin: SITEWIRE/... -> TILE/wire
                tile, wire = c.split("/", 1)
                sp = self.xdb.site_pin(tile, wire)
                node = self.xdb.node_of(tile, wire)
                if sp is None or not isinstance(sp.timing, OutPinTiming) or node is None:
                    self.stats["outpin_unresolved"] += 1
                    self.unresolved += 1
                    continue
                op = Outpin(resistance=sp.timing.drive_resistance,
                            delays=sp.timing.delays)
                op.extra = extra
                rcw = Wire(rc_elements=self.xdb.node_rc(node), math=MATH)
                op.set_sink_wire(rcw)
                self.outpins.append(op)
                self.walk_tile(c, node, rcw, op, extra, npips, first=True)

    def walk_tile(self, w, node, rcw, upstream, extra, npips, first=False):
        """w is a tile wire (nextpnr node name) in prjxray node `node`, whose
        RC Wire is rcw."""
        self.arrive[w] = ("tile", extra, npips)
        for c in self.children.get(w, ()):
            p = self.par[c]
            self.npcost[c] = 25
            if c.startswith("SITEWIRE/"):
                # site input pin: TILE/wire -> SITEWIRE/...
                tile, wire = w.split("/", 1)
                sp = self.xdb.site_pin(tile, wire)
                if sp is None or not isinstance(sp.timing, InPinTiming):
                    self.stats["inpin_unresolved"] += 1
                    self.unresolved += 1
                    continue
                ip = Inpin(capacitance=sp.timing.capacitance, delays=sp.timing.delays,
                           name=c)
                rcw.add_child(ip)
                self.walk_sink_site(c, ip, extra, npips)
                continue
            ctile, cwire = c.split("/", 1)
            cnode = self.xdb.node_of(ctile, cwire)
            if cnode is None:
                self.stats["wire_unresolved"] += 1
                self.unresolved += 1
                continue
            if cnode == node:
                # nextpnr splits a site-pin tile wire off its node; in prjxray
                # they are one node -- no element.
                self.stats["same_node_pip"] += 1
                self.walk_tile(c, node, rcw, upstream, extra, npips)
                continue
            hit = self.xdb.resolve_pip(node, cnode)
            if hit is None:
                self.stats["pip_unresolved"] += 1
                self.unresolved += 1
                self.stats.setdefault("pip_unresolved_examples", []).append(p) \
                    if len(self.stats.get("pip_unresolved_examples", [])) < 10 else None
                continue
            tile, pip, backward = hit
            tim = pip.backward_timing if backward else pip.timing
            self.npcost[c] = self.npr_pip_ps(tile, pip, backward, tim)
            if any(k in self.xdb.tile_type(tile) for k in ("HCLK", "CLK_", "HROW")) or \
                    "GCLK" in cwire or "GCLK" in pip.name:
                self.global_net = True
            if pip.is_pass_transistor:
                self.stats["pip_pass_transistor"] += 1
                if tim is not None and ((tim.drive_resistance or 0) > 0 or
                                        any(d4(tim.delays))):
                    self.stats["pip_pass_transistor_nonzero"] += 1
                    ex = self.stats.setdefault("pt_nonzero_examples", [])
                    if len(ex) < 5:
                        ex.append(pip.name)
                el = PassTransistor(drive_resistance=(tim.drive_resistance if tim else 0.0),
                                    delays=(tim.delays if tim else None))
            else:
                self.stats["pip_buffer" if not pip.is_pseudo else "pip_pseudo"] += 1
                r = tim.drive_resistance if tim and tim.drive_resistance is not None else 0.0
                if r == 0 and first and not pip.is_pseudo:
                    # create_timing_worksheet_db.py: a zero-R buffer right after
                    # the output pin takes the drive R of a site pin on its node
                    for t2, w2 in self.xdb.nodes[cnode][:1]:
                        sp2 = self.xdb.site_pin(t2, w2)
                        if sp2 is not None and isinstance(sp2.timing, OutPinTiming):
                            r = sp2.timing.drive_resistance
                el = Buffer(internal_capacitance=(tim.internal_capacitance if tim else 0.0) or 0.0,
                            drive_resistance=r, delays=(tim.delays if tim else None))
                if pip.is_pseudo:
                    # a route-through: Vivado charges the site input pin too
                    sp_in = self.xdb.site_pin(tile, pip.net_to if backward else pip.net_from)
                    if sp_in is not None and isinstance(sp_in.timing, InPinTiming):
                        extra = add4(extra, d4(sp_in.timing.delays))
                        self.stats["routethru_inpin_charged"] += 1
            rcw.add_child(el)
            nw = Wire(rc_elements=self.xdb.node_rc(cnode), math=MATH)
            el.set_sink_wire(nw)
            cnt = (npips[0], npips[1] + 1, npips[2]) if pip.is_pass_transistor else \
                (npips[0] + 1, npips[1], npips[2])
            self.walk_tile(c, cnode, nw, el, extra, cnt)

    def walk_sink_site(self, w, inpin, extra, npips):
        self.arrive[w] = (inpin, extra, npips)
        for c in self.children.get(w, ()):
            p = self.par[c]
            self.npcost[c] = 25
            if p.startswith("SITEPIP/"):
                self.walk_sink_site(c, inpin, add4(extra, self.sitepip_delay(p)), (npips[0], npips[1], npips[2] + 1))
            elif c.startswith("SITEWIRE/"):
                self.walk_sink_site(c, inpin, extra, npips)
            else:
                # the net leaves the site again (rare): treat as new tile route
                self.stats["reexit_site"] += 1
                self.arrive[c] = None

    def npr_pip_ps(self, tile, pip, backward, tim):
        """nextpnr-xilinx getPipDelay() (xilinx/arch.h) for a TILE_ROUTING
        pip, from the chipdb numbers bbaexport.py would have stored for this
        prjxray pip: max_delay = int(SLOW_MAX ns * 1000); R, C scaled by 1000;
        the Manhattan src_len term is taken as 1 (no driving_pip_loc here).
        A pseudo pip (LUT route-through) is a flat 300 ps there."""
        if pip.is_pseudo:
            return 300
        d = tim.delays if tim is not None else None
        mx = int(max(d[SLOW].min, d[SLOW].max) * 1000) if d else 0
        r_pip = int((tim.drive_resistance or 0) * 1e3 * 1000) if tim else 0
        c_pip = int((tim.internal_capacitance or 0) * 1e3 * 1000) if tim else 0
        tt = self.xdb.tile_type(tile)
        wires = self.xdb.tt(tt).get_wires()
        src = pip.net_to if backward else pip.net_from
        dst = pip.net_from if backward else pip.net_to
        rs = wires.get(src)
        r_src = int(rs.resistance * 1e3 * 1000) if rs else 0
        v = mx + int(float(r_src + r_pip) * c_pip / 1e9)
        if pip.is_pass_transistor:
            rd = wires.get(dst)
            c_dst = int(rd.capacitance * 1e3 * 1000) if rd else 0
            v += int(float(r_src + r_pip) * c_dst / 1e9)
        return max(v, 35)

    def npr_emulated(self, w):
        tot = 0
        while w in self.par and self.par[w]:
            tot += self.npcost.get(w, 0)
            w = pip_parent(self.par[w])
        return tot

    def delay_to(self, w):
        """-> (4-tuple ns, rc ns, npips, inpin) for the nextpnr wire w."""
        a = self.arrive.get(w)
        if a is None:
            return None
        el, extra, npips = a
        if el is None:
            return extra, 0.0, npips, None, ZERO4
        if el == "tile":
            return None
        tot = ZERO4
        rc = 0.0
        for e in el.get_delays():
            tot = add4(tot, d4(e.get_intrinsic_delays()))
            r = e.get_rc_delay()
            if r is not None:
                rc += r
        tot = add4(tot, extra)
        return tot, rc, npips, el, d4(el.get_intrinsic_delays())


CELLARCS = None


# ----------------------------------------------------- dst pin -> site wire

def sink_wire(cell, port, par, children_of):
    """nextpnr routed-JSON cell + port -> the route wire that is its sink."""
    bel = cell["attributes"].get("NEXTPNR_BEL", "")
    if "/" not in bel:
        return None
    site, b = bel.split("/")[:2]
    pre = "SITEWIRE/%s/" % site
    t = cell["type"]
    cands = []
    if t == "SLICE_LUTX":
        L = b[0]
        k = port[1:]
        # the tile pin the route entered on is the physical pin (lut-perm-sink)
        for w, p in par.items():
            if w.startswith(pre) and re.match(r"^%s[1-6]$" % L, w[len(pre):]) and \
                    "->" in p and re.search(r"_%s%s$" % (L, k), p.split("->")[0]):
                cands.append(w)
        if not cands:
            for w in par:
                if w == pre + L + k:
                    cands.append(w)
        return cands[0] if len(cands) == 1 else None
    names = []
    if t == "SELMUX2_1":
        if port == "S0":
            names = [{"F7AMUX": "AX", "F7BMUX": "CX", "F8MUX": "BX"}[b]]
        else:
            names = {"F7AMUX": ["A6LUT_O6", "B6LUT_O6"], "F7BMUX": ["C6LUT_O6", "D6LUT_O6"],
                     "F8MUX": ["F7AMUX_OUT", "F7BMUX_OUT"]}[b]
    elif t == "SLICE_FFX":
        names = {"CK": ["CLKINV_OUT", "CLK"], "CE": ["CEUSEDMUX_OUT", "CE"],
                 "SR": ["SRUSEDMUX_OUT", "SR"],
                 "D": ["%sFFMUX_OUT" % b[:-2] if b.endswith("FF") else b + "MUX_OUT"]}.get(port, [])
    elif t == "CARRY4":
        if port.startswith("S"):
            names = ["%s6LUT_O6" % "ABCD"[int(port[1])]]
        elif port.startswith("DI"):
            names = ["%sCY0_OUT" % "ABCD"[int(port[2])]]
        elif port == "CIN":
            names = ["CIN"]
        elif port == "CYINIT":
            names = ["PRECYINIT_OUT", "AX", "CYINIT"]
    names += [port + "INV_OUT", port + "USED_OUT", port]
    for n in names:
        if pre + n in par:
            return pre + n
    return None


# ------------------------------------------------------------------- main

RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)\s*\((\d+):(\d+):(\d+)\)\)")
RE_IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)\s*\((\d+):(\d+):(\d+)\)\)")
RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")


def unesc(s):
    return s.replace("\\", "")


def ps(x):
    return int(round(x * 1000.0))


def main():
    global CELLARCS
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--routed", required=True)
    ap.add_argument("--sdf", required=True, help="nextpnr's SDF for the same route (template)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--arcs", help="per-arc TSV: every column, nextpnr's number, flags")
    ap.add_argument("--sitepip-ps", type=float, default=None,
                    help="flat delay for every site pip (sensitivity run); default: see docstring")
    ap.add_argument("--nets", help="comma list: only report these nets (debug)")
    args = ap.parse_args()

    t0 = time.time()
    xdb = XrayDb()
    CELLARCS = CellArcs(xdb)
    top = json.load(open(args.routed))["modules"]["top"]
    cells = top["cells"]
    routes = {}
    netname = {}
    for name, nn in top["netnames"].items():
        r = nn.get("attributes", {}).get("ROUTING")
        if nn["bits"]:
            netname.setdefault(nn["bits"][0], name)
        if r and nn["bits"]:
            routes.setdefault(nn["bits"][0], r)

    stats = collections.Counter()
    nets = {}

    def net(bit):
        if bit not in nets:
            nets[bit] = NetTiming(xdb, parse_routing(routes[bit]), args.sitepip_ps, stats)
        return nets[bit]

    out = []
    arcs_rows = []
    inst = None
    n_ic = n_ic_x = n_io = n_io_x = 0
    for line in open(args.sdf):
        m = RE_IC.search(line)
        if m:
            n_ic += 1
            src, dst = unesc(m.group(1)), unesc(m.group(2))
            npr = int(m.group(3))
            cname, _, port = dst.rpartition("/")
            c = cells.get(cname)
            res = None
            flag = ""
            nname = ""
            if c is not None and port in c["connections"]:
                bit = c["connections"][port][0]
                nname = netname.get(bit, "")
                if bit in routes and not netname.get(bit, "").startswith("$PACKER_"):
                    nt = net(bit)
                    w = sink_wire(c, port, nt.par, nt.children)
                    if w is None:
                        flag = "nosink"
                    else:
                        res = nt.delay_to(w)
                        if res is None:
                            flag = "noarrive"
                        elif nt.global_net:
                            flag = "global"
                else:
                    flag = "const" if bit in routes else "noroute"
            else:
                flag = "nocell"
            if res is None:
                stats["ic_kept_nextpnr_" + flag] += 1
                v4 = (npr / 1000.0,) * 4
                rc = 0.0
                npips = (-1, -1, -1)
                inpin4 = extra4 = ZERO4
                emu = -1
            else:
                n_ic_x += 1
                tot, rc, npips, _, inpin4 = res
                v4 = tuple(x + rc for x in tot)
                extra4 = nt.arrive[w][1]
                emu = nt.npr_emulated(w)
            a, b_, cc = ps(v4[0]), ps(v4[2]), ps(v4[3])
            new = "(INTERCONNECT %s %s (%d:%d:%d) (%d:%d:%d))" % (
                m.group(1), m.group(2), a, b_, cc, a, b_, cc)
            out.append(line[:m.start()] + new + line[m.end():])
            arcs_rows.append(("IC", src, dst, npr) + tuple(ps(x) for x in v4) +
                             (ps(rc), npips[0], flag or "ok", nname, ps(inpin4[3]), ps(extra4[3]), npips[1], npips[2], emu))
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1))
            out.append(line)
            continue
        m = RE_IO.search(line)
        if m and inst in cells:
            n_io += 1
            c = cells[inst]
            a, z = m.group(1), m.group(2)
            npr = int(m.group(3))
            v = CELLARCS.lookup(c["type"], c["attributes"].get("NEXTPNR_BEL", ""),
                                c["attributes"], c.get("parameters", {}), a, z)
            if v is None:
                stats["io_kept_nextpnr_%s" % c["type"]] += 1
                v = (npr / 1000.0,) * 4
                flag = "kept"
            else:
                n_io_x += 1
                flag = "ok"
            x, y, w_ = ps(v[0]), ps(v[2]), ps(v[3])
            new = "(IOPATH %s %s (%d:%d:%d) (%d:%d:%d))" % (a, z, x, y, w_, x, y, w_)
            out.append(line[:m.start()] + new + line[m.end():])
            arcs_rows.append(("IO", inst + "/" + a, inst + "/" + z, npr) +
                             tuple(ps(q) for q in v) + (0, 0, flag, "", 0, 0, 0, 0, -1))
            continue
        out.append(line.replace('(PROGRAM "nextpnr")',
                                '(PROGRAM "xray_delay.py (prjxray-db, FAST_MIN:SLOW_MIN:SLOW_MAX)")'))
    open(args.out, "w").write("".join(out))
    if args.arcs:
        with open(args.arcs, "w") as f:
            f.write("kind\tsrc\tdst\tnextpnr_ps\t%s\trc_ps\tn_bufpip\tflag\tnet\tinpin_smax_ps\tsite_extra_smax_ps\tn_passtr\tn_sitepip\tnextpnr_emulated_ps\n" % "\t".join(c.lower() + "_ps" for c in COLS))
            for r in arcs_rows:
                f.write("\t".join(str(x) for x in r) + "\n")
    unres = sum(n.unresolved for n in nets.values())
    sys.stderr.write("xray_delay: INTERCONNECT %d, %d from prjxray; IOPATH %d, %d from prjxray; "
                     "%d nets, %.0f s\n" % (n_ic, n_ic_x, n_io, n_io_x, len(nets), time.time() - t0))
    for k, v in sorted(stats.items()):
        sys.stderr.write("  %-40s %s\n" % (k, v))
    if stats["pip_unresolved"] or stats["outpin_unresolved"] or stats["inpin_unresolved"] \
            or stats["wire_unresolved"]:
        sys.stderr.write("xray_delay: FAIL -- %d routing element(s) did not resolve against "
                         "prjxray-db; those arcs kept nextpnr's number\n" % unres)
        sys.exit(2)


if __name__ == "__main__":
    main()
