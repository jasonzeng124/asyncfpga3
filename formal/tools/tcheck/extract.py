#!/usr/bin/env python3
"""Probe C-10e front end (UNTRUSTED): routed gcd_hw -> link obligations as 10a race
netlists for the verified checker `tcheck` (lake exe).

    python3 formal/tools/tcheck/extract.py BUILD_DIR TOP --out OBL.tc [--osc dhk ...]

BUILD_DIR holds TOP.sdf, TOP_routed.json, TOP.fasm (cells/hw/build_hw.sh output).

Graph.  The timing graph is the one every project rule walks: tighten.routed_graph
(nextpnr SDF IOPATH + INTERCONNECT arcs, false arcs cut by LUT INIT, storage = LUT
feedback outputs), with --osc instruments cut exactly as tighten.py does.  Each arc
then gets a delay INTERVAL per variant (one variant = one corner model):

  sdf      [d, d]             nextpnr's SDF number (what the rules read)
  sdfband  [.772 d, 1.155 d]   rule E's GUARD_LO/GUARD_HI band on the SDF number
  fast     prjxray fast corner [fast_min, fast_max] (+ Elmore RC, fixed)
  slow     prjxray slow corner [slow_min, slow_max] (+ Elmore RC, fixed)
  fastG    fast x band:  [.772 fast_min, 1.155 fast_max]
  slowG    slow x band:  [.772 slow_min, 1.155 slow_max]

prjxray numbers: a CLB->CLB-LUT-pin INTERCONNECT arc is the routed net from the
driver's site output pin (found by walking the FASM's active pips back from the
sink's physical pin, fasm2lean Extract.walk) to the sink site pin, as an RC tree
of prjxray/timing.py classes over every ON pip (prjxdelay/ringdelay.Net: pips,
site pin, Elmore incl. fanout load).  A LUT IOPATH arc is prjxray-db's LUT6 arc
for the physical pin (slicel/slicem.sdf).  Every other arc (site-internal hops,
CARRY4, MUXF7, FF, IOB, BUFG) has no prjxray number here and FALLS BACK to the
SDF band in every prjxray variant; each instance reports how many of its arcs
fell back.  (Fallback is a stated gap, H_FALLBACK_BAND, not a bound.)

Obligations (per bd_latch controller `ctl`, i.e. per link stage; mirroring the
structure of tighten.py's rules H and I, but timed over ALL paths by the checker):

  I  capture (8e's Sep + latch setup).  Launch: rise of an upstream controller
     `up` that requests `ctl` and whose latch feeds `ctl`'s latch.  Request side
     (must be late): up -> ctl (rise), ctl -> up (ack), up -> ctl (fall), ctl ->
     enable pin -> latch LUT output: the earliest any bit of ctl's bank closes.
     Data side (must be early): up -> up's enable -> up's latch Q -> ... -> ctl's
     latch D pins -> latch LUT output -> its own feedback pin (tighten's loop_wire).
     Storage crossings on the request side are taken as pass-through from the
     input on the path (a C-element fires on its LAST input, so its real firing
     is never earlier: sound for the side that must be late).
  H  hold (8e's Hold).  Launch: fall of `ctl`.  Data side (must be early): ctl ->
     enable pin -> latch LUT output (the bank has closed).  Request side (must be
     late): the earliest disturbance of a D pin of ctl's latch, crossing storage
     nodes (each fires the moment it is reached), as tighten.earliest_disturbance;
     the state-node path is chosen by Dijkstra on the variant's lower bounds
     (UNVERIFIED extractor step, H_EXTRACT_MIN) and emitted as one chain.

Each segment between two state nodes is the sub-DAG of ALL arcs on paths between
them that do not pass through storage (tighten's walk, but all paths kept, so
the checker computes the min/max itself).  Segments are unrolled (node copies per
segment), which makes every instance a DAG; launch = node 0.
"""
import argparse
import heapq
import json
import math
import os
import pathlib
import re
import sys
from collections import defaultdict

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parent.parent.parent
TC = os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain"))
GUARD_LO, GUARD_HI = 0.772, 1.155
VARIANTS = ["sdf", "sdfband", "fast", "slow", "fastG", "slowG"]
INVERTED = [0]      # arcs whose prjxray min > max (hull taken; see intervals)
NO_DRVHOP = bool(os.environ.get("TCHECK_NO_DRVHOP"))   # C-10m: before/after only
HOP_NOL = bool(os.environ.get("TCHECK_HOP_NOL"))       # C-10m: xrc cross-check only


def load_rules(cells_dir):
    sys.path.insert(0, str(HERE.parent / "fasm2lean"))
    sys.path.insert(0, str(HERE.parent / "prjxdelay"))
    sys.path.insert(0, os.path.join(TC, "openxc7-src/prjxray"))
    sys.path.insert(0, str(cells_dir / "verify"))
    sys.path.insert(0, str(cells_dir / "hw"))
    sys.argv = [sys.argv[0]]          # tighten.py parses argv at import
    import tighten                    # noqa: E402
    import ringdelay                  # noqa: E402
    import fasm2lean                  # noqa: E402
    return tighten, ringdelay, fasm2lean


class Prjx:
    """prjxray per-arc 4-corner numbers [fast_min, fast_max, slow_min, slow_max] ps."""

    def __init__(self, R, F, fasm, routed):
        self.R, self.F = R, F
        feats, vecs = F.read_fasm(str(fasm))
        self.fab = F.Fabric(F.DB)
        self.nrev = self._bidir(feats)
        self.ex = F.Extract(self.fab, feats, vecs, {})
        self.arcs = R.lut_arcs(F.DB)
        self.site_at = {}
        for tile, g in self.fab.grid.items():
            if g["type"].startswith("CLB"):
                for s in self.fab.tt(g["type"])["sites"]:
                    self.site_at[self.fab.site_name(tile, s)] = (tile, s)
        j = json.load(open(routed))
        self.cells = list(j["modules"].values())[0]["cells"]
        self.nets = {}
        self.cache = {}
        self.inpin = {}
        self.hops = {}       # C-10h: (src, dst) -> (driver hop, sink hop), 4 corners

    def _bidir(self, feats):
        """C-10h: long lines (LV/LVB) are BIDIRECTIONAL pips in prjxray-db, stored once
        (e.g. INT_R.LVB0<<->>LVB12: src LVB0, dst LVB12, with src_to_dst and dst_to_src
        delays).  A route that drives the line from the other end appears in the FASM as
        TILE.LVB0.LVB12 (dst LVB0, src LVB12), which fasm2lean's Extract does not match,
        so its backward walk found the node "floating".  Before Extract is built, add the
        reverse direction of every bidirectional pip of the tile types that the FASM
        uses that way, with dst_to_src as its delay.  (fasm2lean itself is read-only.)"""
        need = set()
        for f in feats:
            parts = f.split(".")
            if len(parts) == 3 and parts[0] in self.fab.grid:
                need.add(self.fab.ttype(parts[0]))
        n = 0
        for tt in sorted(need):
            j = self.fab.tt(tt)
            add = {}
            for k, p in j["pips"].items():
                if p.get("is_directional") == "0" and p.get("dst_to_src") \
                        and (p["src_wire"], p["dst_wire"]) not in j["_by_name"]:
                    q = dict(p, src_wire=p["dst_wire"], dst_wire=p["src_wire"],
                             src_to_dst=p["dst_to_src"], dst_to_src=p["src_to_dst"])
                    add[k + "#reverse"] = q
            for k, q in add.items():
                j["pips"][k] = q
                j["_by_dst"][q["dst_wire"]].append(q)
                j["_by_name"][(q["dst_wire"], q["src_wire"])] = q
                n += 1
        return n

    def lut(self, inst):
        c = self.cells.get(inst)
        if not c:
            return None
        m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", c["attributes"].get("NEXTPNR_BEL", ""))
        if not m or m.group(1) not in self.site_at:
            return None
        tile, s = self.site_at[m.group(1)]
        return tile, s, m.group(2), m.group(3)

    def mux_tables(self):
        """C-10g: prjxray-db slicel/slicem.sdf SELMUX2_1 cell arcs (F7AMUX, F7BMUX,
        F8MUX: pins 0, 1, S0 -> OUT) and the ROUTING_BEL site-internal hop
        (a6lut|b6lut|c6lut|d6lut -> f7amux|f7bmux), as 4-corner ns lists."""
        if hasattr(self, "_mux"):
            return self._mux
        self._mux, self._rbel = {}, {}
        num = r"\(([\d.]*)::([\d.]*)\)\(([\d.]*)::([\d.]*)\)"
        for st in ("slicel", "slicem"):
            ct = inst = None
            for line in open(os.path.join(self.F.DB, "timings", st + ".sdf")):
                m = re.search(r"\(CELLTYPE \"(\S+)\"\)", line)
                if m:
                    ct = m.group(1)
                m = re.search(r"\(INSTANCE\s+\S+/(F[78][AB]?MUX)\)", line)
                if m:
                    inst = m.group(1)
                elif "(INSTANCE" in line:
                    inst = None
                if inst is None:
                    continue
                m = re.search(r"\(IOPATH\s+(\S+)\s+OUT\s+" + num, line)
                if m and ct == "SELMUX2_1":
                    self._mux[(st, inst, m.group(1))] = [float(x) for x in m.groups()[1:]]
                m = re.search(r"\(INTERCONNECT\s+([a-d])6lut\s+f7[ab]mux\s+" + num, line)
                if m and ct == "ROUTING_BEL":
                    self._rbel[(st, inst, m.group(1).upper())] = [float(x) for x in m.groups()[1:]]
        return self._mux

    def site_tables(self):
        """C-10h: every ROUTING_BEL INTERCONNECT (site-internal hop) and every CARRY4*
        IOPATH of prjxray-db slicel/slicem.sdf, as 4-corner ps lists.  Keys:
          hop[(sitetype, from, to)]  (to of an *L instance, e.g. amuxl/affl, folded
                                       onto amux/aff: the HULL over both, since which
                                       one a site uses is not decoded here)
          c4[(sitetype, from, to)]   (hull over every CARRY4* celltype: CARRY4,
                                       CARRY4_AX.., _O5, _LFF, _LBOTH: the DI source and
                                       output-load variants are not decoded either)"""
        if hasattr(self, "_hop"):
            return self._hop, self._c4
        self._hop, self._c4 = {}, {}
        num = r"\(([\d.]*)::([\d.]*)\)\(([\d.]*)::([\d.]*)\)"

        def hull(tab, k, v):
            if k in tab:
                o = tab[k]
                v = [min(o[0], v[0]), max(o[1], v[1]), min(o[2], v[2]), max(o[3], v[3])]
            tab[k] = v
        for st in ("slicel", "slicem"):
            txt = open(os.path.join(self.F.DB, "timings", st + ".sdf")).read()
            for cell in re.findall(r"\(CELL\s*(.*?)\n    \)", txt, re.S):
                ct = re.search(r'CELLTYPE "(\S+)"', cell).group(1)
                for kind, a, b, *ns in re.findall(r"\((IOPATH|INTERCONNECT)\s+(\S+)\s+(\S+)\s+" + num, cell):
                    v = [float(x) * 1e3 for x in ns]
                    if ct == "ROUTING_BEL" and kind == "INTERCONNECT":
                        if HOP_NOL and re.match(r"^[a-d](mux|5?ff)l$", b):
                            # C-10m: cross-check only (TCHECK_HOP_NOL=1): the plain AMUX..DMUX
                            # entry alone, as the auditor's xrc.py reads it; never a verdict
                            continue
                        bb = b[:-1] if re.match(r"^[a-d](mux|5?ff)l$", b) else b
                        hull(self._hop, (st, a, bb), v)
                    elif ct.startswith("CARRY4") and kind == "IOPATH":
                        hull(self._c4, (st, a, b), v)
        return self._hop, self._c4

    def site(self, inst):
        """-> (tile, site json, bel name) for a placed SLICE cell, or None."""
        c = self.cells.get(inst)
        m = c and re.match(r"(SLICE_X\d+Y\d+)/(\w+)$", c["attributes"].get("NEXTPNR_BEL", ""))
        if not m or m.group(1) not in self.site_at:
            return None
        tile, s = self.site_at[m.group(1)]
        return tile, s, m.group(2)

    def drv_bel(self, si, sp):
        """The site-internal source name prjxray uses for a cell output (a6lut, a5lut,
        carry4_o0, carry4_co3, f7amux, f8mux), or None."""
        S = self.site(si)
        if not S:
            return None
        b = S[2]
        if re.match(r"^[A-D][56]LUT$", b):
            return b.lower()
        if b == "CARRY4" and re.match(r"^C?O[0-3]$", sp):
            return "carry4_" + sp.lower()
        if re.match(r"^F[78][AB]?MUX$", b) or re.match(r"^[A-D]5?FF$", b):
            return b.lower()
        return None

    def bel(self, inst):
        c = self.cells.get(inst)
        m = c and re.match(r"(SLICE_X\d+Y\d+)/(\w+)$", c["attributes"].get("NEXTPNR_BEL", ""))
        if not m or m.group(1) not in self.site_at:
            return None
        return self.site_at[m.group(1)][1]["type"].lower(), m.group(2)

    def mux_arc(self, src, dst):
        """SELMUX2_1 cell arc, or the LUT O6 -> F7 mux site-internal hop, or None."""
        si, sp = src.rsplit("/", 1)
        di, dp = dst.rsplit("/", 1)
        B = self.bel(di)
        if not B or not re.match(r"F[78][AB]?MUX$", B[1]):
            return None
        tab = self.mux_tables()
        if si == di and dp == "OUT":
            v = tab.get((B[0], B[1], sp))
            return [x * 1e3 for x in v] if v else None
        Bs = self.bel(si)
        if Bs and sp == "O6" and re.match(r"[A-D]6LUT$", Bs[1]):
            v = self._rbel.get((B[0], B[1], Bs[1][0]))
            return [x * 1e3 for x in v] if v else None
        return None

    def iopath(self, src, dst):
        si, sp = src.rsplit("/", 1)
        di, dp = dst.rsplit("/", 1)
        if dp == "OUT":
            return self.mux_arc(src, dst)
        S = self.site(di)
        if S and S[2] == "CARRY4" and si == di:      # C-10h: CARRY4 cell arcs
            _hop, c4 = self.site_tables()
            v = c4.get((S[1]["type"].lower(), sp, dp))
            return list(v) if v else None
        L = self.lut(si)
        if si != di or not L or not re.match(r"A[1-6]$", sp) or dp not in ("O6", "O5"):
            return None
        tile, s, letter, k = L
        v = self.arcs.get((s["type"].lower(), dp, sp))
        return [x * 1e3 for x in v] if v else None

    def interconnect(self, src, dst):
        key = (src, dst)
        if key in self.cache:
            return self.cache[key]
        self.cache[key] = r = self._ic(src, dst)
        return r

    def _ic(self, src, dst):
        di, dp = dst.rsplit("/", 1)
        si, _sp = src.rsplit("/", 1)
        if dp in ("0", "1"):
            return self.mux_arc(src, dst)
        hop, _c4 = self.site_tables()
        sink_hop = None              # C-10h: site-internal hop after the site input pin
        L = self.lut(di)
        if L and re.match(r"A[1-6]$", dp):
            tile, s, letter, _k = L
            sp_name = letter + dp[1]
        else:
            S = self.site(di)
            if not S:
                return None
            tile, s, b = S
            st = s["type"].lower()
            SS = self.site(si)
            same = SS is not None and SS[0] == tile and SS[1]["x_coord"] == s["x_coord"]
            if re.match(r"^F7AMUX|F7BMUX|F8MUX$", b) and dp == "S0":
                # the select of a wide mux enters through AX / CX / BX (no db hop)
                sp_name = {"F7AMUX": "AX", "F7BMUX": "CX", "F8MUX": "BX"}[b]
            elif b == "CARRY4" and re.match(r"^(DI|S)[0-3]$", dp):
                x = "abcd"[int(dp[-1])]
                db_ = self.drv_bel(si, _sp)
                if same and db_ and re.match(r"^[a-d][56]lut$", db_):
                    # LUT O6 -> S#, LUT O5 -> DI#: a site-internal hop only
                    v = hop.get((st, db_, "carry4"))
                    if v is None or db_[0] != x:
                        return None
                    return list(v)
                if dp.startswith("S"):
                    return None
                sp_name, sink_hop = x.upper() + "X", hop.get((st, x + "x", "di" + dp[-1]))
                if sink_hop is None:
                    return None
            else:
                return None
        if sp_name not in s["site_pins"]:
            return None
        wire = s["site_pins"][sp_name]["wire"]
        try:
            res, _pips = self.ex.walk(tile, wire, dst)
        except SystemExit:
            return None
        if not res or res[0] != "slice":
            return None
        _, ptile, psite, ppin = res
        # the walk must end at the driver cell's site
        SL = self.lut(si)
        if SL and (SL[0] != ptile or SL[1]["x_coord"] != psite["x_coord"]):
            return None
        k = (ptile, psite["type"], psite["x_coord"], ppin)
        if k not in self.nets:
            try:
                self.nets[k] = self.R.Net(self.fab, self.ex, ptile, psite["site_pins"][ppin]["wire"],
                                          psite["site_pins"][ppin])
            except (SystemExit, AssertionError, KeyError):
                self.nets[k] = None
        n = self.nets[k]
        if n is None:
            return None
        self.inpin[(src, dst)] = n.inpins.get((tile, wire))
        r = n.sink(tile, wire)
        if not r:
            return None
        # C-10h: the site-internal hop from the driving BEL to its site output pin
        # (a5lut -> amux, carry4_o0 -> amux, f7amux -> amux, ...; a6lut -> a is 0).
        # 10e/10g left it out, which was optimistic for every non-O6 driver.
        db_ = self.drv_bel(si, _sp)
        if db_ is None:
            return None
        if NO_DRVHOP and db_.endswith("lut"):
            # C-10m: TCHECK_NO_DRVHOP=1 reproduces the C-10e/10g model (no OUTMUX hop on
            # LUT outputs) for before/after tables only; never a verdict
            dh = [0.0, 0.0, 0.0, 0.0]
        elif ppin.lower() == db_[0] and db_.endswith("6lut"):
            dh = [0.0, 0.0, 0.0, 0.0]
        else:
            dh = hop.get((psite["type"].lower(), db_, ppin.lower()))
            if dh is None:
                return None
        sh = sink_hop if sink_hop is not None else [0.0, 0.0, 0.0, 0.0]
        self.hops[(src, dst)] = (dh, sh)
        return [a + b + c for a, b, c in zip(r[0], dh, sh)]

    def split(self, src, dst_a, dst_b):
        """C-10g, rule J: the EXACT shared part of one routed net.  The two sinks'
        RC-tree element lists (Outpin, wires, pips, Inpin; ringdelay.Net) share a
        prefix by identity; the Elmore term of an element (R x downstream C) and its
        intrinsic delay are the same number in both sinks' sums, so the 4-corner delay
        to the branch point is the prefix sum.  -> (shared, suffix_a, suffix_b), each
        [fast_min, fast_max, slow_min, slow_max] ps, or None."""
        if self.interconnect(src, dst_a) is None or self.interconnect(src, dst_b) is None:
            return None
        ia, ib = self.inpin.get((src, dst_a)), self.inpin.get((src, dst_b))
        if ia is None or ib is None:
            return None
        ea, eb = ia.get_delays(), ib.get_delays()
        n = 0
        while n < min(len(ea), len(eb)) and ea[n] is eb[n]:
            n += 1
        R = self.R

        def tot(els):
            rc = sum(e.get_rc_delay() or 0.0 for e in els) * 1e3
            return [sum(R.pick(e.get_intrinsic_delays(), k) for e in els) * 1e3 + rc for k in range(4)]
        (dh, sha), (_dh, shb) = self.hops[(src, dst_a)], self.hops[(src, dst_b)]
        add = lambda x, y: [a + b for a, b in zip(x, y)]  # noqa: E731
        if n == 0:
            # C-10m: no common element.  This happens when the two sinks leave the slice
            # through DIFFERENT output pins of the same LUT (O6 direct on A..D and through
            # the OUTMUX on AMUX..DMUX: two routed nets, two Net objects).  The branch point
            # is the LUT output itself: nothing is shared, and each side carries its OWN
            # driver hop (C-10h took sink a's hop as shared, which credited the OUTMUX hop
            # to the side that does not have it and dropped it from the side that does).
            return [0.0] * 4, add(add(tot(ea), dh), sha), add(add(tot(eb), _dh), shb)
        assert dh == _dh, (src, dst_a, dst_b)
        # C-10h: the driver's site-internal hop is shared, each sink hop is its own
        return add(tot(ea[:n]), dh), add(tot(ea[n:]), sha), add(tot(eb[n:]), shb)


def intervals(d, c):
    """{variant: (lo, hi)} from the SDF number d and the prjxray 4-tuple c (or None)."""
    band = (int(math.floor(GUARD_LO * d)), int(math.ceil(GUARD_HI * d)))
    out = {"sdf": (d, d), "sdfband": band}
    if c is None:
        for v in ("fast", "slow", "fastG", "slowG"):
            out[v] = band
    else:
        fm, fM, sm, sM = c
        # C-10g: a few prjxray-db pips carry min > max within one corner (seen: fast
        # 733 > 721 ps after Elmore).  Take the hull of the two numbers (wider, so a
        # bound if either is) and count it.
        if fm > fM or sm > sM:
            INVERTED[0] += 1
            fm, fM, sm, sM = min(fm, fM), max(fm, fM), min(sm, sM), max(sm, sM)
        out["fast"] = (int(math.floor(fm)), int(math.ceil(fM)))
        out["slow"] = (int(math.floor(sm)), int(math.ceil(sM)))
        out["fastG"] = (int(math.floor(GUARD_LO * fm)), int(math.ceil(GUARD_HI * fM)))
        out["slowG"] = (int(math.floor(GUARD_LO * sm)), int(math.ceil(GUARD_HI * sM)))
    return out


class _Excl:
    """An excluded-arc set plus a destination predicate (arcs whose destination is
    outside are excluded too), usable wherever `segment` tests `(p, d) in excl`."""

    def __init__(self, base, inside):
        self.base, self.inside = base, inside

    def __contains__(self, arc):
        return arc in self.base or not self.inside(arc[1])


class Inst:
    """One unrolled race netlist (node keys -> Nat after a topological sort)."""

    def __init__(self, label):
        self.label = label
        self.arcs = []          # (key_src, key_dst, ivl dict, fallback?)
        self.keys = {}
        self.req = None
        self.data = set()

    def add(self, a, b, ivl, fb):
        self.arcs.append((a, b, ivl, fb))

    def emit(self, f, launch, setup=0):
        succ = defaultdict(list)
        indeg = defaultdict(int)
        nodes = {launch}
        for a, b, _, _ in self.arcs:
            succ[a].append(b); indeg[b] += 1; nodes |= {a, b}
        if indeg[launch]:
            raise RuntimeError(f"{self.label}: arc into the launch")
        order, ready = [], [launch]
        while ready:
            n = ready.pop(); order.append(n)
            for m in succ[n]:
                indeg[m] -= 1
                if indeg[m] == 0:
                    ready.append(m)
        if len(order) != len(nodes):
            raise RuntimeError(f"{self.label}: cycle after unrolling")
        idx = {n: i for i, n in enumerate(order)}
        nfb = sum(fb for *_, fb in self.arcs)
        for v in VARIANTS:
            f.write(f"inst {self.label} {v} fallback={nfb}/{len(self.arcs)}\n")
            f.write(f"setup {setup}\nreq {idx[self.req]}\n")
            f.write("data " + " ".join(str(idx[d]) for d in sorted(self.data, key=idx.get)) + "\n")
            for a, b, ivl, _ in sorted(self.arcs, key=lambda x: (idx[x[0]], idx[x[1]])):
                lo, hi = ivl[v]
                f.write(f"arc {idx[a]} {idx[b]} {lo} {hi}\n")
            f.write("end\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("build")
    ap.add_argument("top")
    ap.add_argument("--out", required=True)
    ap.add_argument("--cells", default=str(REPO / "cells"))
    ap.add_argument("--osc", action="append", default=[])
    ap.add_argument("--json", help="per-obligation metadata")
    ap.add_argument("--rules2", default="", help="C-10g extra rules, letters of AEFJR8 (rules2.py)")
    ap.add_argument("--no-hi", action="store_true", help="skip 10e's H and I obligations")
    ap.add_argument("--cert", action="store_true",
                    help="C-10h: also emit F, R, H with the late side as a checked potential "
                         "on the cyclic graph (labels Fc, Rc, Hc; certs.py)")
    ap.add_argument("--only", default="", help="C-10h: comma list of rules to emit (e.g. Hc)")
    ap.add_argument("--rules10k", default="", help="C-10k: letters of FZX (rules10k.py: Fd, Z, X)")
    ap.add_argument("--rules10l", default="", help="C-10l: letters of CK (rules10l.py: credited X/Xi/Xm, X4 ctl fork)")
    a = ap.parse_args()
    bd = pathlib.Path(a.build)
    sdf, routed, fasm = bd / f"{a.top}.sdf", bd / f"{a.top}_routed.json", bd / f"{a.top}.fasm"
    T, R, F = load_rules(pathlib.Path(a.cells))
    # tighten.main's order: parse, cut false arcs, storage census, then --osc
    # (routed_graph would abort on the declared oscillator before --osc applies)
    edges, _ct, _n1, _n2 = T.parse_sdf(sdf)
    dead, _ = T.false_arcs(edges, sdf)
    for src in list(edges):
        edges[src] = [(d_, w) for d_, w in edges[src] if (src, d_) not in dead]
    stops = T.storage_nodes(edges)
    for prefix in a.osc:          # as tighten.py --osc: cut every arc sourced in the instrument
        for src in list(edges):
            i = T.pin_split(src)[0]
            if i == prefix or i.startswith(prefix + "."):
                edges[src] = []
    back = defaultdict(set)
    for s_, lst in edges.items():
        for d_, _ in lst:
            back[d_].add(s_)
    ff, fr = T.fastfall_side_arcs(edges), T.fastrise_side_arcs(edges)
    timing = T.Timing(edges, stops)
    P = Prjx(R, F, fasm, routed)
    W = {}
    nfb = [0, 0]

    def ivl(s_, d_, w):
        if (s_, d_) not in W:
            # a cell arc: same instance, input pin -> output pin (an output -> own input
            # arc is the routed feedback wire, an INTERCONNECT)
            same = T.pin_split(s_)[0] == T.pin_split(d_)[0] and not T.is_output(s_)
            c = P.iopath(s_, d_) if same else P.interconnect(s_, d_)
            W[(s_, d_)] = (intervals(w, c), c is None)
            nfb[c is None] += 1
        return W[(s_, d_)]

    def segment(I, tag, start_key, start, targets, excl, inside=None):
        """Add the sub-DAG of all arcs on start -> targets paths that avoid storage
        (and the arcs in `excl`) to I; node keys (tag, pin).  Returns reached targets.
        `inside` (C-10g, rule A's confinement): a predicate every arc's DESTINATION
        must satisfy, as tighten.walk's `confine`."""
        if inside is not None:
            excl = _Excl(excl, inside)
        fwd, work = {start}, [start]
        while work:
            p = work.pop()
            if p in stops and p != start:
                continue
            for d_, _ in edges.get(p, ()):
                if (p, d_) in excl or d_ in fwd or d_ == start:
                    continue
                fwd.add(d_); work.append(d_)
        hit = {t for t in targets if t in fwd}
        bwd, work = set(hit), list(hit)
        while work:
            p = work.pop()
            for s_ in back.get(p, ()):
                if s_ in fwd and s_ not in bwd and (s_ not in stops or s_ == start) \
                        and any(d_ == p for d_, _ in edges.get(s_, ()) if (s_, d_) not in excl):
                    bwd.add(s_); work.append(s_)
        key = lambda p: start_key if p == start else (tag, p)   # noqa: E731
        for p in bwd:
            if p in stops and p != start:
                continue
            for d_, w in edges.get(p, ()):
                if d_ in bwd and d_ != start and (p, d_) not in excl:
                    iv, fb = ivl(p, d_, w)
                    I.add(key(p), key(d_), iv, fb)
        return {t: key(t) for t in hit}

    controllers = sorted(s for s in stops if T.latch_enables(edges, s))
    out = open(a.out, "w")
    meta = []
    want = set(a.only.split(",")) if a.only else {"H", "I", "Hc", "A", "E", "F", "J", "W", "R", "Fc", "Rc"}
    import certs                          # noqa: E402  (C-10h)
    cctx = dict(T=T, edges=edges, stops=stops, fr=fr, ivl=ivl, VARIANTS=VARIANTS, out=out,
                meta=meta, cert=a.cert)
    for ctl in ([] if a.no_hi else controllers):
        label = T.pin_split(ctl)[0]
        if T.dc_link_of(ctl) is not None:
            meta.append({"ctl": label, "rule": "I", "skip": "bd_link_dc (not modelled)"})
            continue
        enables = T.latch_enables(edges, ctl)
        en_pins = {p for p, _ in enables}
        insts = {T.pin_split(p)[0] for p in en_pins}
        d_pins = T.latch_data_pins(back, insts, en_pins)
        if not d_pins:
            continue
        outs = lambda i: [o for o in (i + "/O6", i + "/O5") if o in edges]  # noqa: E731

        def close_seg(I, tag, frm_key):
            """ctl -> enable pins -> latch LUT outputs; returns the output keys."""
            ks = []
            for p, w in enables:
                iv, fb = ivl(ctl, p, w)
                I.add(frm_key, (tag, p), iv, fb)
                for o, w2 in edges.get(p, ()):
                    if T.is_output(o) and T.pin_split(o)[0] == T.pin_split(p)[0]:
                        iv, fb = ivl(p, o, w2)
                        I.add((tag, p), (tag, o), iv, fb)
                        ks.append((tag, o))
            return ks

        # ---------------- I: capture
        feeders = set()
        for dp in d_pins:
            feeders |= {s for s in T.starts_reaching(back, dp, stops)
                        if s in stops and T.RE_BD_LATCH.search(T.pin_split(s)[0])}
        ups = [up for up in controllers if up != ctl and ctl in timing.early(up)
               and any(T.pin_split(f_)[0] in {T.pin_split(p)[0] for p, _ in T.latch_enables(edges, up)}
                       for f_ in feeders)]
        for up in ups:
            I = Inst(f"I {label} up={T.pin_split(up)[0]}")
            L = ("launch", up)
            r1 = segment(I, "s1", L, up, {ctl}, ff)
            if ctl not in r1:
                continue
            r2 = segment(I, "s2", r1[ctl], ctl, {up}, ff)
            if up not in r2:
                continue
            r3 = segment(I, "s3", r2[up], up, {ctl}, fr)
            if ctl not in r3:
                continue
            ks = close_seg(I, "s4", r3[ctl])
            I.add(("close",), ("closeAny",), {v: (0, 0) for v in VARIANTS}, False)
            for k in ks:
                I.add(k, ("close",), {v: (0, 0) for v in VARIANTS}, False)
            I.req = ("closeAny",)
            own_lat = {T.pin_split(p)[0] for p, _ in T.latch_enables(edges, up)}
            # data: up -> its enables -> its latch outputs (feeders) -> ctl's D pins
            fs = [f_ for f_ in feeders if T.pin_split(f_)[0] in own_lat]
            rf = segment(I, "d1", L, up, set(fs), set())
            for f_, fk in rf.items():
                rd = segment(I, ("d2", f_), fk, f_, set(d_pins), set())
                for dp, dk in rd.items():
                    inst = T.pin_split(dp)[0]
                    for o, w in edges.get(dp, ()):
                        if T.is_output(o) and T.pin_split(o)[0] == inst:
                            iv, fb = ivl(dp, o, w)
                            I.add(dk, ("dq", f_, o), iv, fb)
                            # round the feedback loop back to the latch's own pins
                            for fbp, w2 in edges.get(o, ()):
                                if not T.is_output(fbp) and T.pin_split(fbp)[0] == inst:
                                    iv2, fb2 = ivl(o, fbp, w2)
                                    I.add(("dq", f_, o), ("dfb", f_, fbp), iv2, fb2)
                                    I.data.add(("dfb", f_, fbp))
            if not I.data or "I" not in want:
                continue
            I.emit(out, L)
            meta.append({"ctl": label, "rule": "I", "up": T.pin_split(up)[0], "label": I.label})

        # ---------------- H: hold
        I = Inst(f"H {label}")
        L = ("launch", ctl)
        ks = close_seg(I, "en", L)
        I.data = set(ks)

        def own(pin):
            return T.pin_split(pin)[0] in insts
        chains_ok = False
        for v in ("sdf",):     # path chosen once on the SDF lower bounds (see H_EXTRACT_MIN)
            # (pin, phase): phase 0 = still on the falling edge out of ctl (no FASTRISE
            # taps), phase 1 = past the first state node (any polarity), as tighten.
            best, prev = {(ctl, 0): 0}, {}
            heap = [(0, ctl, 0)]
            hit = None
            while heap:
                t, p, ph = heapq.heappop(heap)
                if t > best.get((p, ph), math.inf):
                    continue
                if p in d_pins:
                    hit = (p, ph)
                    break
                if p in stops and p != ctl and own(p):
                    continue
                nph = 1 if (p in stops and p != ctl) else ph
                for d_, w in edges.get(p, ()):
                    if nph == 0 and (p, d_) in fr:
                        continue
                    lo = ivl(p, d_, w)[0][v][0]
                    if t + lo < best.get((d_, nph), math.inf):
                        best[(d_, nph)] = t + lo; prev[(d_, nph)] = (p, ph)
                        heapq.heappush(heap, (t + lo, d_, nph))
            if hit is None:
                break
            path = [hit]
            while path[-1] != (ctl, 0):
                path.append(prev[path[-1]])
            path.reverse()
            if len({q for q in path}) != len(path):
                break
            for (x, px), (y, py) in zip(path, path[1:]):
                w = next(w for d_, w in edges[x] if d_ == y)
                iv, fb = ivl(x, y, w)
                I.add(L if (x, px) == (ctl, 0) else ("dist", x, px), ("dist", y, py), iv, fb)
            hit = ("dist",) + hit
            I.req = hit
            chains_ok = True
            nstate = sum(1 for p, _ in path[1:-1] if p in stops)
        if chains_ok and I.data:
            I.label = f"H {label} via={nstate}states"
            if "H" in want:
                I.emit(out, L)
                meta.append({"ctl": label, "rule": "H", "label": I.label})
        if a.cert and "Hc" in want:
            # C-10h: same data side (ctl -> enables -> latch outputs); late side = the
            # earliest disturbance of a D pin over the WHOLE graph, phase rule as the
            # Dijkstra above (phase 0: no FASTRISE taps until a state node; ctl's own
            # latch bits not crossed), bounded by a checked potential.
            Ic = Inst(f"Hc {label}")
            Ic.arcs = [x for x in I.arcs if x[1][0] == "en"]
            Ic.data = set(ks)
            own_st = {p for p in stops if own(p) and p != ctl}
            sp = certs.spec(ctl, [(dp, ph) for dp in d_pins for ph in (0, 1)],
                            two=1, noFr0=1, swStor=1, blocked=own_st)
            certs.emit_cert(cctx, Ic, L, sp, {"ctl": label, "rule": "Hc"})
    if a.rules2 or a.rules10k or a.rules10l:
        import rules2                     # noqa: E402  (C-10g: rules A, E, F, J, RT_FB, 8e)
        ctx = dict(T=T, P=P, edges=edges, back=back, stops=stops, ff=ff, fr=fr, timing=timing,
                   ivl=ivl, segment=segment, out=out, meta=meta, sdf=sdf, routed=routed,
                   controllers=controllers, osc=a.osc, Inst=Inst, VARIANTS=VARIANTS,
                   intervals=intervals, cert=a.cert, cctx=cctx, certs=certs, want=want)
        if a.rules2:
            rules2.emit_all(ctx, a.rules2)
        if a.rules10k:
            import rules10k               # noqa: E402  (C-10k: Fd, Z, X)
            rules10k.emit_all(ctx, a.rules10k)
        if a.rules10l:
            import rules10l               # noqa: E402  (C-10l: credited X/Xi/Xm, K)
            rules10l.emit_all(ctx, a.rules10l)
    out.close()
    print(f"extract: {len(controllers)} controllers, {len(meta)} obligations; "
          f"arcs with prjxray numbers {nfb[0]}, fallback to SDF band {nfb[1]}, "
          f"prjxray min>max hulled {INVERTED[0]}", file=sys.stderr)
    if a.json:
        kinds = defaultdict(int)
        for (s_, d_), (_iv, fb) in W.items():
            if fb and T.is_const(s_):
                kinds["(constant driver: never switches) net to " + _ct.get(T.pin_split(d_)[0], "?")] += 1
            elif fb:
                same = T.pin_split(s_)[0] == T.pin_split(d_)[0] and not T.is_output(s_)
                ct = _ct.get(T.pin_split(d_)[0], "?")
                kinds[("cell " if same else "net to ") + ct + "/" + re.sub(r"\d+$", "#", T.pin_split(d_)[1])] += 1
        json.dump({"obligations": meta, "fallback_kinds": dict(sorted(kinds.items(), key=lambda x: -x[1]))},
                  open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
