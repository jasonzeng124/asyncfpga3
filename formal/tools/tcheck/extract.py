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

    def lut(self, inst):
        c = self.cells.get(inst)
        if not c:
            return None
        m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])([56])LUT$", c["attributes"].get("NEXTPNR_BEL", ""))
        if not m or m.group(1) not in self.site_at:
            return None
        tile, s = self.site_at[m.group(1)]
        return tile, s, m.group(2), m.group(3)

    def iopath(self, src, dst):
        si, sp = src.rsplit("/", 1)
        di, dp = dst.rsplit("/", 1)
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
        L = self.lut(di)
        if not L or not re.match(r"A[1-6]$", dp):
            return None
        tile, s, letter, _k = L
        sp_name = letter + dp[1]
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
        r = n.sink(tile, wire)
        return r[0] if r else None


def intervals(d, c):
    """{variant: (lo, hi)} from the SDF number d and the prjxray 4-tuple c (or None)."""
    band = (int(math.floor(GUARD_LO * d)), int(math.ceil(GUARD_HI * d)))
    out = {"sdf": (d, d), "sdfband": band}
    if c is None:
        for v in ("fast", "slow", "fastG", "slowG"):
            out[v] = band
    else:
        fm, fM, sm, sM = c
        out["fast"] = (int(math.floor(fm)), int(math.ceil(fM)))
        out["slow"] = (int(math.floor(sm)), int(math.ceil(sM)))
        out["fastG"] = (int(math.floor(GUARD_LO * fm)), int(math.ceil(GUARD_HI * fM)))
        out["slowG"] = (int(math.floor(GUARD_LO * sm)), int(math.ceil(GUARD_HI * sM)))
    return out


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
            same = T.pin_split(s_)[0] == T.pin_split(d_)[0]
            c = P.iopath(s_, d_) if same else P.interconnect(s_, d_)
            W[(s_, d_)] = (intervals(w, c), c is None)
            nfb[c is None] += 1
        return W[(s_, d_)]

    def segment(I, tag, start_key, start, targets, excl):
        """Add the sub-DAG of all arcs on start -> targets paths that avoid storage
        (and the arcs in `excl`) to I; node keys (tag, pin).  Returns reached targets."""
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
    for ctl in controllers:
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
            if not I.data:
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
            I.emit(out, L)
            meta.append({"ctl": label, "rule": "H", "label": I.label})
    out.close()
    print(f"extract: {len(controllers)} controllers, {len(meta)} obligations; "
          f"arcs with prjxray numbers {nfb[0]}, fallback to SDF band {nfb[1]}", file=sys.stderr)
    if a.json:
        json.dump(meta, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
