#!/usr/bin/env python3
"""margin/carryring/loops.py NET.json ROUTED.json PREDICTED.tsv [XRAY.sdf] [--seg OUT.seg] (shard C, UNTRUSTED)

Formal's own prediction of research's carry_ro_top ring periods (BOARD-QUEUE item 36), from the netlist DECODED FROM
THE BITS (tools-A decode_base.py + build_net.py; every arc a prjxray number {fmin, smax}, no rise/fall split).

Per ring grp[g].ro[b]: start at the decoded output node of the ring's NAND (routed.json cell grp[g].ro[b].inv, placed
on SLICE/X6LUT -> decoded gate SLICE.XLUT.O6) and enumerate every simple cycle back to it through the decoded gate
graph, following only (a) pip and hop gates (routing, any owner) and (b) LUT / CARRY4 / MUXF gates whose BEL holds a
cell of THIS ring (routed.json NEXTPNR_BEL, the placement the bits were checked EQUIVALENT to) entered on a pin the
gate's truth table actually depends on. Exactly one cycle must be found. Its arcs are summed per class:
    y  carry (CARRY4 IOPATH incl. its site pins as build_net gives them) and muxf (F7/F8 SELMUX IOPATH)
    x  every other gate on the cycle (LUT site pin + IOPATH, pips with their Elmore RC, site output hops)
(draws.py's 'x' class = carry + muxf). period = 2 x loop (one inverting stage; arcs have no rise/fall split), so
    P(x, y) = LO + x R + y CF,   LO = 2 sum fmin, R = 2 sum_x (smax - fmin), CF = 2 sum_y (smax - fmin)
which is research's form (carry_predict.py: P = LO + x R + yc C + yf F, here C or F by ring kind).

With XRAY.sdf (research's xray_delay SDF) the same cycle is also walked in research's arcs (research's own
carry_predict.ring_terms, imported read-only) and both cycles are cut into segments at each logic cell's output
(segment = wire into the cell's pin + the cell's arc), so a disagreement is located to a cell and split into
wire vs cell parts (--seg OUT.seg: the per-segment table for every ring)."""
import argparse, csv, importlib.util, json, os, re, sys
from collections import defaultdict

ap = argparse.ArgumentParser()
ap.add_argument("net"); ap.add_argument("routed"); ap.add_argument("pred"); ap.add_argument("xray", nargs="?")
ap.add_argument("--seg"); ap.add_argument("--rsch", default=os.environ.get("RSCH", "/home/user/rsch"))
a = ap.parse_args()

N = json.load(open(a.net)); G = N["gates"]; NAMES = N["nodes"]
BEL = {c["attributes"].get("NEXTPNR_BEL"): n for n, c in json.load(open(a.routed))["modules"]["top"]["cells"].items()
       if c.get("attributes", {}).get("NEXTPNR_BEL")}
INV = {v: k for k, v in BEL.items()}
KINDS = ["L8", "C1", "C4", "F8", "C16", "L16", "C32", "F16"]   # KIND[(g+b)%8], carry_ro_top.v


def owner(g):
    """yosys cell placed on the BEL this decoded gate models, or None (pip / hop / const)."""
    k, nm = g["kind"], g["name"]
    if k in ("lut6", "lut5"):
        m = re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])$", nm)
        return BEL.get("%s/%s%sLUT" % m.groups()) if m else None
    if k == "carry":
        return BEL.get(nm.split(".")[0] + "/CARRY4")
    if k == "muxf":
        s, mx = nm.split(".")
        return BEL.get("%s/%sMUX" % (s, mx))
    return None


def sens(g, p):
    """does the gate's function depend on input p (truth table over its k inputs, bit i = ins[i])"""
    k, f = g["k"], g["init"]
    return any(((f >> i) & 1) != ((f >> (i ^ (1 << p))) & 1) for i in range(1 << k))


OWN = [owner(g) for g in G]
RD = defaultdict(list)
for gi, g in enumerate(G):
    for p, n in enumerate(g["ins"]):
        RD[n].append((gi, p))
_sc = {}


def ok(gi, p, pref):
    g = G[gi]
    if g["kind"] in ("pip", "hop"):
        return True
    if g["kind"] not in ("lut6", "lut5", "carry", "muxf") or not (OWN[gi] or "").startswith(pref):
        return False
    if (gi, p) not in _sc:
        _sc[(gi, p)] = sens(g, p)
    return _sc[(gi, p)]


def cycles(start, pref, cap=50):
    out, stack = [], [(start, [], frozenset([start]))]
    while stack:
        n, path, seen = stack.pop()
        for gi, p in RD.get(n, ()):
            if not ok(gi, p, pref):
                continue
            o = G[gi]["out"]
            if o == start:
                out.append(path + [(gi, p)])
                if len(out) > cap:
                    return out
                continue
            if o in seen or len(path) > 4000:
                continue
            stack.append((o, path + [(gi, p)], seen | {o}))
    return out


def ycls(g):
    return g["kind"] in ("carry", "muxf")


# research's walk (read-only import), for the segment comparison
RW = None
if a.xray:
    sp = importlib.util.spec_from_file_location("carry_predict", os.path.join(a.rsch, "cells/hw/carry_ring/carry_predict.py"))
    RW = importlib.util.module_from_spec(sp); sp.loader.exec_module(RW)
    RE = RW.parse(a.xray)

PRED = {(int(r["g"]), int(r["b"])): r for r in csv.DictReader(open(a.pred), delimiter="\t")}
segf = open(a.seg, "w") if a.seg else None
if segf:
    segf.write("ring\tcell\tF_wire_lo\tR_wire_lo\tF_cell_lo\tR_cell_lo\tF_wire_hi\tR_wire_hi\tF_cell_hi\tR_cell_hi\n")
cols = ["ring", "kind", "n", "cyc", "same_cells", "f_lo", "f_R", "f_CF", "f_arcs", "f_ny",
        "f_P02", "f_P10", "f_Pmin", "f_Pmax", "r_P02", "r_P10", "r_Pmin", "r_Pmax",
        "q_P02", "q_P10", "q_Pmin", "q_Pmax", "f_dPdy", "r_dPdy", "flag"]
print("\t".join(cols))
for g in range(8):
    for b in range(8):
        pref = "grp[%d].ro[%d]." % (g, b); kd = KINDS[(g + b) % 8]
        m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])6LUT$", INV[pref + "inv"])
        gname = "%s.%sLUT.O6" % m.groups()
        gi0 = next(i for i, x in enumerate(G) if x["name"] == gname)
        cyc = cycles(G[gi0]["out"], pref)
        row = {"ring": "g%d.b%d" % (g, b), "kind": kd[0], "n": kd[1:], "cyc": len(cyc)}
        r = PRED[(g, b)]
        if len(cyc) != 1:
            row["flag"] = "NO_UNIQUE_CYCLE"; print("\t".join(str(row.get(c, "")) for c in cols)); continue
        cy = cyc[0]
        lo = sum(G[gi]["arcs"][p]["fmin"] for gi, p in cy)
        R = sum(G[gi]["arcs"][p]["smax"] - G[gi]["arcs"][p]["fmin"] for gi, p in cy if not ycls(G[gi]))
        CF = sum(G[gi]["arcs"][p]["smax"] - G[gi]["arcs"][p]["fmin"] for gi, p in cy if ycls(G[gi]))
        lo, R, CF = 2 * lo, 2 * R, 2 * CF
        P = lambda x, y: lo + x * R + y * CF
        rP = lambda x, y: float(r["lo_ps"]) + x * float(r["R_ps"]) + y * (float(r["C_ps"]) + float(r["F_ps"]))
        fcells = [OWN[gi] for gi, p in cy if OWN[gi]]
        row.update(f_lo=lo, f_R=R, f_CF=CF, f_arcs=len(cy), f_ny=sum(1 for gi, p in cy if ycls(G[gi])))
        for t, (x, y) in (("P02", (.288, .2)), ("P10", (.288, 1.0)), ("Pmin", (0, 0)), ("Pmax", (1, 1))):
            fv = P(x, y); rv = float(r["P_" + {"P02": "x288_y02", "P10": "x288_y10", "Pmin": "fastmin", "Pmax": "slowmax"}[t]])
            row["f_" + t] = "%.0f" % fv; row["r_" + t] = "%.0f" % rv; row["q_" + t] = "%.4f" % (fv / rv)
        row["f_dPdy"] = CF; row["r_dPdy"] = int(r["C_ps"]) + int(r["F_ps"])
        row["flag"] = r["flag"]
        if RW is not None:
            t, err = RW.ring_terms(RE, g, b)
            rcells = []
            for s, d, w, cls in t["path"]:
                ins = d.rpartition("/")[0]
                if ins == s.rpartition("/")[0]:
                    rcells.append(ins)        # an IOPATH: the walk passes through this cell
            row["same_cells"] = "yes" if rcells == fcells else "NO"   # both walks start at inv's output
            if segf:
                # research segments: INTERCONNECT(s) into the cell, then the cell's IOPATH
                rseg, acc = [], [0, 0]
                for s, d, (lo_, _m, hi_), cls in t["path"]:
                    if s.rpartition("/")[0] == d.rpartition("/")[0]:
                        rseg.append((d.rpartition("/")[0], acc, [lo_, hi_])); acc = [0, 0]
                    else:
                        acc = [acc[0] + lo_, acc[1] + hi_]
                fseg, acc = [], [0, 0]
                for gi, p in cy:
                    e = G[gi]["arcs"][p]
                    if OWN[gi]:
                        fseg.append((OWN[gi], acc, [e["fmin"], e["smax"]])); acc = [0, 0]
                    else:
                        acc = [acc[0] + e["fmin"], acc[1] + e["smax"]]
                rs = {c: (w, c2) for c, w, c2 in rseg}
                for c, w, c2 in fseg:
                    rw, rc = rs.get(c, ([None, None], [None, None]))
                    segf.write("%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" % (row["ring"], c, w[0], rw[0], c2[0], rc[0],
                                                                          w[1], rw[1], c2[1], rc[1]))
        else:
            row["same_cells"] = "?"
        print("\t".join(str(row.get(c, "")) for c in cols))
