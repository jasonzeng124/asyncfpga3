#!/usr/bin/env python3
"""draw_sdf.py ROUTED_JSON XRAY_SDF K OUT_SDF [--carry LO,HI] [--chain-rx RX] -- one draw of the delay model
(research/tools/eventgraph/bench_gate.sh draw:K) written as an SDF with ONE delay per arc, on the routed JSON's own
instance names, for the static rules (research/tools/corner_audit.py) to read.

bench_gate.sh draw:K gives cells/gls/gen.py, on the netlist decoded from the bits: bands XC (delay chains), XR (the
rest), XK (CARRY4 / SELMUX2_1 / SLICE_FFX / RAMB18E1) from random.Random(7919 K + 17) -- XC, XR uniform on
[0.20, 0.31], XK uniform on [LO, HI] (default [0.20, 1.0], DRAW_CARRY); an arc's delay = FAST_MIN + band *
(SLOW_MAX - FAST_MIN) (the xray SDF's (FAST_MIN : SLOW_MIN : SLOW_MAX) triple); then the scatter of setting M:
GLS_SCATTER=0.126 in wire mode (an INTERCONNECT arc times the mean of its route branch's per-pip factors, each
1 + 0.126 N from md5("K:pip"); an arc whose branch is not found, and every IOPATH arc, its own 1 + 0.126 N) and
GLS_SCATTER_REGION=0.02 (1 + 0.02 N per 10 x 10 slice block, md5("region:K:x:y"); a cell arc its own site's, an
INTERCONNECT its sink's).  This file does the same on the xray SDF of the routed JSON: the bands, the per-pip and the
region factors are gen.py's exactly (the same hashes); the per-arc normals of IOPATH (and fallback) arcs come from
random.Random(K) in this file's own order, so they are the same distribution but not the same numbers as gen.py's
(gen.py draws them in its own arc order).  SETUPHOLD lines are copied unchanged (gen.py does not scatter them either).
Every written arc carries its delay in all three columns of both triples: corner_audit reads it at any band.
"""
import argparse
import hashlib
import json
import math
import random
import re

RE_CT = re.compile(r'\(CELLTYPE "([^"]*)"\)')
RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)\s+\((\d+):(\d+):(\d+)\)\)")
RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)\s+\((\d+):(\d+):(\d+)\)\)")
RE_SITE = re.compile(r"^[A-Z0-9_]*?_X(\d+)Y(\d+)/")
CELL_K = ("CARRY4", "SELMUX2_1", "SLICE_FFX", "RAMB18E1_RAMB18E1")
SIGMA, SIGMA_R, REGION = 0.126, 0.02, 10


def unesc(s):
    return s.replace("\\", "")


def normal_from_md5(text):
    h = hashlib.md5(text.encode()).digest()
    u1 = (int.from_bytes(h[:8], "big") + 1) / 2.0 ** 64
    u2 = int.from_bytes(h[8:], "big") / 2.0 ** 64
    return math.sqrt(-2 * math.log(u1)) * math.cos(2 * math.pi * u2)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("routed_json")
    ap.add_argument("xray_sdf")
    ap.add_argument("k", type=int)
    ap.add_argument("out_sdf")
    ap.add_argument("--carry", default="0.20,1.0")
    ap.add_argument("--chain-rx", default=r"\.chain\.g\[\d+\]\.u$")
    a = ap.parse_args()
    K = a.k
    r = random.Random(7919 * K + 17)
    xc, xr, u = r.uniform(.20, .31), r.uniform(.20, .31), r.random()
    lo, hi = (float(x) for x in a.carry.split(","))
    xk = lo + u * (hi - lo)
    # bench_gate.sh prints the bands with 4 decimals and gen.py reads them back: use the same rounding
    xc, xr, xk = (float("%.4f" % v) for v in (xc, xr, xk))
    top = json.load(open(a.routed_json))["modules"]["top"]
    cells = top["cells"]
    chain_rx = re.compile(a.chain_rx)
    chains = {n for n in cells if chain_rx.search(n)}
    routes = {}
    for nn in top["netnames"].values():
        rr = nn.get("attributes", {}).get("ROUTING")
        if rr and nn["bits"]:
            routes.setdefault(nn["bits"][0], rr)
    parents = {}
    pip_f, reg_f = {}, {}
    arc_rng = random.Random(K)

    def pipf(p):
        if p not in pip_f:
            pip_f[p] = 1 + SIGMA * normal_from_md5("%s:%s" % (K, p))
        return pip_f[p]

    def regf(inst):
        c = cells.get(inst)
        m = RE_SITE.match(c.get("attributes", {}).get("NEXTPNR_BEL", "")) if c else None
        if not m:
            return 1.0
        k = (int(m.group(1)) // REGION, int(m.group(2)) // REGION)
        if k not in reg_f:
            reg_f[k] = 1 + SIGMA_R * normal_from_md5("region:%s:%d:%d" % (K, k[0], k[1]))
        return reg_f[k]

    def wire_factor(dst):        # gen.py WireModel.factor
        cell, _, pin = dst.rpartition("/")
        c = cells.get(cell)
        if c is None or pin not in c["connections"]:
            return None
        bit = c["connections"][pin][0]
        if bit not in routes:
            return None
        if bit not in parents:
            f = routes[bit].split(";")
            parents[bit] = {f[i]: f[i + 1] for i in range(0, len(f) - 2, 3)}
        par = parents[bit]
        bel = c["attributes"].get("NEXTPNR_BEL", "")
        if "/" not in bel:
            return None
        site, b = bel.split("/")[:2]
        pre = "SITEWIRE/%s/" % site
        if b.endswith("LUT"):
            sinks = [w for w in par if w.startswith(pre) and re.match(r"^%s[1-6]$" % b[0], w[len(pre):])]
        else:
            sinks = [w for w in par if w.startswith(pre + pin)] or \
                    [w for w in par if w.startswith(pre) and par[w] and
                     not any(par.get(x, "").split("->")[0] == w for x in par)]
        if len(sinks) != 1:
            return None
        pips, w, seen = [], sinks[0], set()
        while w in par and par[w] and w not in seen:
            seen.add(w)
            pips.append(par[w])
            w = par[w].split("->")[0]
        if not pips:
            return None
        return sum(pipf(p) for p in pips) / len(pips)

    def band(ct, inst):
        if inst in chains:
            return xc
        return xk if ct in CELL_K else xr

    out, ct, inst = [], None, None
    n = {"ic": 0, "ic_fallback": 0, "io": 0}
    for line in open(a.xray_sdf):
        m = RE_CT.search(line)
        if m:
            ct = m.group(1)
        m = RE_IC.search(line)
        if m:
            src, dst = unesc(m.group(1)), unesc(m.group(2))
            d_inst = dst.rpartition("/")[0]
            fmin, smax = int(m.group(3)), int(m.group(5))
            base = fmin + band(None, d_inst) * (smax - fmin)
            f = wire_factor(dst)
            if f is None:
                f = 1 + SIGMA * arc_rng.gauss(0, 1)
                n["ic_fallback"] += 1
            v = max(0, int(round(base * f * regf(d_inst))))
            line = line[:m.start()] + "(INTERCONNECT %s %s (%d:%d:%d) (%d:%d:%d))" % (
                m.group(1), m.group(2), v, v, v, v, v, v) + line[m.end():]
            n["ic"] += 1
            out.append(line)
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1))
            out.append(line)
            continue
        m = RE_IO.search(line)
        if m and inst is not None:
            fmin, smax = int(m.group(3)), int(m.group(5))
            base = fmin + band(ct, inst) * (smax - fmin)
            v = max(0, int(round(base * (1 + SIGMA * arc_rng.gauss(0, 1)) * regf(inst))))
            line = line[:m.start()] + "(IOPATH %s %s (%d:%d:%d) (%d:%d:%d))" % (
                m.group(1), m.group(2), v, v, v, v, v, v) + line[m.end():]
            n["io"] += 1
        out.append(line)
    open(a.out_sdf, "w").write("".join(out))
    print("draw_sdf K %d: chains %.4f rest %.4f carry/f7f8/ff/ram %.4f; %d INTERCONNECT (%d without a route branch: "
          "own factor), %d IOPATH; %d pips, %d regions" % (K, xc, xr, xk, n["ic"], n["ic_fallback"], n["io"],
                                                           len(pip_f), len(reg_f)))


if __name__ == "__main__":
    main()
