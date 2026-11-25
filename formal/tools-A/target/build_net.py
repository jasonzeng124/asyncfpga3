#!/usr/bin/env python3
"""build_net.py (shard A, THE goal): the target's decoded netlist in Spec.lean's form.

    python3 build_net.py D0.JSON FROMBIT.FASM ROUTED.JSON OUT.json

D0.JSON is decode_base.py's output (shard C's fasm2lean3 decoder, copied, plus the
route of every walked pin, pip by pip). This script turns it into the gate list of
Formal.Target.Spec: every node is a routing node (prjxray tileconn) or a site-internal
net, every gate is `k` input nodes, an INIT, one prjxray arc per pin, one output node.

  gate kind   inputs                         INIT                     arcs (ps, prjxray)
  pip         its source node                0b10 (copy)              src_to_dst delay; upper ends + Elmore RC
  lut6        site pins A1..A6               the 64-bit INIT          site-pin delay + IOPATH Ak O6
  lut5        site pins A1..A5               INIT[31:0]               site-pin delay + IOPATH Ak O5
  muxf        I0, I1, S                      0xCA (S ? I1 : I0)       IOPATH 0/1/S0 OUT (F7AMUX, F7BMUX, F8MUX)
  carry       CI, CYINIT, S0..Si, DI0..      the CARRY4 function      IOPATH x -> COi / Oi; DI arcs: envelope
              (CO_i, O_i: one gate each)                                over the CARRY4_* variants
  hop         a site-internal net            0b10                     0 (prjxray puts it in the BEL arc)
  const       none                           1 (VCC) or 0 (GND)       none
Flip-flops, clock buffers, BSCAN, IOBs: NO gate (their output nets are free nodes).
Every choice that is not plain prjxray data is listed in the output's "fidelity".
Untrusted: what it emits is checked by the Lean round trip (Formal/Target/), not trusted.
"""
import json
import os
import re
import sys
from collections import defaultdict

TC = os.environ.get("TC", os.path.expanduser("~/dev2/lib/fpgatoolchain"))
DB = os.path.join(TC, "openxc7/share/nextpnr/prjxray-db/zynq7")


def die(m):
    print("build_net: " + m, file=sys.stderr)
    sys.exit(1)


def ps4(d):
    if not d:
        return None
    return [int(round(float(x) * 1000)) for x in d]


# ---------- prjxray SDF (site timing) ----------
def read_sdf(path):
    """{(celltype, instance): {(in, out): [fmin, fmax, smin, smax] (envelope if repeated)}}"""
    txt = open(path).read()
    out = defaultdict(dict)
    for cell in re.finditer(r'\(CELLTYPE "([^"]+)"\)\s*\(INSTANCE ([^)]*)\)(.*?)\n    \)', txt, re.S):
        ct, inst, body = cell.group(1), cell.group(2).strip(), cell.group(3)
        for m in re.finditer(r"\(IOPATH (\S+) (\S+) \(([\d.]+)::([\d.]+)\)\(([\d.]+)::([\d.]+)\)\)", body):
            k = (m.group(1), m.group(2))
            v = [int(round(float(m.group(i)) * 1000)) for i in (3, 4, 5, 6)]
            old = out[(ct, inst)].get(k)
            out[(ct, inst)][k] = v if old is None else [min(old[0], v[0]), max(old[1], v[1]),
                                                         min(old[2], v[2]), max(old[3], v[3])]
    return out


_sdf = {}


def sdf_for(tiletype):
    if tiletype not in _sdf:
        _sdf[tiletype] = read_sdf(os.path.join(DB, "timings", tiletype + ".sdf"))
    return _sdf[tiletype]


def iopath(tiletype, sitetype, inst, a, b, celltypes=None):
    """IOPATH a->b of instance <sitetype>/<inst> (or <sitetype> if inst is None), envelope over
    the cell types given (all, if None)."""
    want = sitetype if inst is None else "%s/%s" % (sitetype, inst)
    hits = []
    for (ct, i), paths in sdf_for(tiletype).items():
        if i == want and (celltypes is None or ct in celltypes or any(ct.startswith(c) for c in celltypes)):
            if (a, b) in paths:
                hits.append(paths[(a, b)])
    if not hits:
        return None
    return [min(h[0] for h in hits), max(h[1] for h in hits), min(h[2] for h in hits), max(h[3] for h in hits)]


def main():
    d0, fasm_path, routed_path, outp = sys.argv[1:5]
    D = json.load(open(d0))
    tiles = json.load(open(os.path.join(DB, "xc7z010", "tilegrid.json")))
    tt_cache = {}

    def tt(tile):
        t = tiles[tile]["type"]
        if t not in tt_cache:
            p = os.path.join(DB, "tile_type_%s.json" % t)
            tt_cache[t] = json.load(open(p)) if os.path.exists(p) else {"pips": {}, "sites": [], "wires": {}}
            j = tt_cache[t]
            j["_by"] = {}
            for p in j["pips"].values():
                j["_by"][(p["dst_wire"], p["src_wire"])] = (p, False)
                if str(p.get("is_directional")) == "0":
                    j["_by"].setdefault((p["src_wire"], p["dst_wire"]), (p, True))
            j["_sp"] = {}
            for s in j["sites"]:
                for pin, v in s["site_pins"].items():
                    if v and v.get("wire"):
                        j["_sp"][v["wire"]] = (s, pin, v)
        return tt_cache[t]

    fidelity = defaultdict(int)
    nodes = {}

    def node(name):
        if name not in nodes:
            nodes[name] = len(nodes)
        return nodes[name]

    gates = []
    driver = {}

    def add_gate(g):
        o = g["out"]
        if o in driver:
            prev = gates[driver[o]]
            if (prev["kind"], prev["ins"], prev["init"]) == (g["kind"], g["ins"], g["init"]):
                return driver[o]
            die("node %s has two drivers: %s and %s" % (o, prev["name"], g["name"]))
        driver[o] = len(gates)
        gates.append(g)
        return driver[o]

    # ---- the loads of each routing node, for the Elmore term: (buffered pips leaving it
    # that are on) in_cap, plus site input pin caps
    pips_on = {}   # (tile, dst, src) -> (pseudo, srcnode, dstnode)
    for c in D["cells"]:
        for pin, v in c["conn"].items():
            r = v.get("_route") if isinstance(v, dict) else None
            if r:
                for t, dw, sw, ps, sn, dn in r["pips"]:
                    pips_on[(t, dw, sw)] = (ps, sn, dn)
    load = defaultdict(float)
    pass_out = defaultdict(list)
    for (t, dw, sw), (ps, sn, dn) in pips_on.items():
        p, rev = tt(t)["_by"].get((dw, sw), (None, False))
        if p is None:
            die("pip %s.%s.%s not in prjxray-db" % (t, dw, sw))
        if p["is_pass_transistor"]:
            pass_out[sn].append(dn)
        else:
            s2d = (p.get("dst_to_src") if rev else p.get("src_to_dst")) or {}
            load[sn] += float(s2d.get("in_cap") or 0)

    def load_star(n, depth=0):
        return load[n] + (sum(load_star(m, depth + 1) for m in pass_out.get(n, ())) if depth < 20 else 0)

    # ---- (shard A, 2026-11-17) RC_TREE=1: prjxray Elmore tree as research's xray_delay.py
    # (cells/gls/fid/xray_delay.py on claude/research, evaluating prjxray/timing.py). Off by default:
    # without RC_TREE nothing below runs and the output is byte-identical. The tree: a WIRE is a
    # prjxray node, R and C summed over its tile wires (LV nodes: two wires' RC); a buffered pip is
    # Buffer(R = pip res, C = in_cap), a pass pip PassTransistor(R); the root is the site output pin
    # (drive R), the leaves the site input pins (pin C). Elmore terms (ohm * fF * 1e-3 = ps), each on
    # every corner, ceil'd once per gate:
    #   pip gate  += R_pip * Cup(dst) + R_dst * (C_dst/2 + Cdown(dst))     [the pip and its dst wire]
    #   hop gate  += R_drive * Cup(src) + R_src * (C_src/2 + Cdown(src))   [output pin and its wire]
    # Cdown(n) = sum over n's children (buffer: in_cap; pass pip: Cup(its dst); input pin: pin C),
    # Cup(n) = C_n + Cdown(n). A sink's sum along its path is then prjxray's Elmore delay to it. Also as
    # research: the hop carries the output pin's intrinsic delay and, unless RC_TREE_OUTMUX=0, the
    # slice OUTMUX routing-BEL arc (x6lut/x5lut/f7/f8/carry4/x5ff -> xMUX, timings/slice[lm].sdf);
    # a LUT route-through (prjxray is_pseudo) pip carries its input site pin's delay.
    RC_TREE = os.environ.get("RC_TREE") == "1"
    if RC_TREE:
        import importlib.util as _ilu
        _sp = _ilu.spec_from_file_location("db", os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                              "decode_base.py"))
        _DBm = _ilu.module_from_spec(_sp)
        _sp.loader.exec_module(_DBm)
        rfab = _DBm.Fabric3()
        rc_kids = defaultdict(list)        # node -> [(R, is_pass, in_cap, dst node)]
        for (t, dw, sw), (ps, sn, dn) in pips_on.items():
            p, rev = tt(t)["_by"][(dw, sw)]
            s2d = (p.get("dst_to_src") if rev else p.get("src_to_dst")) or {}
            rc_kids[sn].append((float(s2d.get("res") or 0), bool(p["is_pass_transistor"]),
                                float(s2d.get("in_cap") or 0), dn))
            if not p["is_pass_transistor"] and not float(s2d.get("res") or 0) and p["is_pseudo"] != "1":
                fidelity["RC_TREE: buffered pip with R 0 (no Elmore term of its own)"] += 1
        rc_pin = defaultdict(float)        # node -> input pin C of the site pins it feeds
        _seen = set()
        for c in D["cells"]:
            for v in c["conn"].values():
                r = v.get("_route") if isinstance(v, dict) else None
                if r and tuple(r["sinkwire"]) not in _seen:
                    _seen.add(tuple(r["sinkwire"]))
                    spn = tt(r["sinkwire"][0])["_sp"].get(r["sinkwire"][1])
                    rc_pin[r["sink"]] += float((spn[2].get("cap") if spn else 0) or 0)
        _wrc = {}

        def wire_rc(n):
            """(R ohm, C fF) of node n: its tile wires summed (xray_delay.py node_rc)."""
            if n not in _wrc:
                t0, w0 = n.split("/", 1)
                if t0 not in tiles:
                    _wrc[n] = (0.0, 0.0)
                    fidelity["RC_TREE: node not in the tile grid (wire RC 0)"] += 1
                    return _wrc[n]
                ws = sorted(rfab.node(t0, w0))
                els = []
                for t2, w2 in ws:
                    wd = tt(t2).get("wires")
                    rc = wd.get(w2) if isinstance(wd, dict) else None
                    if rc and (float(rc.get("res") or 0) or float(rc.get("cap") or 0)):
                        els.append((float(rc.get("res") or 0), float(rc.get("cap") or 0)))
                if any(w2.startswith("LV") for _, w2 in ws):
                    els = els[:2]
                _wrc[n] = (sum(e[0] for e in els), sum(e[1] for e in els))
            return _wrc[n]
        _cd = {}

        def cdown(n, depth=0):
            if n not in _cd:
                if depth > 200:
                    die("RC_TREE: node %s: tree deeper than 200 (a loop?)" % n)
                _cd[n] = rc_pin[n] + sum((cup(dn, depth + 1) if pt else ic) for _r, pt, ic, dn in rc_kids[n])
            return _cd[n]

        def cup(n, depth=0):
            return wire_rc(n)[1] + cdown(n, depth)

        def wire_term(n):
            R, C = wire_rc(n)
            return R * (C / 2 + cdown(n))

        rb = {}
        for st in ("SLICEL", "SLICEM"):
            txt = open(os.path.join(DB, "timings", st.lower() + ".sdf")).read()
            for cell in re.finditer(r'\(CELLTYPE "ROUTING_BEL"\)\s*\(INSTANCE ([^)]*)\)(.*?)\n    \)', txt, re.S):
                for m in re.finditer(r"\(INTERCONNECT (\S+) (\S+) \(([\d.]+)::([\d.]+)\)\(([\d.]+)::([\d.]+)\)\)",
                                     cell.group(2)):
                    rb[(cell.group(1).strip(), m.group(1))] = [int(round(float(m.group(i)) * 1000))
                                                               for i in (3, 4, 5, 6)]

        def outmux(r, net):
            """slice OUTMUX routing-BEL arc for a route leaving through xMUX, or None."""
            if not r.get("srcpin"):
                fidelity["RC_TREE: route with no recorded source pin (no OUTMUX arc)"] += 1
                return None
            t, pin, stype = r["srcpin"][0], r["srcpin"][1], r["srcpin"][2]
            if stype not in ("SLICEL", "SLICEM") or not re.match(r"^[A-D]MUX$", pin):
                return None
            s = str(net).split(".", 1)[-1]
            m = re.match(r"^([A-D])([56])$", s)
            src = ("%s%slut" % (m.group(1).lower(), m.group(2)) if m else
                   {"F7A": "f7amux", "F7B": "f7bmux", "F8": "f8mux"}.get(s) or
                   (re.sub(r"^XOR(\d)$", r"carry4_o\1", s) if s.startswith("XOR") else
                    re.sub(r"^CO(\d)$", r"carry4_co\1", s) if s.startswith("CO") else
                    re.sub(r"^([A-D])5Q$", lambda q: q.group(1).lower() + "5ff", s)))
            d = rb.get(("%s/%s" % (stype, pin), src))
            if d is None:
                fidelity["RC_TREE: OUTMUX %s from %s: no routing-BEL arc in prjxray-db (0)" % (pin, s)] += 1
            return d

        def hop_arc(src, r, net):
            """Output pin (drive R, intrinsic delay) + its node's wire term [+ OUTMUX]."""
            spn = None
            for t2, w2 in sorted(rfab.node(*src.split("/", 1))):
                x = tt(t2)["_sp"].get(w2)
                if x and x[2].get("res") is not None:
                    spn = x
                    break
            d = (ps4(spn[2].get("delay")) if spn else None) or [0, 0, 0, 0]
            if spn is None:
                fidelity["RC_TREE: site output pin with no drive R in prjxray-db (R 0)"] += 1
            rdrv = float(spn[2].get("res") or 0) if spn else 0.0
            rc = int(-(-(rdrv * cup(src) + wire_term(src)) * 1e-3 // 1))
            om = outmux(r, net) if os.environ.get("RC_TREE_OUTMUX", "1") == "1" else None
            if om:
                d = [x + y for x, y in zip(d, om)]
                fidelity["RC_TREE: slice OUTMUX routing-BEL arc on the site output hop"] += 1
            fidelity["RC_TREE: site output hop = output pin delay + Elmore (drive R, wire)"] += 1
            return {"fmin": d[0] + rc, "fmax": d[1] + rc, "smin": d[2] + rc, "smax": d[3] + rc}

    def pip_arc(t, dw, sw, dn):
        p, rev = tt(t)["_by"][(dw, sw)]
        s2d = (p.get("dst_to_src") if rev else p.get("src_to_dst")) or {}
        d = ps4(s2d.get("delay"))
        if d is None:
            d = [0, 0, 0, 0]
            fidelity["pip with no delay data (prjxray: none), arc 0"] += 1
        if not (d[0] <= d[1] and d[2] <= d[3] and d[0] <= d[2] and d[1] <= d[3]):
            # prjxray record not ordered (seen on BRKH_INT *_SLOW and CLK_HROW pips): widen to one
            # band [min, max] at both corners, which contains every number of the record
            m, M = min(d), max(d)
            d = [m, M, m, M]
            fidelity["pip delay record not ordered in prjxray-db: widened to [min, max] at both corners"] += 1
        r = float(s2d.get("res") or 0)
        if RC_TREE:
            # (shard A, 2026-11-17) RC_TREE=1: the pip's and its dst wire's Elmore terms, all corners
            rc = int(-(-(r * cup(dn) + wire_term(dn)) * 1e-3 // 1))
            if p["is_pseudo"] == "1":
                # a LUT route-through: research (as Vivado) charges the input site pin too
                spn = tt(t)["_sp"].get(dw if rev else sw)
                pd = (ps4(spn[2].get("delay")) if spn else None) or [0, 0, 0, 0]
                d = [x + y for x, y in zip(d, pd)]
                fidelity["RC_TREE: route-through pip charged its input site pin delay"] += 1
            fidelity["RC_TREE: pip = intrinsic + Elmore (pip R * Cup(dst) + dst wire), all corners"] += 1
            return {"fmin": d[0] + rc, "fmax": d[1] + rc, "smin": d[2] + rc, "smax": d[3] + rc}
        rc = int(-(-r * load_star(dn) * 1e-3 // 1))   # ceil, ps
        if rc and os.environ.get("RC_ALL") == "1":
            # (shard A, 2026-11-17) research's xray_delay.py and prjxray's own model add the one RC term to every
            # corner; the default below keeps the historical choice (upper ends only, a wider band) for the proofs
            fidelity["pip RC (Elmore, R * downstream C) added to all four corners (RC_ALL=1)"] += 1
            return {"fmin": d[0] + rc, "fmax": d[1] + rc, "smin": d[2] + rc, "smax": d[3] + rc}
        if rc:
            fidelity["pip RC (Elmore, R * downstream C) added to the upper ends only"] += 1
        return {"fmin": d[0], "fmax": d[1] + rc, "smin": d[2], "smax": d[3] + rc}

    Z = {"fmin": 0, "fmax": 0, "smin": 0, "smax": 0}
    const_node = {}

    def const_src(val):
        nm = "CONST%d" % int(bool(val))
        if nm not in const_node:
            const_node[nm] = node(nm)
            add_gate({"name": nm, "kind": "const", "k": 0, "init": 1 if val else 0, "ins": [], "arcs": [],
                      "out": const_node[nm], "prov": None})
        return const_node[nm]

    hop_done = set()

    def route_in(v, what):
        """The node a pin reads, adding the gates of its route (pips, the hop from the
        source's site-internal net, or a constant)."""
        if not isinstance(v, dict):
            die("%s: bad pin %r" % (what, v))
        r = v.get("_route")
        if r is None:
            if "const" in v:
                return const_src(v["const"])
            return node(v["net"])
        for t, dw, sw, ps, sn, dn in r["pips"]:
            add_gate({"name": "%s.%s.%s" % (t, dw, sw), "kind": "pip", "k": 1, "init": 2, "ins": [node(sn)],
                      "arcs": [pip_arc(t, dw, sw, dn)], "out": node(dn),
                      "prov": {"tile": t, "dst": dw, "src": sw, "pseudo": ps}})
        src = r["srcnode"]
        if "const" in v:
            # the route starts at a VCC_WIRE / GND_WIRE tie: that node is the constant
            if src not in hop_done:
                hop_done.add(src)
                add_gate({"name": src, "kind": "const", "k": 0, "init": 1 if v["const"] else 0, "ins": [],
                          "arcs": [], "out": node(src), "prov": {"tie": src}})
        elif src not in hop_done:
            hop_done.add(src)
            add_gate({"name": "hop " + src, "kind": "hop", "k": 1, "init": 2, "ins": [node(v["net"])],
                      "arcs": [hop_arc(src, r, v["net"]) if RC_TREE else dict(Z)], "out": node(src),
                      "prov": {"srcpin": r["srcpin"], "net": v["net"]}})
            if not RC_TREE:
                fidelity["site output hop, arc 0 (in the BEL arc, prjxray)"] += 1
        return node(r["sink"])

    def sitepin_delay(v):
        r = v.get("_route") if isinstance(v, dict) else None
        if not r:
            return [0, 0, 0, 0]
        t, w = r["sinkwire"]
        sp = tt(t)["_sp"].get(w)
        d = ps4(sp[2].get("delay")) if sp else None
        return d or [0, 0, 0, 0]

    def site_of(name):
        """'SLICE_X22Y88.ALUT' -> tile, tile type, site type."""
        sn = name.split(".")[0]
        for t, g in tiles.items():
            if sn in g.get("sites", {}):
                return t, g["type"], g["sites"][sn]
        die("site %s not found" % sn)

    site_cache = {}

    def site(name):
        sn = name.split(".")[0]
        if sn not in site_cache:
            site_cache[sn] = site_of(name)
        return site_cache[sn]

    def arc_of(d):
        return {"fmin": d[0], "fmax": d[1], "smin": d[2], "smax": d[3]}

    def add(a, b):
        return [x + y for x, y in zip(a, b)]

    opaque = []
    for c in sorted(D["cells"], key=lambda c: c["name"]):
        kind, name = c["kind"], c["name"]
        if kind == "lut6_2":
            t, ttype, stype = site(name)
            L = name.split(".")[1][0]
            ins = [route_in(c["conn"]["I%d" % i], "%s I%d" % (name, i)) for i in range(6)]
            sp = [sitepin_delay(c["conn"]["I%d" % i]) for i in range(6)]
            a6, a5 = [], []
            for i in range(6):
                p6 = iopath(ttype, stype, "%s6LUT" % L, "A%d" % (i + 1), "O6")
                if p6 is None:
                    die("%s: no IOPATH A%d O6" % (name, i + 1))
                a6.append(arc_of(add(sp[i], p6)))
                if i < 5:
                    p5 = iopath(ttype, stype, "%s5LUT" % L, "A%d" % (i + 1), "O5")
                    if p5 is None:
                        die("%s: no IOPATH A%d O5" % (name, i + 1))
                    a5.append(arc_of(add(sp[i], p5)))
            add_gate({"name": name + ".O6", "kind": "lut6", "k": 6, "init": c["init"], "ins": ins, "arcs": a6,
                      "out": node(c["outs"]["O6"]), "prov": {"site": name.split(".")[0], "lut": L, "tile": t}})
            add_gate({"name": name + ".O5", "kind": "lut5", "k": 5, "init": c["init"] & 0xFFFFFFFF,
                      "ins": ins[:5], "arcs": a5, "out": node(c["outs"]["O5"]),
                      "prov": {"site": name.split(".")[0], "lut": L, "tile": t, "o5": True}})
        elif kind in ("muxf7", "muxf8"):
            t, ttype, stype = site(name)
            sub = name.split(".")[1]
            inst = {"F7A": "F7AMUX", "F7B": "F7BMUX", "F8": "F8MUX"}[sub]
            ins = [route_in(c["conn"][p], name + " " + p) for p in ("I0", "I1", "S")]
            arcs = []
            for p, sp_ in (("0", "I0"), ("1", "I1"), ("S0", "S")):
                d = iopath(ttype, stype, inst, p, "OUT")
                if d is None:
                    die("%s: no IOPATH %s OUT" % (name, p))
                arcs.append(arc_of(add(sitepin_delay(c["conn"][sp_]), d)))
            add_gate({"name": name, "kind": "muxf", "k": 3, "init": 0xCA, "ins": ins, "arcs": arcs,
                      "out": node(c["outs"]["O"]), "prov": {"site": name.split(".")[0], "mux": sub}})
        elif kind == "carry4":
            t, ttype, stype = site(name)
            cv = c["conn"]
            ci = route_in(cv["CI"], name + " CI")
            cy = route_in(cv["CYINIT"], name + " CYINIT")
            S = [route_in(cv["S%d" % i], "%s S%d" % (name, i)) for i in range(4)]
            DI = [route_in(cv["DI%d" % i], "%s DI%d" % (name, i)) for i in range(4)]
            for i in range(4):
                for o in ("CO", "O"):
                    nd = i + 1 if o == "CO" else i     # DI0..DI(nd-1) matter
                    pins = [("CIN", ci, cv["CI"]), ("CYINIT", cy, cv["CYINIT"])] + \
                           [("S%d" % j, S[j], cv["S%d" % j]) for j in range(i + 1)] + \
                           [("DI%d" % j, DI[j], cv["DI%d" % j]) for j in range(nd)]
                    k = len(pins)
                    init = 0
                    for a in range(2 ** k):
                        b = [(a >> q) & 1 for q in range(k)]
                        cin, cyi = b[0], b[1]
                        s = b[2:3 + i]
                        di = b[3 + i:]
                        cc = cin | cyi
                        for j in range(i):
                            cc = cc if s[j] else di[j]
                        val = (cc if s[i] else di[i]) if o == "CO" else (s[i] ^ cc)
                        if val:
                            init |= 1 << a
                    arcs = []
                    for pn, _, pv in pins:
                        if isinstance(pv, dict) and "const" in pv and "_route" not in pv:
                            arcs.append(dict(Z))
                            continue
                        d = iopath(ttype, stype, None, pn, "%s%d" % (o, i), celltypes=["CARRY4"])
                        if d is None:
                            die("%s: no IOPATH %s %s%d" % (name, pn, o, i))
                        arcs.append(arc_of(add(sitepin_delay(pv), d)))
                    ciV, cyV = cv["CI"], cv["CYINIT"]
                    precy = ("CIN" if "_route" in ciV else
                             "AX" if "_route" in cyV else ("C1" if cyV.get("const") else "C0"))
                    cy0 = [isinstance(cv["DI%d" % j], dict) and "_route" not in cv["DI%d" % j]
                           and str(cv["DI%d" % j].get("net", "")).endswith("5") for j in range(4)]
                    add_gate({"name": "%s.%s%d" % (name, o, i), "kind": "carry", "k": k, "init": init,
                              "ins": [p[1] for p in pins], "arcs": arcs,
                              "out": node(c["outs"]["%s%d" % (o, i)]),
                              "prov": {"site": name.split(".")[0], "precy": precy, "cy0": cy0}})
            fidelity["CARRY4 output as one gate over its inputs (IOPATH per pin; DI: envelope of variants)"] += 8
        else:
            # flip-flops, BUFG/BUFHCE, BSCAN: no gate; their output nets are free nodes. Their
            # input routes are still added (the pips conduct).
            for p, v in c["conn"].items():
                if isinstance(v, dict) and "_route" in v:
                    route_in(v, name + " " + p)
            opaque.append({"name": name, "kind": kind, "outs": c["outs"]})
            fidelity["no gate (output free): " + kind] += 1

    # active pips not on any walked route still conduct: add them
    feats = set()
    for line in open(fasm_path):
        line = line.split("#")[0].strip()
        if line:
            feats.add(line)
    extra = 0
    import importlib.util
    here = os.path.dirname(os.path.abspath(__file__))
    spec = importlib.util.spec_from_file_location("db", os.path.join(here, "decode_base.py"))
    DBm = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(DBm)
    fab = DBm.Fabric3()

    def nname(nd):
        t, w = min(nd)
        return "%s/%s" % (t, w)
    for f in sorted(feats):
        parts = f.split(".")
        if len(parts) == 3 and parts[0] in tiles:
            t, dw, sw = parts
            if (dw, sw) in tt(t)["_by"] and (t, dw, sw) not in pips_on:
                sn, dn = nname(fab.node(t, sw)), nname(fab.node(t, dw))
                add_gate({"name": f, "kind": "pip", "k": 1, "init": 2, "ins": [node(sn)],
                          "arcs": [pip_arc(t, dw, sw, dn)], "out": node(dn),
                          "prov": {"tile": t, "dst": dw, "src": sw, "pseudo": False, "untraced": True}})
                extra += 1
    fidelity["active pip on no walked route (added)"] = extra

    out = {"nodes": [n for n, _ in sorted(nodes.items(), key=lambda kv: kv[1])], "gates": gates,
           "opaque": opaque, "fidelity": dict(fidelity), "fasm": os.path.abspath(fasm_path)}
    json.dump(out, open(outp, "w"))
    kinds = defaultdict(int)
    for g in gates:
        kinds[g["kind"]] += 1
    print("build_net: %d nodes, %d gates %s, %d opaque" % (len(nodes), len(gates), dict(kinds), len(opaque)),
          file=sys.stderr)
    for k, v in sorted(fidelity.items()):
        print("  fidelity: %s: %d" % (k, v), file=sys.stderr)


if __name__ == "__main__":
    main()
