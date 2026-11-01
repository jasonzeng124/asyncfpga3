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

    def pip_arc(t, dw, sw, dn):
        p, rev = tt(t)["_by"][(dw, sw)]
        s2d = (p.get("dst_to_src") if rev else p.get("src_to_dst")) or {}
        d = ps4(s2d.get("delay"))
        if d is None:
            d = [0, 0, 0, 0]
            fidelity["pip with no delay data (prjxray: none), arc 0"] += 1
        r = float(s2d.get("res") or 0)
        rc = int(-(-r * load_star(dn) * 1e-3 // 1))   # ceil, ps
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
                      "arcs": [dict(Z)], "out": node(src), "prov": {"srcpin": r["srcpin"], "net": v["net"]}})
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
                    add_gate({"name": "%s.%s%d" % (name, o, i), "kind": "carry", "k": k, "init": init,
                              "ins": [p[1] for p in pins], "arcs": arcs,
                              "out": node(c["outs"]["%s%d" % (o, i)]), "prov": {"site": name.split(".")[0]}})
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
