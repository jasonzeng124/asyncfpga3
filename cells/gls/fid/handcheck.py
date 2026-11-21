#!/usr/bin/env python3
"""
handcheck.py -- recompute one net's sink delays BY HAND from the raw
prjxray-db JSON numbers, independently of prjxray/timing.py and of
xray_delay.py's tree plumbing, and print both.

    PYTHONPATH=$PRJXRAY python3 cells/gls/fid/handcheck.py ROUTED.json NET [NET...]
        [--prune-to SINKWIRE]   keep only the branch to one sink (loading control)

What is shared with xray_delay.py: the node model (which tile wires form a
node) and the pip resolution (which tile pip joins two nodes) -- the hand
check prints both so they can be read off.  What is NOT shared: the numbers
(read here straight from tile_type_*.json, in ohms / fF / ns) and the Elmore
arithmetic (written out here as the textbook sum: each driver's R times the
total capacitance it sees downstream, each wire's R times half its own C plus
everything downstream).
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import xray_delay as X  # noqa: E402

DB = X.DB_ROOT
_raw = {}


def raw(tt):
    if tt not in _raw:
        _raw[tt] = json.load(open(os.path.join(DB, "tile_type_%s.json" % tt)))
    return _raw[tt]


def raw_wire_rc(tile, wire, xdb):
    v = raw(xdb.tile_type(tile))["wires"].get(wire)
    return (float(v["res"]), float(v["cap"])) if v else (0.0, 0.0)


def raw_node_rc(node, xdb):
    rs = cs = 0.0
    lv = any(w.startswith("LV") for _, w in xdb.nodes[node])
    n = 0
    for t, w in xdb.nodes[node]:
        r, c = raw_wire_rc(t, w, xdb)
        if r == 0 and c == 0:
            continue
        if lv and n >= 2:
            continue
        rs += r
        cs += c
        n += 1
    return rs, cs


def raw_pip(tile, pipname_src, pipname_dst, xdb):
    tt = xdb.tile_type(tile)
    for k, v in raw(tt)["pips"].items():
        if v["src_wire"] == pipname_src and v["dst_wire"] == pipname_dst:
            s = v["src_to_dst"]
            return k, v, s
        if v["src_wire"] == pipname_dst and v["dst_wire"] == pipname_src and v["is_directional"] == "0":
            return k, v, v["dst_to_src"]
    return None


def raw_sitepin(tile, wire, xdb):
    for s in raw(xdb.tile_type(tile))["sites"]:
        for name, p in s["site_pins"].items():
            if p and p.get("wire") == wire:
                return name, p
    return None


def f4(d):
    return [float(x) for x in d] if d else [0.0] * 4


class N(object):
    """hand tree node: kind in outpin/wire/buf/pt/inpin."""

    def __init__(self, kind, name, R=0.0, C=0.0, d=None):
        self.kind, self.name, self.R, self.C = kind, name, R, C
        self.d = d or [0.0] * 4
        self.kids = []

    def load(self):
        """capacitance this element presents upstream (fF)."""
        if self.kind == "buf":
            return self.C
        if self.kind == "inpin":
            return self.C
        if self.kind == "pt":
            return sum(k.load() for k in self.kids)
        if self.kind == "wire":
            return self.C + sum(k.load() for k in self.kids)
        raise ValueError

    def rc(self):
        """Elmore term of this element, in ohm*fF (=1e-6 ns)."""
        down = sum(k.load() for k in self.kids)
        if self.kind == "wire":
            return self.R * (self.C / 2 + down)
        if self.kind in ("outpin", "buf", "pt"):
            return self.R * down
        return 0.0


def build(xdb, par, keep=None):
    children = {}
    root = None
    for w, p in par.items():
        if p == "":
            root = w
        else:
            children.setdefault(X.pip_parent(p), []).append(w)
    if keep:
        # prune: keep only the wires on the path root -> keep
        path = set()
        w = keep
        while w:
            path.add(w)
            p = par[w]
            w = X.pip_parent(p) if p else None
        children = {k: [c for c in v if c in path] for k, v in children.items()}
    roots, sinks = [], {}

    def tile_walk(w, node, wnode):
        for c in children.get(w, ()):
            if c.startswith("SITEWIRE/"):
                tile, wire = w.split("/", 1)
                name, sp = raw_sitepin(tile, wire, xdb)
                ip = N("inpin", "%s pin %s" % (w, name), C=float(sp.get("cap", 0)), d=f4(sp["delay"]))
                wnode.kids.append(ip)
                sinks[c] = ip
                stack = [c]
                while stack:
                    s = stack.pop()
                    sinks[s] = ip
                    stack += children.get(s, [])
                continue
            ct, cw = c.split("/", 1)
            cn = xdb.node_of(ct, cw)
            if cn == node:
                tile_walk(c, node, wnode)
                continue
            tile, pip, back = xdb.resolve_pip(node, cn)
            src, dst = (pip.net_to, pip.net_from) if back else (pip.net_from, pip.net_to)
            k, v, s = raw_pip(tile, src, dst, xdb)
            pt = int(v["is_pass_transistor"])
            e = N("pt" if pt else "buf", "%s/%s" % (tile, k), R=float(s.get("res") or 0),
                  C=float(s.get("in_cap") or 0), d=f4(s.get("delay")))
            wnode.kids.append(e)
            R, C = raw_node_rc(cn, xdb)
            nw = N("wire", "node %s/%s (%d tile wires)" % (cn[0], cn[1], len(xdb.nodes[cn])), R=R, C=C)
            e.kids.append(nw)
            tile_walk(c, cn, nw)

    def site_walk(w):
        for c in children.get(w, ()):
            p = par[c]
            if p.startswith("SITEPIP/") or c.startswith("SITEWIRE/"):
                site_walk(c)
                continue
            tile, wire = c.split("/", 1)
            name, sp = raw_sitepin(tile, wire, xdb)
            op = N("outpin", "%s pin %s" % (c, name), R=float(sp["res"]), d=f4(sp["delay"]))
            node = xdb.node_of(tile, wire)
            R, C = raw_node_rc(node, xdb)
            nw = N("wire", "node %s/%s (%d tile wires)" % (node[0], node[1], len(xdb.nodes[node])), R=R, C=C)
            op.kids.append(nw)
            roots.append(op)
            tile_walk(c, node, nw)

    site_walk(root)
    return roots, sinks


def paths(roots):
    """-> {inpin: [elements root..inpin]}"""
    out = {}

    def rec(e, acc):
        acc = acc + [e]
        if e.kind == "inpin":
            out[id(e)] = acc
        for k in e.kids:
            rec(k, acc)
    for r in roots:
        rec(r, [])
    return out


def report(xdb, netname, par, keep=None, tool=None):
    roots, sinks = build(xdb, par, keep)
    P = paths(roots)
    print("=" * 100)
    print("net %s%s" % (netname, ("   [PRUNED to %s]" % keep) if keep else ""))
    seen = set()
    for sink_wire, ip in sorted(sinks.items()):
        if id(ip) in seen:
            continue
        seen.add(id(ip))
        el = P[id(ip)]
        print("-- sink %s" % ip.name)
        print("   %-7s %-62s %9s %8s %8s %8s %10s" % ("kind", "element", "R ohm", "C fF", "Cdown", "slowmax", "RC ps"))
        tot_d = [0.0] * 4
        tot_rc = 0.0
        for e in el:
            down = sum(k.load() for k in e.kids)
            rcps = e.rc() * 1e-6 * 1000          # ohm*fF -> ns -> ps
            tot_rc += rcps
            tot_d = [a + b for a, b in zip(tot_d, e.d)]
            print("   %-7s %-62s %9.1f %8.3f %8.3f %8.3f %10.2f" % (
                e.kind, e.name[-62:], e.R, e.C, down, e.d[3], rcps))
        print("   sum intrinsic (ns) FAST_MIN %.3f FAST_MAX %.3f SLOW_MIN %.3f SLOW_MAX %.3f ; "
              "Elmore RC %.2f ps" % (tot_d[0], tot_d[1], tot_d[2], tot_d[3], tot_rc))
        print("   HAND  slow-max total = %.1f ps   fast-min total = %.1f ps"
              % (tot_d[3] * 1000 + tot_rc, tot_d[0] * 1000 + tot_rc))
        if tool is not None:
            r = tool.delay_to([w for w, i in sinks.items() if i is ip][0])
            if r:
                tot, rc, npips, _, _ = r
                print("   TOOL  slow-max total = %.1f ps   fast-min total = %.1f ps   (site extra not in hand sum: %s)"
                      % ((tot[3] + rc) * 1000, (tot[0] + rc) * 1000,
                         "see OUTMUX" if any(x > 0 for x in tool.arrive[[w for w, i in sinks.items() if i is ip][0]][1]) else "0"))


def synthetic():
    """A pass-transistor chain, which no route here contains with non-zero
    values (every pass-transistor pip on the gcd and ipow routes is a CLB/DSP
    pin tie with R = 0 and no delay).  Built with prjxray/timing.py's own
    classes through xray_delay's math model, and computed by hand below.

        Outpin R=1000 ohm -> Wire(R=100, C=10 fF) -> PassTransistor R=500
        -> Wire(R=200, C=20) -> PassTransistor R=500 -> Wire(R=50, C=5)
        -> Inpin C=2 fF;  every intrinsic delay 0.

    Elmore (ohm*fF = 1e-3 ps):
      Outpin   1000 * (10+20+5+2)        = 37000
      Wire1     100 * (10/2 + 20+5+2)    =  3200
      PT1       500 * (20+5+2)           = 13500
      Wire2     200 * (20/2 + 5+2)       =  3400
      PT2       500 * (5+2)              =  3500
      Wire3      50 * (5/2 + 2)          =   225
      total                              = 60825 ohm*fF = 60.825 ps
    A buffer in place of PT1 (R=500, C_in=3 fF) isolates its downstream:
      Outpin 1000*(10+3)=13000, Wire1 100*(5+3)=800, Buf 500*(20+5+2)=13500,
      Wire2 3400, PT2 3500, Wire3 225 -> 34425 = 34.425 ps."""
    from prjxray.timing import Outpin, Wire, PassTransistor, Buffer, Inpin, RcElement
    k = 1e3   # prjxray/tile.py scale: ohm/1e3 * fF/1e3 = ns
    for kind, hand in (("pt", 60.825), ("buf", 34.425)):
        op = Outpin(resistance=1000 / k, delays=None)
        w1 = Wire([RcElement(100 / k, 10 / k)], X.MATH)
        op.set_sink_wire(w1)
        s1 = PassTransistor(500 / k, None) if kind == "pt" else Buffer(3 / k, 500 / k, None)
        w1.add_child(s1)
        w2 = Wire([RcElement(200 / k, 20 / k)], X.MATH)
        s1.set_sink_wire(w2)
        s2 = PassTransistor(500 / k, None)
        w2.add_child(s2)
        w3 = Wire([RcElement(50 / k, 5 / k)], X.MATH)
        s2.set_sink_wire(w3)
        ip = Inpin(2 / k, None)
        w3.add_child(ip)
        op.propigate_delays(X.MATH)
        rc = sum(e.get_rc_delay() or 0 for e in ip.get_delays()) * 1000
        print("synthetic %-4s chain: prjxray/timing.py %.3f ps, hand %.3f ps  %s"
              % (kind, rc, hand, "OK" if abs(rc - hand) < 1e-6 else "MISMATCH"))


def main():
    a = sys.argv[1:]
    if a == ["--synthetic"]:
        return synthetic()
    keep = None
    if "--prune-to" in a:
        i = a.index("--prune-to")
        keep = a[i + 1]
        del a[i:i + 2]
    routed, names = a[0], a[1:]
    xdb = X.XrayDb()
    X.CELLARCS = X.CellArcs(xdb)
    top = json.load(open(routed))["modules"]["top"]
    import collections
    for n in names:
        r = top["netnames"][n]["attributes"]["ROUTING"]
        par = X.parse_routing(r)
        if keep:
            path, w = {}, keep
            while w:
                path[w] = par[w]
                w = X.pip_parent(par[w]) if par[w] else None
            par = path                     # the route with every other branch removed
        st = collections.Counter()
        tool = X.NetTiming(xdb, par, 0.0, st)   # site pips 0 so the hand sum and tool compare like for like
        report(xdb, n, par, keep, tool)


if __name__ == "__main__":
    main()
