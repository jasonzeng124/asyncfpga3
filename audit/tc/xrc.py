#!/usr/bin/env python3
"""Auditor's own prjxray RC-tree delay model for a nextpnr-xilinx routed JSON.

Independent of formal/tools/tcheck (no import of extract.py / prjxdelay / fasm2lean).
Model = prjxray/timing.py semantics (Outpin -> Wire(pi) -> Buffer|PassTransistor -> Wire ... -> Inpin):
  sink delay[corner] = sum(intrinsic[corner] of outpin, pips, inpin) + sum(R_drive * C_downstream)
  corners = (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX) as prjxray's 4-tuples; RC is corner independent.
  Units: res ohm, cap fF -> 1e-15 s = 1e-3 ps.
Node membership (which tile wires form one electrical node) is expanded from tileconn.json.
nextpnr wires that lie in one prjxray node (e.g. INT IMUX_L15 and CLBLM_M_B1) are merged.
The physical LUT pin is the CLB tile wire feeding the site (e.g. CLBLM_M_B1 -> site pin B1);
the SITEWIRE name after it is nextpnr's BEL pin (after LUT pin permutation)."""
import json, os, re, sys
from collections import defaultdict

DB = os.path.join(os.environ.get("PRJXRAY_DB_DIR", "/root/dev2/lib/fpgatoolchain/openxc7/share/nextpnr/prjxray-db"), "zynq7")
RCU = 1e-3  # ohm*fF -> ps


def f4(d):
    return [float(x) * 1000 for x in d] if d else [0.0] * 4


class DBx:
    def __init__(self, part="xc7z010"):
        tg = json.load(open(f"{DB}/{part}/tilegrid.json"))
        self.ttype = {k: v["type"] for k, v in tg.items()}
        self.at = {(v["grid_x"], v["grid_y"]): k for k, v in tg.items()}
        self.xy = {k: (v["grid_x"], v["grid_y"]) for k, v in tg.items()}
        self.tsites = {k: v.get("sites", {}) for k, v in tg.items()}
        self.tt = {}
        self.conn = defaultdict(list)  # (type, wire) -> [(dx, dy, type2, wire2)]
        for e in json.load(open(f"{DB}/{part}/tileconn.json")):
            (dx, dy), (ta, tb) = e["grid_deltas"], e["tile_types"]
            for wa, wb in e["wire_pairs"]:
                self.conn[(ta, wa)].append((dx, dy, tb, wb))
                self.conn[(tb, wb)].append((-dx, -dy, ta, wa))
        self.ncache = {}

    def ttj(self, t):
        if t not in self.tt:
            p = f"{DB}/tile_type_{t}.json"
            d = json.load(open(p)) if os.path.exists(p) else {"wires": {}, "pips": {}, "sites": []}
            pins = {}
            for s in d["sites"]:
                for pn, pv in s["site_pins"].items():
                    if pv and "wire" in pv:
                        pins[pv["wire"]] = (pn, pv)
            pips = {}
            for k, v in d["pips"].items():
                pips[(v["src_wire"], v["dst_wire"])] = v
            d["_pins"], d["_pips"] = pins, pips
            self.tt[t] = d
        return self.tt[t]

    def node(self, tile, wire):
        key = (tile, wire)
        if key in self.ncache:
            return self.ncache[key]
        seen, todo = {key}, [key]
        while todo:
            t, w = todo.pop()
            x, y = self.xy[t]
            for dx, dy, t2, w2 in self.conn.get((self.ttype[t], w), ()):
                n = self.at.get((x + dx, y + dy))
                if n and self.ttype[n] == t2 and (n, w2) not in seen:
                    seen.add((n, w2)); todo.append((n, w2))
        fs = frozenset(seen)
        for k in seen:
            self.ncache[k] = fs
        return fs

    def node_rc(self, node):
        r = c = 0.0
        for t, w in node:
            v = self.ttj(self.ttype[t])["wires"].get(w)
            if v:
                r += float(v.get("res", 0) or 0); c += float(v.get("cap", 0) or 0)
        return r, c

    def find_pip(self, na, nb):
        """the prjxray pip from node na to node nb: (tile, src, dst, data)"""
        by = defaultdict(list)
        for t, w in na:
            by[t].append(w)
        for t, wb in nb:
            if t in by:
                P = self.ttj(self.ttype[t])["_pips"]
                for wa in by[t]:
                    if (wa, wb) in P:
                        return t, wa, wb, P[(wa, wb)]
        return None


def split_tw(s):
    t, w = s.split("/", 1)
    return t, w


class Net:
    """RC tree of one routed net. sinks: list of dict(site, belpin, phys, tilewire, d[4], path=[node ids])"""

    def __init__(self, X, routing):
        f = routing.split(";")
        par = {}
        for i in range(0, len(f) - 2, 3):
            par[f[i]] = f[i + 1]
        self.X, self.ok, self.why = X, True, ""
        self.sinks = []
        # build children map on nextpnr wires
        kids = defaultdict(list)
        root = None
        for w, p in par.items():
            if not p:
                root = w; continue
            if p.startswith("SITEPIP/"):
                # site-internal: parent is the sitewire named by the pip input
                m = re.match(r"SITEPIP/([^/]+)/([^/]+)/(.+)$", p)
                src = f"SITEWIRE/{m.group(1)}/{m.group(3)}"
                kids[src].append((w, p)); continue
            a, b = p.split("->")
            kids[a].append((w, p))
        self.root = root
        # find outpin crossing: SITEWIRE -> tile wire
        self.outs = []
        stack = [(root, [])]
        while stack:
            w, sp = stack.pop()
            for c, p in kids.get(w, ()):
                if w.startswith("SITEWIRE/") and not c.startswith("SITEWIRE/"):
                    self.outs.append((w, c, sp))
                elif c.startswith("SITEWIRE/"):
                    stack.append((c, sp + [p]))
        if not self.outs:
            self.ok, self.why = False, "no outpin"; return
        self.kids = kids
        self.elems, self.n = {}, 0
        for o in self.outs:
            self.out = o
            self._build()

    def _build(self):
        X = self.X
        sw, tw, sitepips = self.out
        t, w = split_tw(tw)
        pins = X.ttj(X.ttype[t])["_pins"]
        if w not in pins:
            self.ok, self.why = False, f"outpin {tw} not a site pin"; return
        pn, pv = pins[w]
        self.out_name = pn
        self.out_res = float(pv.get("res", 0) or 0)
        self.out_d = f4(pv.get("delay"))
        # intra-site OUTMUX (ROUTING_BEL) for ?MUX outputs
        self.mux = [0.0] * 4
        m = re.fullmatch(r"([A-D])MUX", pn)
        if m:
            src = None
            for sp in sitepips:
                mm = re.match(r"SITEPIP/([^/]+)/([A-D])OUTMUX/(.+)$", sp)
                if mm:
                    x = mm.group(3)
                    x = re.sub(r"_(O[56]|OUT|Q)$", "", x) if not x.startswith("CARRY4") else x
                    src = x.lower()
            site = sw.split("/")[1]
            tab = site_type_sdf(route_site_type(X, site))
            v = tab.get((f"{m.group(1)}MUX", src, f"{m.group(1).lower()}mux")) if src else None
            if v is None:
                self.ok, self.why = False, f"outmux {pn} {sitepips}"
            else:
                self.mux = v
        if os.environ.get("XRC_NOMUX"):  # reproduce a model without the OUTMUX routing-bel delay
            self.mux = [0.0] * 4
        self.out_d = [self.out_d[j] + self.mux[j] for j in range(4)]

        def new(kind, **kw):
            self.n += 1; kw["kind"] = kind; kw["ch"] = []; self.elems[self.n] = kw; return self.n

        rootw = new("wire", node=X.node(t, w))
        self.rootw = rootw

        def walk(nw, eid):  # nextpnr wire nw already represented by element eid (a wire)
            for c, p in self.kids.get(nw, ()):
                if c.startswith("SITEWIRE/"):
                    # inpin crossing: nw is a tile wire = physical site pin
                    tt, ww = split_tw(nw)
                    pins = X.ttj(X.ttype[tt])["_pins"]
                    if ww not in pins:
                        self.ok, self.why = False, f"inpin {nw}"; continue
                    pn, pv = pins[ww]
                    i = new("in", pin=pn, tilewire=nw, sitewire=c, cap=float(pv.get("cap", 0) or 0), d=f4(pv.get("delay")))
                    self.elems[eid]["ch"].append(i)
                    continue
                tt, ww = split_tw(c)
                nb = X.node(tt, ww)
                if nb == self.elems[eid]["node"]:
                    walk(c, eid); continue
                pp = X.find_pip(self.elems[eid]["node"], nb)
                rev = False
                if pp is None:
                    pp = X.find_pip(nb, self.elems[eid]["node"]); rev = True
                    if pp is None or pp[3].get("is_directional") != "0":
                        self.ok, self.why = False, f"no pip {p}"; continue
                s2d = pp[3]["dst_to_src" if rev else "src_to_dst"]
                ispt = int(pp[3]["is_pass_transistor"]) == 1
                e = new("pt" if ispt else "buf", name=f"{pp[0]}.{pp[1]}->{pp[2]}", res=float(s2d.get("res") or 0),
                        incap=float(s2d.get("in_cap") or 0), d=f4(s2d.get("delay")))
                self.elems[eid]["ch"].append(e)
                wi = new("wire", node=nb)
                self.elems[e]["ch"].append(wi)
                walk(c, wi)

        walk(tw, rootw)
        # downstream caps
        def cap_up(i):  # capacitance seen by the parent of element i
            e = self.elems[i]
            k = e["kind"]
            if k == "in":
                return e["cap"]
            if k == "wire":
                r, c = X.node_rc(e["node"]); e["r"], e["c"] = r, c
                dn = sum(cap_up(j) for j in e["ch"])
                e["dcap"] = c / 2 + dn
                return dn + c
            if k == "buf":
                e["dcap"] = cap_up(e["ch"][0]); return e["incap"]
            if k == "pt":
                e["dcap"] = cap_up(e["ch"][0]); return e["dcap"]
        total = cap_up(rootw)
        out_rc = self.out_res * total * RCU
        # propagate delays
        def prop(i, acc, path):
            e = self.elems[i]
            k = e["kind"]
            path = path + [i]
            if k == "in":
                d = [acc[j] + e["d"][j] for j in range(4)]
                self.sinks.append(dict(outpin=self.out_name, mux=self.mux, pin=e["pin"], tilewire=e["tilewire"], sitewire=e["sitewire"], d=d,
                                       sitepin=e["d"], path=path))
                return
            if k == "wire":
                add = e["r"] * e["dcap"] * RCU
                acc = [a + add for a in acc]
            else:
                add = e["res"] * e["dcap"] * RCU
                acc = [acc[j] + e["d"][j] + add for j in range(4)]
            e["acc"] = acc  # delay at this element's output (after its RC)
            for j in e["ch"]:
                prop(j, acc, path)
        prop(rootw, [self.out_d[j] + out_rc for j in range(4)], [])

    def elem_delay_to(self, path_prefix_last):
        """delay (4 corners) at the OUTPUT of element id (inclusive of its RC/intrinsic) from the driver"""
        return self.elems[path_prefix_last]["acc"]


class Route:
    def __init__(self, odir, X=None):
        self.X = X or DBx()
        js = [f for f in os.listdir(odir) if f.endswith("_routed.json")][0]
        sdf = [f for f in os.listdir(odir) if f.endswith(".sdf")][0]
        top = [m for m in json.load(open(os.path.join(odir, js)))["modules"].values()
               if m.get("attributes", {}).get("top")][0]
        self.cells = top["cells"]
        self.routes = {}
        for nm, nn in top["netnames"].items():
            r = nn.get("attributes", {}).get("ROUTING")
            if r and nn["bits"]:
                self.routes.setdefault(nn["bits"][0], r)
        self.driver, self.sinks_of = {}, defaultdict(list)
        for cn, c in self.cells.items():
            for p, d in c.get("port_directions", {}).items():
                for b in c["connections"].get(p, []):
                    if d == "output":
                        self.driver[b] = (cn, p)
                    else:
                        self.sinks_of[b].append((cn, p))
        # SDF
        self.ic, self.io = {}, {}
        RI = re.compile(r"\(INSTANCE\s+(\S*?)\)")
        RO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):")
        RC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):")
        inst = None
        un = lambda s: s.replace("\\", "")
        for line in open(os.path.join(odir, sdf)):
            m = RC.search(line)
            if m:
                self.ic[(un(m.group(1)), un(m.group(2)))] = int(m.group(3)); continue
            m = RI.search(line)
            if m:
                inst = un(m.group(1)); continue
            m = RO.search(line)
            if m and inst:
                self.io[(inst, m.group(1), m.group(2))] = int(m.group(3))
        self.ncache = {}

    def net(self, bit):
        if bit not in self.ncache:
            r = self.routes.get(bit)
            self.ncache[bit] = Net(self.X, r) if r else None
        return self.ncache[bit]

    def sink_of_cellpin(self, cn, port):
        """the routed sink (dict) feeding cell cn's input port: matched through the site wire.
        LUT cells: SITEWIRE/<site>/<L><k> for BEL pin A<k>. Returns (net, sink) or (net, None)."""
        c = self.cells[cn]
        b = c["connections"][port][0]
        n = self.net(b)
        if n is None or not n.ok:
            return n, None
        bel = c["attributes"].get("NEXTPNR_BEL", "")
        site, belname = bel.split("/")
        m = re.fullmatch(r"([A-D])[56]LUT", belname)
        if m and re.fullmatch(r"A[1-6]", port):
            want = re.compile(r"SITEWIRE/%s/%s[1-6]$" % (re.escape(site), m.group(1)))
            hits = [s for s in n.sinks if want.match(s["sitewire"])]
            return n, (hits[0] if len(hits) == 1 else None)
        return n, None

    def lut_arc(self, cn, port, out="O6"):
        """prjxray LUT cell arc for the PHYSICAL pin feeding (cn, port) -> out, 4 corners (ps)"""
        n, s = self.sink_of_cellpin(cn, port)
        if s is None:
            return None
        bel = self.cells[cn]["attributes"]["NEXTPNR_BEL"]
        site = bel.split("/")[0]
        return lut_iopath(self.X, site, bel.split("/")[1][0], s["pin"], out)


_SDF = {}


def site_type_sdf(sitetype):
    """prjxray timing sdf for SLICEL/SLICEM: {(bel, from, to): [fmin,fmax,smin,smax] ps}"""
    if sitetype in _SDF:
        return _SDF[sitetype]
    out, bel = {}, None
    for line in open(f"{DB}/timings/{sitetype.lower()}.sdf"):
        m = re.search(r"\(INSTANCE\s+[^/)]+/?([^)]*)\)", line)
        if m:
            bel = m.group(1); continue
        m = re.search(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\(([\d.]+)::([\d.]+)\)\s*\(([\d.]+)::([\d.]+)\)", line)
        if m:
            out.setdefault((bel, m.group(1), m.group(2)), [float(m.group(i)) * 1000 for i in (3, 4, 5, 6)])
        m = re.search(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\(([\d.]+)::([\d.]+)\)\s*\(([\d.]+)::([\d.]+)\)", line)
        if m:
            out.setdefault((bel, m.group(1), m.group(2)), [float(m.group(i)) * 1000 for i in (3, 4, 5, 6)])
    _SDF[sitetype] = out
    return out


_STY = {}


def route_site_type(X, site):
    if not _STY:
        for t, ss in X.tsites.items():
            _STY.update(ss)
    return _STY[site]


def lut_iopath(X, site, letter, physpin, out):
    """physpin e.g. 'B3' (site pin) -> LUT input A3 of <letter>6LUT/<letter>5LUT"""
    tab = site_type_sdf(route_site_type(X, site))
    bel = f"{letter}{'6' if out == 'O6' else '5'}LUT"
    return tab.get((bel, f"A{physpin[1]}", out))


# ---- non-LUT extensions (MUXF7/F8 = SELMUX2_1): select pin nets, in-site LUT->F7 / F7->F8 hops, cell arcs ----
F7PIN = {"F7AMUX": "AX", "F7BMUX": "CX", "F8MUX": "BX"}


def _bel(R, cn):
    return R.cells[cn]["attributes"].get("NEXTPNR_BEL", "/").split("/")


def route_arc(R, src, dst):
    """model value [4] for one SDF arc (src pin -> dst pin), or None when not modelled"""
    cs, ps = src.rsplit("/", 1)
    cd, pd = dst.rsplit("/", 1)
    if cs not in R.cells or cd not in R.cells:
        return None
    ts, td = R.cells[cs]["type"], R.cells[cd]["type"]
    if cs == cd and R.cells[cs]["port_directions"].get(ps) == "input":  # cell arc
        if "LUT" in ts and re.fullmatch(r"A[1-6]", ps):
            return R.lut_arc(cs, ps, pd)
        if ts == "SELMUX2_1" and pd == "OUT":
            site, bel = _bel(R, cs)
            return site_type_sdf(route_site_type(R.X, site)).get((bel, ps, "OUT"))
        return None
    b = R.cells[cd]["connections"].get(pd, [None])[0]
    if R.driver.get(b) != (cs, ps):
        return None
    if "LUT" in td and re.fullmatch(r"A[1-6]", pd):
        n, s = R.sink_of_cellpin(cd, pd)
        return s["d"] if (s is not None and n.ok) else None
    if td == "SELMUX2_1":
        site, bel = _bel(R, cd)
        if pd in ("0", "1"):
            if "LUT" in ts:  # in-site LUT -> F7 hop (ROUTING_BEL)
                lb = _bel(R, cs)[1]
                return site_type_sdf(route_site_type(R.X, site)).get((bel, lb[0].lower() + "6lut", bel.lower()))
            if ts == "SELMUX2_1":  # F7 -> F8: no db entry (SDF 0)
                return [0.0] * 4
            return None
        if pd == "S0":
            n = R.net(b)
            if n is None or not n.ok:
                return None
            hits = [s for s in n.sinks if s["pin"] == F7PIN.get(bel) and s["sitewire"].split("/")[1] == site]
            return hits[0]["d"] if len(hits) == 1 else None
    return None
