"""Causal back-trace of a full-stack GLS run (cells/gls/ps/build_ps.sh ... bit, GLS_MODEL=fid).

Input: a WORK dir holding netlist_baked.v (gen.py's netlist: cells c_*, nets n*, per-sink ICBUF ic_* carrying the
routed wire delay D), nets.map (n* -> routed-JSON net name) and dump.vcd (every n* net of the top, see dump.v).
Every primitive of the fid model is a TRANSPORT delay per (input pin, output) arc (cells/gls/fid_core.vh,
prims.v), so an output edge at t has exactly one cause: an input-net edge at t_src with t_src + D(wire) + arc == t.
cause() finds it and returns the slack (t - t_src - D - arc); a hop is "exact" when slack == 0.  Flops: Q's cause
is the CK (or async SR) edge, arc TCKQ (prims.v GLS_FID SLICE_FFX: pin copy AK + node->Q TCKQ-AK).  Latches
(SLICE_LATX): CK/D/SR, arc TCKQ (TDQ/TSRQ default to TCKQ; the node evaluates 1 ps after the pin copy lands, and
the arcs are shortened by that 1 ps, so the total is still TCKQ).
"""
import re, bisect, collections

RE_INST = re.compile(r"^\s*(\w+)\s*(?:#\((.*?)\))?\s+(\w+)\s*\((.*)\);\s*$")
OUTS = {"SLICE_LUTX": ("O5", "O6"), "SELMUX2_1": ("OUT",), "SLICE_FFX": ("Q",), "SLICE_LATX": ("Q",),
        "CARRY4": ("O0", "O1", "O2", "O3", "CO0", "CO1", "CO2", "CO3"), "BUFGCTRL": ("O",),
        "IOB33_OUTBUF": ("OUT",), "IOB33_INBUF_EN": ("OUT",), "PSEUDO_GND": ("Y",), "PSEUDO_VCC": ("Y",)}


def prims_defaults(path):
    s = open(path).read(); d = collections.defaultdict(dict)
    for m in re.finditer(r"module (\w+)\s*\((.*?)endmodule", s, re.S):
        for pm in re.finditer(r"parameter\s+([^;]*);", m.group(2)):
            for kv in pm.group(1).split(","):
                mm = re.match(r"\s*(?:integer\s+)?(T\w+)\s*=\s*(-?\d+)", kv)
                if mm: d[m.group(1)][mm.group(1)] = int(mm.group(2))
    return d


class Net:
    def __init__(self, work, prims):
        self.dflt = prims_defaults(prims)
        self.icbuf, self.cells, self.drv, self.loads = {}, {}, {}, collections.defaultdict(list)
        for line in open(work + "/netlist_baked.v"):
            m = RE_INST.match(line)
            if not m: continue
            typ, params, name, conns = m.groups()
            pd = dict(re.findall(r"\.(\w+)\(([^()]*)\)", params or ""))
            cd = dict(re.findall(r"\.(\w+)\(([^()]*)\)", conns))
            if typ == "ICBUF": self.icbuf[cd["O"]] = (cd["I"], int(pd.get("D", 1)))
            else: self.cells[name] = (typ, pd, cd)
        for name, (typ, pd, cd) in self.cells.items():
            for p, x in cd.items():
                if p in OUTS.get(typ, ()):
                    if x.startswith("n"): self.drv[x] = (name, p)
                else:
                    src, D = self.icbuf[x] if x.startswith("w") else (x, 0)
                    if src.startswith("n"): self.loads[src].append((name, p, D))
        self.name = {}
        for l in open(work + "/nets.map"):
            p = l.split()
            if len(p) >= 2 and not l.startswith("#"): self.name[p[0]] = p[1]
        self.inv = {v: k for k, v in self.name.items()}

    def arc(self, typ, pd, pin, port):
        if typ in ("SLICE_FFX", "SLICE_LATX"):
            k = {"CK": "TCKQ", "D": "TDQ", "SR": "TSRQ", "CE": "TCEQ"}[pin]
            v = int(pd.get(k, self.dflt[typ].get(k, -1)))
            return v if v >= 0 else int(pd.get("TCKQ", self.dflt[typ]["TCKQ"]))
        k = "T%s%s" % (pin, port)
        return int(pd.get(k, self.dflt.get(typ, {}).get(k, 0)))


def load_vcd(path, keep=lambda n: n.startswith("n")):
    ids, ev, t = {}, collections.defaultdict(list), 0
    with open(path) as f:
        for line in f:
            if line.startswith("$var"):
                p = line.split()
                if keep(p[4]): ids.setdefault(p[3], []).append(p[4])
            elif line.startswith("$enddefinitions"): break
        for line in f:
            c = line[:1]
            if c == "#": t = int(line[1:]); continue
            if c and c in "01xz":
                for n in ids.get(line[1:].strip(), ()): ev[n].append((t, c))
    return ev


class Trace:
    def __init__(self, net, ev):
        self.N, self.ev = net, ev
        self.times = {n: [t for t, _ in e] for n, e in ev.items()}

    def val_at(self, n, t):            # value of n right after time t
        tt = self.times.get(n, []); i = bisect.bisect_right(tt, t)
        return self.ev[n][i - 1][1] if i else None

    def cause(self, n, t):
        N = self.N
        if n not in N.drv: return None
        cell, port = N.drv[n]; typ, pd, cd = N.cells[cell]
        pins = cd.items()
        if typ == "SLICE_FFX": pins = [(p, x) for p, x in cd.items() if p in ("CK", "SR")]
        best = None
        for p, x in pins:
            if p in OUTS.get(typ, ()): continue
            src, D = N.icbuf[x] if x.startswith("w") else (x, 0)
            if not src.startswith("n"): continue
            a = N.arc(typ, pd, p, port); target = t - D - a
            tt = self.times.get(src, []); i = bisect.bisect_right(tt, target)
            if i == 0: continue
            slack = target - tt[i - 1]
            if best is None or slack < best["slack"]:
                best = dict(src=src, t=tt[i - 1], wire=D, arc=a, slack=slack, pin=p, cell=cell, typ=typ,
                            port=port, val=self.ev[src][i - 1][1])
        return best

    def chain(self, n, t, stop):
        """Walk causes back from (n, t) until stop(n, t) is true; returns hops newest first."""
        out = []
        while True:
            c = self.cause(n, t)
            if c is None: return out, ("END", n, t)
            c["out"], c["tout"], c["edge"] = n, t, self.val_at(n, t)
            out.append(c)
            n, t = c["src"], c["t"]
            if stop(n, t): return out, ("STOP", n, t)
