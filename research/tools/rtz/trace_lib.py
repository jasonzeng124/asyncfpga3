"""Causal back-trace on a routed GLS VCD (netlist_baked.v + prims.v delays)."""
import re, collections, bisect

def load_prims_defaults(prims):
    s = open(prims).read()
    dflt = {}
    for m in re.finditer(r"module (\w+)\s*\((.*?)endmodule", s, re.S):
        mod, body = m.group(1), m.group(2)
        d = {}
        for pm in re.finditer(r"parameter\s+([^;]*);", body):
            for kv in pm.group(1).split(","):
                kv = kv.strip()
                mm = re.match(r"(?:integer\s+)?(T\w+)\s*=\s*(\d+)", kv)
                if mm: d[mm.group(1)] = int(mm.group(2))
        dflt[mod] = d
    return dflt

RE_INST = re.compile(r"^\s*(\w+)\s*(?:#\((.*?)\))?\s+(\w+)\s*\((.*)\);\s*$")
def load_netlist(path):
    icbuf = {}      # w -> (src net, D)
    cells = {}      # name -> (type, params, conns)
    driver = {}     # net -> (cell, port)
    for line in open(path):
        m = RE_INST.match(line)
        if not m: continue
        typ, params, name, conns = m.groups()
        pd = {}
        if params:
            for k, v in re.findall(r"\.(\w+)\(([^()]*)\)", params): pd[k] = v
        cd = dict(re.findall(r"\.(\w+)\(([^()]*)\)", conns))
        if typ == "ICBUF":
            icbuf[cd["O"]] = (cd["I"], int(pd.get("D", 1)))
        else:
            cells[name] = (typ, pd, cd)
    return icbuf, cells

OUTS = {"SLICE_LUTX": ("O5", "O6"), "SELMUX2_1": ("OUT",), "SLICE_FFX": ("Q",),
        "CARRY4": ("O0","O1","O2","O3","CO0","CO1","CO2","CO3"),
        "IOB33_OUTBUF": ("OUT",), "IOB33_INBUF_EN": ("OUT",), "BUFGCTRL": ("O",),
        "PSEUDO_GND": ("Y",), "PSEUDO_VCC": ("Y",)}

def drivers(cells):
    d = {}
    for name, (typ, pd, cd) in cells.items():
        for p in OUTS.get(typ, ()):
            if p in cd and cd[p].startswith("n"):
                d[cd[p]] = (name, p)
    return d

def load_vcd(path, keep=lambda n: True):
    ids, ev = {}, collections.defaultdict(list)
    t = 0
    with open(path) as f:
        for line in f:
            if line.startswith("$var"):
                p = line.split()
                if keep(p[4]): ids.setdefault(p[3], []).append(p[4])
            elif line.startswith("$enddefinitions"):
                break
        for line in f:
            if not line or line[0] == "$": continue
            c = line[0]
            if c == "#": t = int(line[1:]); continue
            if c in "01xz":
                i = line[1:].strip()
                for n in ids.get(i, ()): ev[n].append((t, c))
    return ev
