"""lutnet.py -- shared parser for the glsq monitors (UNTRUSTED): physical LUT cells of a research GLS
netlist_baked.v with their connected output port (O5 or O6), per-pin nets, per-pin TA<k>O<5|6> delays, and the
ICBUF map (pin wire -> (driver net, D))."""
import re, os
def load(W):
    nm = {}
    for ln in open(os.path.join(W, "names.map")):
        p = ln.split()
        if len(p) == 2: nm[p[1]] = p[0]
    net = open(os.path.join(W, "netlist_baked.v")).read()
    icbuf = {m.group(3): (m.group(2), int(m.group(1))) for m in
             re.finditer(r"ICBUF #\(\.D\((\d+)\)\) \S+ \(\.I\((\w+)\), \.O\((\w+)\)\);", net)}
    cells = {}
    for m in re.finditer(r"SLICE_LUTX #\(([^;]*?)\) (c_\d+) \(([^;]*)\);", net):
        params, c, conns = m.group(1), m.group(2), m.group(3)
        pins = dict(re.findall(r"\.(A\d|O5|O6)\(([^)]*)\)", conns))
        op = "O6" if "O6" in pins else ("O5" if "O5" in pins else None)
        ta = {int(k): int(v) for k, v in re.findall(r"\.TA(\d)" + (op or "O6") + r"\((\d+)\)", params)}
        cells[c] = dict(op=op, out=pins.get(op), pins={k: v for k, v in pins.items() if k.startswith("A")}, ta=ta)
    drv = {v["out"]: c for c, v in cells.items() if v["out"]}
    return nm, icbuf, cells, drv
