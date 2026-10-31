#!/usr/bin/env python3
"""ord_static.py -- UNTRUSTED (lead, 2026-10-31): the ArbOrd row Dr + 2 <= DQ + Dq for every bd_arbiter grant
reader, with the research GLS's fixed (SDF) delays: D = ICBUF D of the pin + the LUT's TA<pin>O6.
Dr = the grant LUT's request pin, DQ = ustate$LUT6's pin reading the same request net, Dq = the grant's q pin.
    python3 -I ord_static.py GLS_WORK"""
import re, sys, os
W = sys.argv[1]
nm = {}
for ln in open(os.path.join(W, "names.map")):
    p = ln.split()
    if len(p) == 2: nm[p[1]] = p[0]
net = open(os.path.join(W, "netlist_baked.v")).read()
icbuf = {m.group(3): (m.group(2), int(m.group(1))) for m in
         re.finditer(r"ICBUF #\(\.D\((\d+)\)\) \S+ \(\.I\((\w+)\), \.O\((\w+)\)\);", net)}
def cell(c):
    m = re.search(r"SLICE_LUTX #\(([^;]*?)\) " + c + r" \(([^;]*)\);", net)
    pins = dict(re.findall(r"\.(A\d|O6)\(([^)]*)\)", m.group(2)))
    ta = {int(k): int(v) for k, v in re.findall(r"\.TA(\d)O6\((\d+)\)", m.group(1))}
    src = {p: icbuf[v] for p, v in pins.items() if p.startswith("A") and v in icbuf}   # pin -> (driver net, D)
    return pins, ta, src
arbs = sorted({k.rsplit(".", 1)[0] for k in nm if ".uarb" in k and ".ustate$LUT6" in k})
worst = None
for a in arbs:
    sp, sta, ssrc = cell(nm[a + ".ustate$LUT6"])
    qnet = sp["O6"]
    for g in ("ugrant$LUT5", "ugrant$LUT6"):
        if a + "." + g not in nm: continue
        gp, gta, gsrc = cell(nm[a + "." + g])
        qpins = [p for p, (n, _) in gsrc.items() if n == qnet]
        rpins = [p for p, (n, _) in gsrc.items() if n != qnet and any(n == n2 for (n2, _) in ssrc.values())]
        for qp in qpins:
            Dq = gsrc[qp][1] + gta.get(int(qp[1]), 0)
            for rp in rpins:
                rn = gsrc[rp][0]
                Dr = gsrc[rp][1] + gta.get(int(rp[1]), 0)
                for sp_, (n2, d2) in ssrc.items():
                    if n2 != rn: continue
                    DQ = d2 + sta.get(int(sp_[1]), 0)
                    m = DQ + Dq - Dr - 2
                    worst = m if worst is None else min(worst, m)
                    print(f"{a.split('udut.')[-1]} {g}: Dr {Dr} DQ {DQ} Dq {Dq} margin {m} {'ok' if m >= 0 else 'FAIL'}")
print("WORST", worst)
