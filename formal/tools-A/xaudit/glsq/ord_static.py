#!/usr/bin/env python3
"""ord_static.py -- UNTRUSTED (lead; corrected after audit P15a): the ArbOrd row Dr + 2 <= DQ + Dq for every
bd_arbiter reader (both grants AND the R0 term ustate$LUT5), with the research GLS's fixed delays
D = ICBUF D of the pin + the cell's TA<pin>O<5|6>. Dr = the reader's pin on a request net, DQ = ustate$LUT6's pin
on the same net, Dq = the reader's q pin. A request net = an input net of ustate$LUT6 that is not q and is driven
by a LUT output (O5 or O6); this excludes the reset (non-LUT driver) and may include A0 if the reader reads it
(conservative). Prints every pair and WORST.   python3 -I ord_static.py GLS_WORK"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lutnet import load
nm, icbuf, cells, drv = load(sys.argv[1])
inv = {v: k for k, v in nm.items()}
arbs = sorted({k.rsplit(".", 1)[0] for k in nm if ".uarb" in k and k.endswith(".ustate$LUT6")})
worst = None; npairs = 0
for a in arbs:
    S = cells[nm[a + ".ustate$LUT6"]]; q = S["out"]
    ssrc = {p: icbuf[w] for p, w in S["pins"].items() if w in icbuf}
    reqnets = {n for (n, _) in ssrc.values() if n != q and n in drv}
    for rd in ("ugrant$LUT5", "ugrant$LUT6", "ustate$LUT5"):
        if a + "." + rd not in nm: continue
        R = cells[nm[a + "." + rd]]
        rsrc = {p: icbuf[w] for p, w in R["pins"].items() if w in icbuf}
        qp = [p for p, (n, _) in rsrc.items() if n == q]
        for qpin in qp:
            Dq = rsrc[qpin][1] + R["ta"].get(int(qpin[1]), 0)
            for rp, (n, d) in rsrc.items():
                if n not in reqnets: continue
                Dr = d + R["ta"].get(int(rp[1]), 0)
                for sp, (n2, d2) in ssrc.items():
                    if n2 != n: continue
                    DQ = d2 + S["ta"].get(int(sp[1]), 0)
                    m = DQ + Dq - Dr - 2; npairs += 1
                    worst = m if worst is None else min(worst, m)
                    src = inv.get(drv[n], drv[n]).split("udut.")[-1]
                    print(f"{a.split('udut.')[-1]} {rd}: pin {rp} (ustate {sp}, from {src}) Dr {Dr} DQ {DQ} Dq {Dq} margin {m} {'ok' if m >= 0 else 'FAIL'}")
print(f"PAIRS {npairs} WORST {worst}")
