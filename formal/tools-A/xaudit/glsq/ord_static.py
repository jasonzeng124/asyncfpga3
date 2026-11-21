#!/usr/bin/env python3
"""ord_static.py -- UNTRUSTED (lead; corrected after audit P15a): the ArbOrd row Dr + 2 <= DQ + Dq for every
bd_arbiter reader (both grants AND the R0 term ustate$LUT5), with the research GLS's fixed delays
D = ICBUF D of the pin + the cell's TA<pin>O<5|6>. Dr = the reader's pin on a request net, DQ = ustate$LUT6's pin
on the same net, Dq = the reader's q pin. A request net (fixed after audit P17 row 2d) = a non-q, non-constant
input net of ustate$LUT6 on which the R0 term ustate$LUT5 (r1 q + r2 !q) DEPENDS, computed from its INIT
(some assignment of the other inputs where toggling the net toggles the output). The earlier filter ("any
LUT-driven ustate input other than q") also admitted rst (LUT-buffered here) and A0, which R0 does not read;
ArbOrd's o3/o4 pairs read only P1R/P2R. Each arbiter must give exactly 2 request nets (else exit 1).
OLD=1 restores the earlier filter (for comparison only). Prints every pair and WORST.   python3 -I ord_static.py GLS_WORK"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lutnet import load
nm, icbuf, cells, drv, const = load(sys.argv[1])
inv = {v: k for k, v in nm.items()}
arbs = sorted({k.rsplit(".", 1)[0] for k in nm if ".uarb" in k and k.endswith(".ustate$LUT6")})
def support(R, rsrc):
    nets = sorted({n for (n, _) in rsrc.values() if n not in const})
    def lutout(assign):
        idx = 0
        for k in range(1, 7):
            w = R["pins"].get(f"A{k}")
            if w is None: v = 0
            elif w.startswith("1'b"): v = int(w[-1])
            else:
                n = rsrc[f"A{k}"][0] if f"A{k}" in rsrc else None
                v = const[n] if n in const else assign.get(n, 0)
            idx |= v << (k - 1)
        return (R["init"] >> (idx & 31 if R["op"] == "O5" else idx)) & 1
    dep = set()
    for n in nets:
        others = [m for m in nets if m != n]
        for bits in range(1 << len(others)):
            a = {m: (bits >> i) & 1 for i, m in enumerate(others)}
            if lutout({**a, n: 0}) != lutout({**a, n: 1}): dep.add(n); break
    return dep
worst = None; npairs = 0
for a in arbs:
    S = cells[nm[a + ".ustate$LUT6"]]; q = S["out"]
    ssrc = {p: icbuf[w] for p, w in S["pins"].items() if w in icbuf}
    if os.environ.get("OLD") == "1":
        reqnets = {n for (n, _) in ssrc.values() if n != q and n in drv}
    else:
        R0 = cells[nm[a + ".ustate$LUT5"]]
        r0src = {p: icbuf[w] for p, w in R0["pins"].items() if w in icbuf}
        reqnets = support(R0, r0src) - {q}
        if len(reqnets) != 2: sys.exit(f"ord_static: {a}: R0 support minus q = {sorted(reqnets)}, expected 2 requests")
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
