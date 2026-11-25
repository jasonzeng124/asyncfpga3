#!/usr/bin/env python3
"""gen_evmon.py -- UNTRUSTED (lead, 2026-10-31): log every change of each bd_arbiter's q, A0, r1, r2 (driver nets) on
the research GLS, and write the per-arbiter point delays the window checks need (check_env.py).
    python3 -I gen_evmon.py GLS_WORK OUT.json > evmon.v
OUT.json: per arbiter: nets {q, A0, r1, r2}; DA (ustate's A0 pin: ICBUF D + TA); DQ1/DQ2 (ustate's r1/r2 pins);
readers g1 (ugrant$LUT5: r1, q), g2 (ugrant$LUT6: r2, q), s1/s2 (ustate$LUT5, the R0 term: r1 / r2, q) with Dr, Dq.
Picking rules as gen_cwmon.py: A0 = the ustate input that holds q, rst = the input that forces it high, each grant's
request by its INIT; the R0 reader reads both requests (same nets as ustate)."""
import sys, os, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lutnet import load
nm, icbuf, cells, drv, const = load(sys.argv[1])
def evaluator(R, rsrc):
    def val(pin, assign):
        w = R["pins"].get(pin, "1'b0")
        if w.startswith("1'b"): return int(w[-1])
        n = rsrc[pin][0] if pin in rsrc else None
        if n in const: return const[n]
        return assign.get(n, 0)
    def f(assign):
        idx = sum(val(f"A{k}", assign) << (k - 1) for k in range(1, 7))
        return (R["init"] >> (idx & 31 if R["op"] == "O5" else idx)) & 1
    return f
def pdel(R, rsrc, net):
    ps = [p for p, (n, _) in rsrc.items() if n == net]
    return (rsrc[ps[0]][1] + R["ta"].get(int(ps[0][1]), 0)) if len(ps) == 1 else None
info = {}; out = ["module evmon;"]
for name in sorted(k.rsplit(".", 1)[0] for k in nm if ".uarb" in k and k.endswith(".ustate$LUT6")):
    S = cells[nm[name + ".ustate$LUT6"]]; q = S["out"]
    ss = {p: icbuf[w] for p, w in S["pins"].items() if w in icbuf}; fS = evaluator(S, ss)
    cand = sorted({n for (n, _) in ss.values() if n != q and n not in const})
    def all_asg(nets):
        for vals in itertools.product((0, 1), repeat=len(nets)): yield dict(zip(nets, vals))
    rst = [n for n in cand if all(fS({**g, n: 1, q: qv}) == 1 for g in all_asg([m for m in cand if m != n]) for qv in (0, 1))]
    c2 = [n for n in cand if n not in rst]
    a0 = [n for n in c2 if all(fS({**g, n: 1, q: qv, **{r: 0 for r in rst}}) == qv for g in all_asg([m for m in c2 if m != n]) for qv in (0, 1))]
    G = {}
    ok = len(a0) == 1
    for tag, g, qv in (("g1", "ugrant$LUT5", 1), ("g2", "ugrant$LUT6", 0)):
        R = cells[nm[name + "." + g]]; rs = {p: icbuf[w] for p, w in R["pins"].items() if w in icbuf}; fR = evaluator(R, rs)
        rc = sorted({n for (n, _) in rs.values() if n != q and n not in const})
        mine = [n for n in rc if fR({q: qv, n: 1}) == 1 and fR({q: qv, n: 0}) == 0]
        if len(mine) != 1: ok = False; continue
        G[tag] = dict(req=mine[0], Dr=pdel(R, rs, mine[0]), Dq=pdel(R, rs, q))
    if not ok or "g1" not in G or "g2" not in G: print(f"// {name}: not mapped", file=sys.stderr); continue
    r1, r2 = G["g1"]["req"], G["g2"]["req"]
    R0 = cells[nm[name + ".ustate$LUT5"]]; r0s = {p: icbuf[w] for p, w in R0["pins"].items() if w in icbuf}
    G["s1"] = dict(req=r1, Dr=pdel(R0, r0s, r1), Dq=pdel(R0, r0s, q))
    G["s2"] = dict(req=r2, Dr=pdel(R0, r0s, r2), Dq=pdel(R0, r0s, q))
    info[name] = dict(q=q, A0=a0[0], r1=r1, r2=r2, DA=pdel(S, ss, a0[0]), DQ1=pdel(S, ss, r1), DQ2=pdel(S, ss, r2), readers=G)
    tag = name.split("udut.")[-1]
    for k in ("q", "A0", "r1", "r2"):
        n = info[name][k]
        out.append(f"  always @(tb_run.dut.{n}) $display(\"EV %0t {tag} {k} %b\", $realtime, tb_run.dut.{n});")
out.append("endmodule")
json.dump(info, open(sys.argv[2], "w"), indent=1)
print("\n".join(out))
