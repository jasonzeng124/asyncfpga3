#!/usr/bin/env python3
"""gen_noremon.py -- UNTRUSTED (lead, 2026-10-31): monitor for ArbEdge's no-re-request window `RdEdge.nore` of the
two GRANT readers (e1, e2), on the research routed GLS.
    python3 -I gen_noremon.py GLS_WORK XAN.txt > noremon.v
Lean (`Events9ArbNetEdge.RdEdge.nore`, reader b with request s_b, literal e = q (b = 1) or !q (b = 2)):
  for every flip of e away from the branch at tau (q falls for b = 1, rises for b = 2), the request is low at
  every v with fQ tau <= v and v + lo Dr < tau + hi Dq + 2,
where fQ is ustate's read of that request and lo Dr / hi Dq are the reader's request / q band ends (xarbnet's
printed bands, from XAN.txt, of the same route and corner). For a fixed-delay behaviour fQ tau = tau - DQ with DQ
= ustate's ICBUF D + TA on that request's pin. So the monitor requires the request's DRIVER net to be low on
[tau - DQ, tau + hi Dq + 2 - lo Dr): it flags NORE_VIOL when (pre) the request was high at some time in
[tau - DQ, tau] or (post) it rises before tau + hi Dq + 2 - lo Dr. g1 = ugrant$LUT5 reads r1, g2 = ugrant$LUT6
reads r2 (each grant's single non-q, non-constant input). Caveat: the GLS delays are nextpnr SDF points, not
shown inside the prjxray bands that give lo Dr / hi Dq. The pre-check looks at the request's LAST high interval only
(an earlier pulse inside the window followed by a later pulse after the window end would be missed)."""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lutnet import load
nm, icbuf, cells, drv, const = load(sys.argv[1])
bands = {}
for ln in open(sys.argv[2]):
    m = re.search(r"arbiter (\S+)\.ustate\$LUT6: ArbOK \w+; K \d+, ctl lo \d+; Dq g1/g2/R0 \((\d+), (\d+)\)/\((\d+), (\d+)\)/\((\d+), (\d+)\), Dr1 g1/R0 \((\d+), (\d+)\)/\((\d+), (\d+)\), Dr2 g2/R0 \((\d+), (\d+)\)", ln)
    if m:
        v = list(map(int, m.groups()[1:]))
        bands[m.group(1)] = dict(Dq1=(v[0], v[1]), Dq2=(v[2], v[3]), Dr1=(v[6], v[7]), Dr2=(v[10], v[11]))
out = ["module noremon;"]
for a, B in sorted(bands.items()):
    S = cells[nm[a + ".ustate$LUT6"]]; q = S["out"]
    ssrc = {p: icbuf[w] for p, w in S["pins"].items() if w in icbuf}
    for b, g, flipedge in ((1, "ugrant$LUT5", "negedge"), (2, "ugrant$LUT6", "posedge")):
        R = cells[nm[a + "." + g]]
        rsrc = {p: icbuf[w] for p, w in R["pins"].items() if w in icbuf}
        # the grant's own request: the non-q, non-constant input net whose value the output follows with q on
        # the branch (q = 1 for g1, 0 for g2) and the other candidate inputs low (evaluated on the INIT)
        cand = sorted({n for p, (n, _) in rsrc.items() if n != q and n not in const})
        def val(pin, assign):
            w = R["pins"][pin]
            if w.startswith("1'b"): return int(w[-1])
            n = rsrc[pin][0] if pin in rsrc else None
            if n in const: return const[n]
            return assign.get(n, 0)
        def lutout(assign):
            idx = sum(val(f"A{k}", assign) << (k - 1) for k in range(1, 7))
            return (R["init"] >> (idx & 31 if R["op"] == "O5" else idx)) & 1
        qv = 1 if b == 1 else 0
        mine = [n for n in cand if lutout({q: qv, n: 1}) == 1 and lutout({q: qv, n: 0}) == 0]
        if len(mine) != 1: print(f"// {a} {g}: request candidates {cand}, matching {mine}", file=sys.stderr); continue
        rn = mine[0]
        sp = [p for p, (n, _) in ssrc.items() if n == rn]
        if len(sp) != 1: print(f"// {a} {g}: ustate pins on the request {sp}", file=sys.stderr); continue
        DQ = ssrc[sp[0]][1] + S["ta"].get(int(sp[0][1]), 0)
        loDr = B[f"Dr{b}"][0]; hiDq = B[f"Dq{b}"][1]; E = hiDq + 2 - loDr + int(os.environ.get("EXTRA", "0"))  # EXTRA: detection control
        tag = a.split("udut.")[-1] + f".g{b}"; c = nm[a + ".ustate$LUT6"] + f"_{b}"
        out.append(f"  // {tag}: request net {rn}, DQ {DQ}, window [tau - {DQ}, tau + {E}) (hi Dq {hiDq} + 2 - lo Dr {loDr})")
        # request high on [lrise, lfall) intervals; flag if one overlaps [tau - DQ, tau + E)
        out.append(f"  realtime lrise_{c} = -1.0e9; realtime lfall_{c} = -1.0e9; realtime until_{c} = -1.0e9;")
        out.append(f"  always @(negedge tb_run.dut.{rn}) lfall_{c} = $realtime;")
        out.append(f"  always @({flipedge} tb_run.dut.{q}) begin until_{c} = $realtime + ({E}); $display(\"NORE_FLIP %0t {tag}\", $realtime);"
                   f" if ((tb_run.dut.{rn} !== 1'b0 && lrise_{c} < $realtime + ({E}) && $realtime + ({E}) > $realtime - {DQ})"
                   f" || (tb_run.dut.{rn} === 1'b0 && ({E}) > -{DQ} && lfall_{c} > $realtime - {DQ} && lrise_{c} < $realtime + ({E})))"
                   f" $display(\"NORE_VIOL %0t {tag} pre\", $realtime); end")
        out.append(f"  always @(posedge tb_run.dut.{rn}) begin lrise_{c} = $realtime; if ($realtime < until_{c}) $display(\"NORE_VIOL %0t {tag} post %0t\", $realtime, until_{c} - $realtime); end")

out.append("endmodule")
print("\n".join(out))
