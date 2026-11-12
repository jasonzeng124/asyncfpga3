#!/usr/bin/env python3
"""gen_cwmon.py -- UNTRUSTED (lead, 2026-10-31): monitor for ArbEdge's C window `RdEdge.fall` of the two GRANT
readers, on the research routed GLS.   python3 -I gen_cwmon.py GLS_WORK XAN.txt > cwmon.v
Lean (`Events9ArbNetEdge.RdEdge.fall`): for every fall of the reader's request s at sigma (s (sigma-1) high,
s sigma low), ustate reads A0 high at every ustate time u with sigma + lo Dr <= u + hi Dq and
u + lo Dq < sigma + hi Dr + 2. For a fixed-delay behaviour ustate reads A0 at u - DA (DA = ICBUF D + TA on ustate's
A0 pin), so the A0 DRIVER net must be high on [sigma + lo Dr - hi Dq - DA, sigma + hi Dr + 2 - lo Dq - DA).
sigma = the fall time of the request's driver net. The monitor flags CW_VIOL if A0 is low at any time in that window
(A0's last 16 low intervals per arbiter are kept and checked against each request fall's window; an A0 fall
after sigma inside the window is checked as it happens). An older low interval than the last 16 is not seen. A0 = the ustate
input with which the INIT holds q (output = q for both q values with A0 = 1, rst = 0, any requests); rst = the
input that forces the output high. lo Dr / hi Dr /
lo Dq / hi Dq: the reader's request and q bands from XAN.txt. Same caveats as gen_noremon.py.
POINT=1: the pointwise C condition of `ArbEdgeSP` (c_of_pt) at this run's own point delays instead: A0 high at
sigma + Dr - Dq - DA (+0..2), Dr / Dq = the grant's request / q pin delays (ICBUF D + TA)."""
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
out = ["module cwmon;"]
for a, B in sorted(bands.items()):
    S = cells[nm[a + ".ustate$LUT6"]]; q = S["out"]
    ssrc = {p: icbuf[w] for p, w in S["pins"].items() if w in icbuf}
    fS = evaluator(S, ssrc)
    cand = sorted({n for (n, _) in ssrc.values() if n != q and n not in const})
    import itertools
    def forces1(rn_):
        others = [n for n in cand if n != rn_]
        for vals in itertools.product((0, 1), repeat=len(others)):
            asg = dict(zip(others, vals)); asg[rn_] = 1
            for qv in (0, 1):
                asg[q] = qv
                if fS(asg) != 1: return False
        return True
    rsts = [n for n in cand if forces1(n)]     # the reset input (q = rst + ...), held low below
    cand = [n for n in cand if n not in rsts]
    def holds(an):
        others = [n for n in cand if n != an]
        for vals in itertools.product((0, 1), repeat=len(others)):
            asg = dict(zip(others, vals)); asg[an] = 1
            for r_ in rsts: asg[r_] = 0
            for qv in (0, 1):
                asg[q] = qv
                if fS(asg) != qv: return False
        return True
    a0 = [n for n in cand if holds(n)]
    if len(a0) != 1: print(f"// {a}: A0 candidates {a0} of {cand}", file=sys.stderr); continue
    a0n = a0[0]
    pa = [p for p, (n, _) in ssrc.items() if n == a0n][0]
    DA = ssrc[pa][1] + S["ta"].get(int(pa[1]), 0)
    for b, g in ((1, "ugrant$LUT5"), (2, "ugrant$LUT6")):
        R = cells[nm[a + "." + g]]
        rsrc = {p: icbuf[w] for p, w in R["pins"].items() if w in icbuf}
        fR = evaluator(R, rsrc); qv = 1 if b == 1 else 0
        rc = sorted({n for (n, _) in rsrc.values() if n != q and n not in const})
        mine = [n for n in rc if fR({q: qv, n: 1}) == 1 and fR({q: qv, n: 0}) == 0]
        if len(mine) != 1: print(f"// {a} {g}: request {mine} of {rc}", file=sys.stderr); continue
        rn = mine[0]
        loDr, hiDr = B[f"Dr{b}"]; loDq, hiDq = B[f"Dq{b}"]
        lo = loDr - hiDq - DA; hi = hiDr + 2 - loDq - DA      # window [sigma + lo, sigma + hi)
        if os.environ.get("POINT") == "1":   # pointwise C (ArbEdgeSP.c_k) at this run's own point delays
            Dr = [d + R["ta"].get(int(p_[1]), 0) for p_, (n, d) in rsrc.items() if n == rn][0]
            Dq = [d + R["ta"].get(int(p_[1]), 0) for p_, (n, d) in rsrc.items() if n == q][0]
            lo = Dr - Dq - DA; hi = lo + 3
        tag = a.split("udut.")[-1] + f".g{b}"; c = nm[a + ".ustate$LUT6"] + f"_{b}"; ca = nm[a + ".ustate$LUT6"]
        out.append(f"  // {tag}: request {rn}, A0 net {a0n} (ustate pin {pa}, DA {DA}), window [sigma + {lo}, sigma + {hi})")
        if b == 1:   # one ring buffer of A0's recent low intervals per arbiter (16 entries)
            out.append(f"  realtime ls_{ca} [0:15]; realtime le_{ca} [0:15]; integer ix_{ca} = 0; integer k_{ca};")
            out.append(f"  initial for (k_{ca} = 0; k_{ca} < 16; k_{ca} = k_{ca} + 1) begin ls_{ca}[k_{ca}] = -2.0e9; le_{ca}[k_{ca}] = -2.0e9; end")
            out.append(f"  always @(negedge tb_run.dut.{a0n}) begin ix_{ca} = (ix_{ca} + 1) % 16; ls_{ca}[ix_{ca}] = $realtime; le_{ca}[ix_{ca}] = 1.0e15; end")
            out.append(f"  always @(posedge tb_run.dut.{a0n}) le_{ca}[ix_{ca}] = $realtime;")
        out.append(f"  realtime wlo_{c} = 1.0e15; realtime whi_{c} = -1.0e9; integer j_{c};")
        out.append(f"  always @(negedge tb_run.dut.{rn}) begin wlo_{c} = $realtime + ({lo}); whi_{c} = $realtime + ({hi}); "
                   f"$display(\"CW_FALL %0t {tag}\", $realtime); "
                   f"if (tb_run.dut.{a0n} === 1'bx) $display(\"CW_VIOL %0t {tag} x\", $realtime); "
                   f"for (j_{c} = 0; j_{c} < 16; j_{c} = j_{c} + 1) "
                   f"if (ls_{ca}[j_{c}] < whi_{c} && le_{ca}[j_{c}] > wlo_{c}) $display(\"CW_VIOL %0t {tag} past overlap %0t\", $realtime, (le_{ca}[j_{c}] < whi_{c} ? le_{ca}[j_{c}] : whi_{c}) - (ls_{ca}[j_{c}] > wlo_{c} ? ls_{ca}[j_{c}] : wlo_{c})); end")
        if hi > 0:
            out.append(f"  always @(negedge tb_run.dut.{a0n}) if ($realtime >= wlo_{c} && $realtime < whi_{c}) $display(\"CW_VIOL %0t {tag} future\", $realtime);")
out.append("endmodule")
print("\n".join(out))
