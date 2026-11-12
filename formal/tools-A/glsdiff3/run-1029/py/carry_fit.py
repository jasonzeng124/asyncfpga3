#!/usr/bin/env python3
"""carry_fit.py -- is the research GLS CARRY4 "per-(pin, output) transport, then the
zero-time carry function" on multi-pin traces?  That is the Lean/Gen model (each arc a
Pure channel with lo = hi = its SDF number; CARRY4 = the UG474 MUXCY/XORCY equations:
CO_i = S_i ? CO_(i-1) : DI_i, O_i = S_i xor CO_(i-1), CO_(-1) = CIN | CYINIT).
Random edge traces on CIN, S0, S1, S2, DI0, DI1, DI2 (10 ps grid); every arc set to a
distinct value = 3 mod 10, so arrivals of different pins either coincide (one step) or
are >= 10 ps apart.  Compares the event list of all 8 outputs with the reference.
The reference is computed from the equations above, not from a run.
Usage: python3 -I carry_fit.py PRIMS_V N [SEED]"""
import os, random, subprocess, sys, tempfile
PINS = ["CIN", "S0", "S1", "S2", "DI0", "DI1", "DI2"]
OUTS = ["O0", "O1", "O2", "O3", "CO0", "CO1", "CO2", "CO3"]
SUP = {"O0": ["CIN", "S0"], "O1": ["CIN", "S0", "S1", "DI0"], "O2": ["CIN", "S0", "S1", "S2", "DI0", "DI1"],
       "O3": ["CIN", "S0", "S1", "S2", "DI0", "DI1", "DI2"],
       "CO0": ["CIN", "S0", "DI0"], "CO1": ["CIN", "S0", "S1", "DI0", "DI1"],
       "CO2": ["CIN", "S0", "S1", "S2", "DI0", "DI1", "DI2"], "CO3": ["CIN", "S0", "S1", "S2", "DI0", "DI1", "DI2"]}
def fn(o, v):
    c = v["CIN"]; co = []
    for i in range(4):
        s = v.get("S%d" % i, 0); di = v.get("DI%d" % i, 0)
        oi = s ^ c; c = c if s else di; co.append(c)
        if o == "O%d" % i: return oi
    return co[int(o[2])]
def arcs(rng):
    A = {}
    for o in OUTS:
        for p in SUP[o]: A[(p, o)] = rng.randrange(10, 60) * 10 + 3
    return A
def ref(edges, A):
    out = {}
    for o in OUTS:
        ev = sorted(set(t + A[(p, o)] for t, p, _ in edges if p in SUP[o]))
        cur = {p: 0 for p in PINS}; f = fn(o, cur); lst = []
        # value of pin p as seen by output o at time T: last edge with t + arc <= T
        for T in ev:
            v = {p: 0 for p in PINS}
            for t, p, val in edges:
                if p in SUP[o] and t + A[(p, o)] <= T: v[p] = val
            nf = fn(o, v)
            if nf != f: lst.append((T + 0, nf)); f = nf
        out[o] = lst
    return out
def tb(edges, A):
    par = ", ".join(".T%s%s(%d)" % (p, o, d) for (p, o), d in sorted(A.items()))
    L = ["`timescale 1ps/1ps", "module tb;"]
    L.append("reg " + ", ".join("%s = 0" % p.lower() for p in PINS) + ";")
    L.append("wire " + ", ".join(o.lower() for o in OUTS) + ";")
    L.append("CARRY4 #(%s) u (.CYINIT(1'b0), .DI3(1'b0), .S3(1'b0), %s, %s);" % (
        par, ", ".join(".%s(%s)" % (p, p.lower()) for p in PINS), ", ".join(".%s(%s)" % (o, o.lower()) for o in OUTS)))
    for o in OUTS:
        L.append("always @(%s) if ($time > 900) $display(\"%s %%0d %%b\", $time, %s);" % (o.lower(), o, o.lower()))
    L.append("initial begin")
    t0 = 0
    for t, p, v in edges:
        L.append("  #%d %s = %d;" % (t - t0, p.lower(), v)); t0 = t
    L += ["  #2000 $finish;", "end", "endmodule"]
    return "\n".join(L)
def main():
    prims, n = sys.argv[1], int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 11
    rng = random.Random(seed); ok = 0; first = None; nev = 0
    with tempfile.TemporaryDirectory() as wd:
        for k in range(n):
            A = arcs(rng); t = 1000; edges = []; cur = {p: 0 for p in PINS}
            for _ in range(rng.randint(4, 14)):
                t += rng.randrange(1, 40) * 10; p = rng.choice(PINS); cur[p] ^= 1; edges.append((t, p, cur[p]))
            open(os.path.join(wd, "tb.v"), "w").write(tb(edges, A))
            vvp = os.path.join(wd, "tb.vvp")
            subprocess.run(["iverilog", "-gspecify", "-o", vvp, os.path.join(wd, "tb.v"), prims], check=True)
            so = subprocess.run(["vvp", "-n", vvp], check=True, capture_output=True, text=True).stdout
            got = {o: [] for o in OUTS}
            for l in so.splitlines():
                w = l.split()
                if len(w) == 3 and w[0] in got: got[w[0]].append((int(w[1]), 1 if w[2] == "1" else (0 if w[2] == "0" else w[2])))
            exp = ref(edges, A); nev += sum(len(v) for v in exp.values())
            if got == exp: ok += 1
            elif first is None:
                bad = [o for o in OUTS if got[o] != exp[o]][0]
                first = (edges, bad, got[bad], exp[bad])
    print("CARRY4 per-(pin,output) transport: %d/%d traces exact (%d reference output edges)" % (ok, n, nev))
    if first: print("first mismatch: in %s\n  output %s gls %s\n  ref %s" % first)
main()
