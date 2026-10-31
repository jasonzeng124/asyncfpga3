#!/usr/bin/env python3
"""
dsp_latency.py -- how many register stages does each DSP48E1 put on its A
and B operands, as SIMULATED from a routed-shaped JSON (nextpnr's, or the one
fasm2net.py built from the bits)?

    dsp_latency.py JSON --work DIR [--ref ROUTED_JSON] [--cycles N]

Each DSP48E1 is simulated ALONE, with exactly the instance gen.py writes for
it (gen.dsp_config: the decoded register parameters, control words and
CLKINV) and prims.v's model.  Its CE/RST pins get the constants the JSON
connects them to (a live CE/RST is reported SKIP: no stimulus here could
stand for it).  A, B, C and PCIN get fresh random words every cycle (never 0
in A[24:0] or B, so "A frozen at 0" and "A late" look different), and
P sampled before each rising edge is fitted, in Python, against
    P(t) = signed(A[24:0](t - LA)) * signed(B(t - LB))
for LA, LB in 0..5.  The oracle is that multiplication, nothing from the
model.  A stages = LA - MREG - PREG.  A configuration that is not a plain
multiply (X=Y=M, ALUMODE 0, Z=0, A gated off) is reported SKIP.

Output, one line per DSP (by NEXTPNR_BEL):
  DSPLAT <bel> AREG=<a> ACASCREG=.. BREG=.. MREG=.. PREG=.. CE=<pins=v..> : A_STAGES=<n|NEVER> B_STAGES=<n|NEVER>
With --ref, the same bel's AREG/BREG in the reference (the routed JSON the
tool meant to build) is the expectation, and each line ends PASS or FAIL:
  PASS  iff simulated A stages == ref AREG and B stages == ref BREG.
Then `DSPLAT_VERDICT PASS|FAIL|NONE` (NONE: no registered DSP to test) and
exit 0 / 1 / 2.

This is the dsp_areg acceptance PROPERTY (research/data/fid/inventory.md):
the unpatched writer's AREG=1 must simulate as AREG=2 from its bits, the
patched one as AREG=1.  With yosys's AREG=1 mapping (CEA1 tied 0, CEA2 the
enable) AREG=2 means the A1 register never loads, so the decoded unpatched
cell's A stage count is NEVER, not 2 (UG479: A2 loads A1 when AREG=2).
"""
import argparse, json, os, random, re, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import gen          # noqa: E402  (dsp_config, dsp_regs, dsp_reg_conn: the instance gen.py writes)
import dsp_model    # noqa: E402

CONST_T = {"PSEUDO_VCC": 1, "PSEUDO_GND": 0}
CONST_N = {"$PACKER_VCC_NET": 1, "$PACKER_GND_NET": 0}


def load(path):
    top = json.load(open(path))["modules"]["top"]
    cells = top["cells"]
    netname = {}
    for name, nn in top.get("netnames", {}).items():
        for b in nn["bits"]:
            netname.setdefault(b, name)
    netconst = {}
    for cn, c in cells.items():
        if c["type"] in CONST_T:
            for b in c["connections"].get("Y", []):
                netconst[b] = CONST_T[c["type"]]
    for b, n in netname.items():
        if n in CONST_N:
            netconst.setdefault(b, CONST_N[n])
    return cells, netname, netconst


def regs_of(c):
    rp, _pins, _why = gen.dsp_regs(c)
    return rp


def plan(cells, netname, netconst):
    """-> [(bel, cname, cfg text, {pin: 0/1}, rp, why)]"""
    out = []
    for cn, c in sorted(cells.items(), key=lambda kv: kv[1]["attributes"].get("NEXTPNR_BEL", kv[0])):
        if c["type"] != gen.DSP_T:
            continue
        bel = c["attributes"].get("NEXTPNR_BEL", cn)
        rp = regs_of(c)
        why = None
        try:
            zmux, acasc, extra = gen.dsp_config(cn, c, netname)
        except SystemExit as e:
            out.append((bel, cn, None, {}, rp, "REFUSED by gen.py: %s" % str(e)[:200]))
            continue
        cfg = ".ZMUX(%d), .ACASC(%d)%s" % (zmux, acasc, extra)
        m = dict(re.findall(r"\.(\w+)\((\d+)\)", cfg))
        plain = (zmux == 0 and m.get("XMUX", "1") == "1" and m.get("YMUX", "1") == "1"
                 and m.get("ALUMODE", "0") == "0" and m.get("AGATE", "0") == "0"
                 and m.get("CIN", "0") == "0" and m.get("MUNK", "0") == "0")
        if not plain:
            why = "SKIP: not a plain multiply (%s)" % cfg
        ce = {}
        for p, fixed in gen.dsp_reg_conn(c):
            if p == "CLK":
                continue
            if fixed:
                ce[p] = int(fixed[-1])
            else:
                b = c["connections"][p][0]
                if b in netconst:
                    ce[p] = netconst[b]
                elif isinstance(b, str):
                    ce[p] = int(b)
                else:
                    why = why or "SKIP: %s is a live net (%s)" % (p, netname.get(b, b))
        out.append((bel, cn, cfg, ce, rp, why))
    return out


def tb_text(items, cycles, seed):
    rnd = random.Random(seed)
    L = ["`timescale 1ps/1ps", "module tb_dsplat;", "  reg clk;", "  initial clk = 0;",
         "  always #5000 clk = ~clk;"]
    for k, (bel, cn, cfg, ce, rp, why) in enumerate(items):
        if cfg is None:
            continue
        acasc = ".ACASC(1)" in cfg
        L.append("  reg [29:0] a%d; reg [17:0] b%d; reg [47:0] c%d, pc%d; wire [47:0] p%d;" % ((k,) * 5))
        pins = []
        for i in range(30):
            pins.append(".%s%d(a%d[%d])" % ("ACIN" if acasc else "A", i, k, i))
        pins += [".B%d(b%d[%d])" % (i, k, i) for i in range(18)]
        pins += [".C%d(c%d[%d])" % (i, k, i) for i in range(48)]
        pins += [".PCIN%d(pc%d[%d])" % (i, k, i) for i in range(48)]
        pins += [".P%d(p%d[%d])" % (i, k, i) for i in range(48)]
        if dsp_model.registered(rp):
            pins.append(".CLK(clk)")
            pins += [".%s(1'b%d)" % (p, v) for p, v in sorted(ce.items())]
        L.append("  DSP48E1_DSP48E1 #(%s) u%d (%s);" % (cfg, k, ", ".join(pins)))
    L.append("  integer t;")
    L.append("  initial begin")
    for t in range(cycles):
        L.append("    #(%d - $time);" % (10000 * t + 2000))          # 3 ns after the falling edge
        for k, (bel, cn, cfg, ce, rp, why) in enumerate(items):
            if cfg is None:
                continue
            a = rnd.getrandbits(25) or 12345
            b = rnd.getrandbits(18) or 321
            L.append("    a%d = 30'h%x; b%d = 18'h%x; c%d = 48'h%x; pc%d = 48'h%x;"
                     % (k, a, k, b, k, rnd.getrandbits(48), k, rnd.getrandbits(48)))
        L.append("    #(%d - $time);" % (10000 * t + 4000))          # 1 ns before rising edge t
        for k, (bel, cn, cfg, ce, rp, why) in enumerate(items):
            if cfg is None:
                continue
            L.append('    $display("S %d %d %%h %%h %%h", a%d, b%d, p%d);' % (k, t, k, k, k))
    L.append("    $finish;")
    L.append("  end")
    L.append("endmodule")
    return "\n".join(L) + "\n"


def sx(v, w):
    v &= (1 << w) - 1
    return v - (1 << w) if v >> (w - 1) else v


def fit(samples):
    """samples: [(a, b, p)] per cycle.  -> (LA, LB) or None, and whether P
    was 0 on every cycle."""
    n = len(samples)
    allzero = all(p == 0 for _, _, p in samples[6:])
    for la in range(6):
        for lb in range(6):
            ok = True
            for t in range(6, n):
                a = samples[t - la][0] if t - la >= 0 else 0
                b = samples[t - lb][1] if t - lb >= 0 else 0
                want = (sx(a, 25) * sx(b, 18)) & ((1 << 48) - 1)
                if samples[t][2] != want:
                    ok = False
                    break
            if ok:
                return (la, lb), allzero
    return None, allzero


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json")
    ap.add_argument("--work", required=True, type=Path)
    ap.add_argument("--ref")
    ap.add_argument("--cycles", type=int, default=40)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    a.work.mkdir(parents=True, exist_ok=True)
    cells, netname, netconst = load(a.json)
    items = plan(cells, netname, netconst)
    ref = {}
    if a.ref:
        rc, rn, _ = load(a.ref)
        for cn, c in rc.items():
            if c["type"] == gen.DSP_T:
                ref[c["attributes"].get("NEXTPNR_BEL", cn)] = regs_of(c)
    (a.work / "tb_dsplat.v").write_text(tb_text(items, a.cycles, a.seed))
    prims = HERE.parent / "prims.v"
    r = subprocess.run(["iverilog", "-gspecify", "-o", str(a.work / "dsplat.vvp"),
                        str(a.work / "tb_dsplat.v"), str(prims)], capture_output=True, text=True)
    if r.returncode:
        print("DSPLAT_VERDICT ERROR: iverilog: %s" % r.stderr[-400:])
        sys.exit(2)
    r = subprocess.run(["vvp", "-n", str(a.work / "dsplat.vvp")], capture_output=True, text=True)
    (a.work / "dsplat.log").write_text(r.stdout + r.stderr)
    S = {}
    for line in r.stdout.splitlines():
        f = line.split()
        if len(f) == 6 and f[0] == "S":
            k, t = int(f[1]), int(f[2])
            vals = [None if "x" in v or "z" in v else int(v, 16) for v in f[3:]]
            S.setdefault(k, {})[t] = vals
    verdicts = []
    for k, (bel, cn, cfg, ce, rp, why) in enumerate(items):
        head = "DSPLAT %s %s CE/RST={%s}" % (bel, " ".join("%s=%d" % (x, rp[x]) for x in dsp_model.REGS),
                                             " ".join("%s=%d" % kv for kv in sorted(ce.items())))
        if not dsp_model.registered(rp) and a.ref and not dsp_model.registered(ref.get(bel, {})):
            print("%s : combinational (not part of this property)" % head)
            continue
        if why:
            print("%s : %s" % (head, why))
            verdicts.append(False if "REFUSED" in why else None)
            continue
        smp = [S.get(k, {}).get(t) for t in range(a.cycles)]
        if any(s is None or None in s for s in smp[6:]):
            res, stages = "P has x/z", (None, None)
            stages_txt = "A_STAGES=? B_STAGES=? (%s)" % res
        else:
            lat, allzero = fit(smp)
            if lat is None:
                stages = ("NEVER", "NEVER") if allzero else ("?", "?")
                stages_txt = ("A_STAGES=NEVER B_STAGES=NEVER (P = 0 on every cycle: an operand register "
                              "never loads)" if allzero else "A_STAGES=? B_STAGES=? (P fits no A(t-LA)*B(t-LB))")
            else:
                off = rp["MREG"] + rp["PREG"]
                stages = (lat[0] - off, lat[1] - off)
                stages_txt = "A_STAGES=%d B_STAGES=%d (P = A(t-%d)*B(t-%d), MREG+PREG=%d)" % (
                    stages[0], stages[1], lat[0], lat[1], off)
        if a.ref:
            want = ref.get(bel)
            if want is None:
                print("%s : %s : no such DSP in --ref : FAIL" % (head, stages_txt))
                verdicts.append(False)
                continue
            ok = stages == (want["AREG"], want["BREG"])
            print("%s : %s : ref AREG=%d BREG=%d : %s" % (head, stages_txt, want["AREG"], want["BREG"],
                                                         "PASS" if ok else "FAIL"))
            verdicts.append(ok)
        else:
            print("%s : %s" % (head, stages_txt))
    tested = [v for v in verdicts if v is not None]
    if not a.ref:
        sys.exit(0)
    if not tested:
        print("DSPLAT_VERDICT NONE (no registered DSP48E1 to test)")
        sys.exit(2)
    ok = all(tested)
    print("DSPLAT_VERDICT %s (%d DSP(s) tested)" % ("PASS" if ok else "FAIL", len(tested)))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
