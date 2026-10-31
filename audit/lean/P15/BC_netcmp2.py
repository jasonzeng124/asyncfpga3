#!/usr/bin/env python3
"""Auditor P15bc: extends P14's BC_netcmp.py (own extraction, own semantics; does not use formal's
extract.py) to every gcd_hw unit (adds INV cells, 4-port units, MUXF-heavy shifters) and to the
xorshift units. For each unit: (1) Lean cells/outs == the yosys module's z_data cone, cell for cell
(type, INIT, every pin, output order, cone equality); (2) own simulation of the yosys module vs a
Python spec written from bdc's Verilog / the C source, on random + corner vectors.
Usage: python3 -I BC_netcmp2.py SYNTH.json LEANDIR UNIT [UNIT...]"""
import json, re, sys, random

def load_mod(j, unit):
    ms = [k for k in j["modules"] if re.search(r"bdc_fused_%s(\\|$)" % re.escape(unit), k)]
    assert len(ms) == 1, (unit, ms)
    return ms[0], j["modules"][ms[0]]

def parse_lean(path):
    src = open(path).read()
    body = src.split("def cells : List Cell := [", 1)[1].split("]\n\ndef outs", 1)[0]
    outs = src.split("def outs : List W := [", 1)[1].split("]", 1)[0]
    cells = [l.strip().rstrip(",") for l in body.split("\n") if l.strip()]
    return cells, [o.strip() for o in outs.split(",")]

OUTP = {"O", "CO"}
def isout(c, p):
    pd = c.get("port_directions")
    if pd: return pd.get(p) == "output"
    return p in OUTP

def wname(b, inb):
    if b == "0": return ".c0"
    if b == "1": return ".c1"
    if b in inb: return ".inp %d %d" % inb[b]
    return ".net %d" % b

def compare(j, leandir, unit):
    mname, m = load_mod(j, unit)
    inb = {}
    for p, v in m["ports"].items():
        mm = re.fullmatch(r"e(\d+)_data", p)
        if mm and v["direction"] == "input":
            for k, b in enumerate(v["bits"]): inb[b] = (int(mm.group(1)), k)
    drv = {}
    for cn, c in m["cells"].items():
        for p, bits in c["connections"].items():
            if isout(c, p):
                for b in bits:
                    if isinstance(b, int):
                        assert b not in drv, ("two drivers", b); drv[b] = cn
    U = unit[0].upper() + unit[1:]
    cells, outs = parse_lean("%s/%s.lean" % (leandir, U))
    zs = m["ports"]["z_data"]["bits"]
    assert outs == [wname(b, inb) for b in zs], "outs differ"
    used = []; cnt = {"lut": 0, "carry4": 0, "muxf": 0, "inv": 0}
    for line in cells:
        if line.startswith(".lut"):
            mm = re.fullmatch(r"\.lut (\d+) \[(.*)\] (\d+)", line)
            init, ins, out = int(mm.group(1)), [x.strip() for x in mm.group(2).split(",")], int(mm.group(3))
            cn = drv[out]; c = m["cells"][cn]; used.append(cn)
            assert c["type"].startswith("LUT"); n = int(c["type"][3:])
            assert c["connections"]["O"] == [out]
            assert int(c["parameters"]["INIT"], 2) == init, (cn, "INIT")
            assert len(ins) == n and all(ins[i] == wname(c["connections"]["I%d" % i][0], inb) for i in range(n)), (cn, "pins")
            cnt["lut"] += 1
        elif line.startswith(".inv"):
            mm = re.fullmatch(r"\.inv \((.*?)\) (\d+)", line)
            i0, out = mm.group(1), int(mm.group(2)); cn = drv[out]; c = m["cells"][cn]; used.append(cn)
            assert c["type"] == "INV" and c["connections"]["O"] == [out] and wname(c["connections"]["I"][0], inb) == i0
            cnt["inv"] += 1
        elif line.startswith(".carry4"):
            mm = re.fullmatch(r"\.carry4 \((.*?)\) \((.*?)\) \[(.*?)\] \[(.*?)\] (.*)", line)
            ci, cy, di, s, os_ = mm.groups()
            nums = [int(x) for x in os_.split()]
            real = [x for x in nums if x < 10**7]
            cn = drv[real[0]]; c = m["cells"][cn]; used.append(cn); assert c["type"] == "CARRY4"
            con = c["connections"]
            assert ci == wname(con["CI"][0], inb) and cy == wname(con["CYINIT"][0], inb)
            assert [x.strip() for x in di.split(",")] == [wname(b, inb) for b in con["DI"]]
            assert [x.strip() for x in s.split(",")] == [wname(b, inb) for b in con["S"]]
            exp = con.get("O", ["x"] * 4) + con.get("CO", ["x"] * 4)
            assert len(exp) == 8
            for a, b in zip(nums, exp):
                if isinstance(b, int): assert a == b, (cn, "carry outs")
                else: assert a >= 10**7
            cnt["carry4"] += 1
        elif line.startswith(".muxf"):
            mm = re.fullmatch(r"\.muxf \((.*?)\) \((.*?)\) \((.*?)\) (\d+)", line)
            i0, i1, sel, out = mm.groups(); cn = drv[int(out)]; c = m["cells"][cn]; used.append(cn)
            con = c["connections"]; assert c["type"] in ("MUXF7", "MUXF8")
            assert (i0, i1, sel) == tuple(wname(con[p][0], inb) for p in ("I0", "I1", "S"))
            cnt["muxf"] += 1
        else:
            raise SystemExit("unknown lean cell " + line)
    assert len(used) == len(set(used)), "cell listed twice"
    cone = set(); stack = [b for b in zs if isinstance(b, int) and b not in inb]
    while stack:
        b = stack.pop(); cn = drv[b]
        if cn in cone: continue
        cone.add(cn); c = m["cells"][cn]
        for p, bits in c["connections"].items():
            if not isout(c, p):
                stack += [x for x in bits if isinstance(x, int) and x not in inb]
    assert cone == set(used), ("cone mismatch", len(cone), len(used))
    return mname, m, inb, drv, cnt

def simulate(m, inb, drv, invals):
    memo = {}
    def val(b):
        if b == "0": return 0
        if b == "1": return 1
        if b in inb:
            p, k = inb[b]; return (invals.get(p, 0) >> k) & 1
        if b in memo: return memo[b]
        cn = drv[b]; c = m["cells"][cn]; con = c["connections"]; t = c["type"]
        if t.startswith("LUT"):
            n = int(t[3:]); idx = sum(val(con["I%d" % i][0]) << i for i in range(n))
            memo[con["O"][0]] = (int(c["parameters"]["INIT"], 2) >> idx) & 1
        elif t == "INV":
            memo[con["O"][0]] = 1 - val(con["I"][0])
        elif t in ("MUXF7", "MUXF8"):
            memo[con["O"][0]] = val(con["I1"][0]) if val(con["S"][0]) else val(con["I0"][0])
        elif t == "CARRY4":
            cc = val(con["CI"][0]) | val(con["CYINIT"][0])
            for i in range(4):
                s = val(con["S"][i]); d = val(con["DI"][i])
                o = s ^ cc; cc = cc if s else d
                if isinstance(con.get("O", "xxxx")[i], int): memo[con["O"][i]] = o
                if isinstance(con.get("CO", "xxxx")[i], int): memo[con["CO"][i]] = cc
        else:
            raise SystemExit("cell type " + t)
        return memo[b]
    return sum(val(b) << k for k, b in enumerate(m["ports"]["z_data"]["bits"]))

M = 0xffffffff
def s32(x): x &= M; return x - (1 << 32) if x >> 31 else x
# specs written from bdc's Verilog (gcd_kernel.v, read by the auditor) / kernels/xorshift/xorshift.c
SPEC = {
 "uori0": lambda a, b, c, d: (a | b) & M, "uori1": lambda a, b, c, d: (a | b) & M,
 "ucmpi0": lambda a, b, c, d: int(a & M == 0), "ucmpi1": lambda a, b, c, d: int(a & M == 0),
 "ucmpi8": lambda a, b, c, d: int(a & M == 0), "ucmpi10": lambda a, b, c, d: int(a & M == 0),
 "ucmpi2": lambda a, b, c, d: int((a & 1) == (b & 1)), "ucmpi3": lambda a, b, c, d: int((a & b & 1) == 0),
 "uaddi0": lambda a, b, c, d: (a + b) & M,
 "ushrsi": lambda a, b, c, d: (s32(a) >> min(b & M, 63)) & M,
 # ((e2 & e3) != 0) | (signed e0 < signed e1)
 "uori2": lambda a, b, c, d: int((c & d & 1) != 0 or s32(a) < s32(b)),
 "uselect0": lambda a, b, c, d: (a if s32(a) < s32(b) else b) & M,
 # d = e0 - e1; d > -1 ? d : 0 - d   (signed)
 "uselect1": lambda a, b, c, d: ((a - b) & M) if s32(a - b) > -1 else ((-(a - b)) & M),
 "ushli0": lambda a, b, c, d: (a << (b & M)) & M if (b & M) < 64 else 0,
 # xorshift
 "xs_uaddi0": lambda a, b, c, d: (a + 1) & M,
 "xs_ucmpi0": lambda a, b, c, d: int(s32(a) > s32(b)),
 "xs_ucmpi1": lambda a, b, c, d: int(s32(a) < s32(b)),
 "xs_uxori2": lambda a, b, c, d: (a ^ (a << 5)) & M,
 "xs_uxori1": lambda a, b, c, d: (lambda t: (t ^ (t >> 17)) & M)((a ^ (a << 13)) & M),
}
CORNER = [0, 1, 2, 0x7fffffff, 0x80000000, 0x80000001, 0xffffffff, 0xfffffffe, 31, 32, 33]

def specfor(unit, xs):
    if xs: return SPEC["xs_" + unit]
    if unit.startswith("ushrsi"): return SPEC["ushrsi"]
    if unit in ("uori3", "uori4"): return SPEC["uori2"]
    return SPEC[unit]

if __name__ == "__main__":
    xs = "--xs" in sys.argv
    args = [a for a in sys.argv[1:] if a != "--xs"]
    js, leandir = args[0], args[1]
    j = json.load(open(js))
    rnd = random.Random(15)
    for unit in args[2:]:
        mname, m, inb, drv, cnt = compare(j, leandir, unit)
        widths = {}
        for (p, k) in inb.values(): widths[p] = max(widths.get(p, 0), k + 1)
        spec = specfor(unit, xs)
        N = 4000; bad = 0; extra = ""
        def vec():
            v = []
            for p in range(4):
                w = widths.get(p, 0)
                if w == 0: v.append(0); continue
                r = rnd.random()
                if r < 0.15: x = rnd.choice(CORNER) & ((1 << w) - 1)
                elif r < 0.3: x = 0
                else: x = rnd.getrandbits(w)
                v.append(x)
            return v
        for _ in range(N):
            v = vec()
            if unit.startswith("ushrsi"): v[1] = 1            # proved case: e1 = 1
            if unit == "ushli0": v[1] = rnd.randrange(32)      # proved case: k < 32
            if unit in ("uori2", "uori3", "uori4") and rnd.random() < 0.5: v[1] = 1
            if simulate(m, inb, drv, dict(enumerate(v))) != spec(*v): bad += 1
        if unit == "ushli0":
            # outside the proved range: what does the hardware do for k >= 32?
            ob = 0
            for _ in range(500):
                a = rnd.getrandbits(32); k = rnd.choice([32, 33, 63, 64, 1000, 2**31, M, rnd.getrandbits(32) | 32])
                if simulate(m, inb, drv, {0: a, 1: k}) != spec(a, k, 0, 0): ob += 1
            extra = "; k>=32 vs Verilog (0): %d/500 mismatches" % ob
        if unit.startswith("ushrsi"):
            ob = 0
            for _ in range(500):
                a = rnd.getrandbits(32); k = rnd.getrandbits(5)
                if simulate(m, inb, drv, {0: a, 1: k}) != spec(a, k, 0, 0): ob += 1
            extra = "; shift 0..31: %d/500 mismatches" % ob
        print("%-9s %s lean==json cone OK %s widths=%s; sim vs spec: %d/%d mismatches%s"
              % (unit, mname.split("\\")[1], cnt, widths, bad, N, extra))
