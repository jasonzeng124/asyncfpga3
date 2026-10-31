#!/usr/bin/env python3
"""Auditor P14bc: independent comparison of formal's Lean unit netlists (Formal/Gen/Compute/GcdD/*.lean)
with a yosys JSON netlist, plus an independent Python simulation of each unit's z_data cone.
Usage: python3 -I BC_netcmp.py SYNTH.json LEANDIR UNIT [UNIT...]
Written from scratch; does not import or reuse formal's extract.py."""
import json, re, sys, random

def load_mod(j, unit):
    ms = [k for k in j["modules"] if re.search(r"bdc_fused_%s(\\|$)" % re.escape(unit), k)]
    assert len(ms) == 1, (unit, ms)
    return ms[0], j["modules"][ms[0]]

def parse_lean(path):
    src = open(path).read()
    body = src.split("def cells : List Cell := [", 1)[1].split("]\n\ndef outs", 1)[0]
    outs = src.split("def outs : List W := [", 1)[1].split("]", 1)[0]
    cells = []
    for line in body.split("\n"):
        line = line.strip().rstrip(",")
        if not line: continue
        cells.append(line)
    return cells, [o.strip() for o in outs.split(",")]

def isout(c, p):
    pd = c.get("port_directions")
    if pd: return pd.get(p) == "output"
    return p in ("O", "CO")   # LUTn/MUXF7/8: O; CARRY4: O, CO (only comb types are in the cones)

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
    # output-net -> cell
    drv = {}
    for cn, c in m["cells"].items():
        for p, bits in c["connections"].items():
            if isout(c, p):
                for b in bits:
                    if isinstance(b, int): drv[b] = cn
    U = unit[0].upper() + unit[1:]
    cells, outs = parse_lean("%s/%s.lean" % (leandir, U))
    zs = m["ports"]["z_data"]["bits"]
    assert outs == [wname(b, inb) for b in zs], "outs differ"
    used = set()
    nlut = ncar = nmux = 0
    for line in cells:
        if line.startswith(".lut"):
            mm = re.fullmatch(r"\.lut (\d+) \[(.*)\] (\d+)", line)
            init, ins, out = int(mm.group(1)), [x.strip() for x in mm.group(2).split(",")], int(mm.group(3))
            cn = drv[out]; c = m["cells"][cn]; used.add(cn)
            n = int(c["type"][3:]); assert c["type"].startswith("LUT")
            assert int(c["parameters"]["INIT"], 2) == init, (cn, "INIT")
            assert len(ins) == n and all(ins[i] == wname(c["connections"]["I%d" % i][0], inb) for i in range(n)), (cn, "pins")
            nlut += 1
        elif line.startswith(".carry4"):
            mm = re.fullmatch(r"\.carry4 \((.*?)\) \((.*?)\) \[(.*?)\] \[(.*?)\] (.*)", line)
            ci, cy, di, s, os_ = mm.groups()
            nums = [int(x) for x in os_.split()]
            real = [x for x in nums if x < 10**7]
            cn = drv[real[0]]; c = m["cells"][cn]; used.add(cn); assert c["type"] == "CARRY4"
            con = c["connections"]
            assert ci == wname(con["CI"][0], inb) and cy == wname(con["CYINIT"][0], inb)
            assert [x.strip() for x in di.split(",")] == [wname(b, inb) for b in con["DI"]]
            assert [x.strip() for x in s.split(",")] == [wname(b, inb) for b in con["S"]]
            exp = con["O"] + con["CO"]
            for a, b in zip(nums, exp):
                if isinstance(b, int): assert a == b, (cn, "carry outs")
                else: assert a >= 10**7
            ncar += 1
        elif line.startswith(".muxf"):
            mm = re.fullmatch(r"\.muxf \((.*?)\) \((.*?)\) \((.*?)\) (\d+)", line)
            i0, i1, sel, out = mm.groups(); cn = drv[int(out)]; c = m["cells"][cn]; used.add(cn)
            con = c["connections"]
            assert c["type"] in ("MUXF7", "MUXF8")
            assert (i0, i1, sel) == tuple(wname(con[p][0], inb) for p in ("I0", "I1", "S"))
            nmux += 1
        else:
            raise SystemExit("unknown lean cell " + line)
    # every cell in the cone of z_data appears
    cone = set(); stack = [b for b in zs if isinstance(b, int) and b not in inb]
    while stack:
        b = stack.pop(); cn = drv[b]
        if cn in cone: continue
        cone.add(cn); c = m["cells"][cn]
        for p, bits in c["connections"].items():
            if not isout(c, p):
                stack += [x for x in bits if isinstance(x, int) and x not in inb]
    assert cone == used, ("cone mismatch", len(cone), len(used))
    return mname, m, inb, drv, (nlut, ncar, nmux, len(m["cells"]))

def simulate(m, inb, drv, invals):
    """invals: dict port -> int. Returns z_data int. Own semantics: LUT out = INIT[sum I_k<<k];
    MUXF: S?I1:I0; CARRY4 (UNISIM): c0 = CI|CYINIT; O[i]=S[i]^c_i; c_{i+1} = S[i]?c_i:DI[i]."""
    memo = {}
    def val(b):
        if b == "0": return 0
        if b == "1": return 1
        if b in inb:
            p, k = inb[b]; return (invals[p] >> k) & 1
        if b in memo: return memo[b]
        cn = drv[b]; c = m["cells"][cn]; con = c["connections"]; t = c["type"]
        if t.startswith("LUT"):
            n = int(t[3:]); idx = sum(val(con["I%d" % i][0]) << i for i in range(n))
            init = int(c["parameters"]["INIT"], 2); memo[con["O"][0]] = (init >> idx) & 1
        elif t in ("MUXF7", "MUXF8"):
            memo[con["O"][0]] = val(con["I1"][0]) if val(con["S"][0]) else val(con["I0"][0])
        elif t == "CARRY4":
            cc = val(con["CI"][0]) | val(con["CYINIT"][0])
            for i in range(4):
                s = val(con["S"][i]); d = val(con["DI"][i])
                o = s ^ cc; cc = cc if s else d
                if i < len(con.get("O", [])) and isinstance(con["O"][i], int): memo[con["O"][i]] = o
                if i < len(con.get("CO", [])) and isinstance(con["CO"][i], int): memo[con["CO"][i]] = cc
        else:
            raise SystemExit("cell type " + t)
        return memo[b]
    return sum(val(b) << k for k, b in enumerate(m["ports"]["z_data"]["bits"]))

def s32(x): return x - (1 << 32) if x >> 31 else x
SPEC = {
 "uori0": lambda a, b: (a | b) & 0xffffffff,
 "uori1": lambda a, b: (a | b) & 0xffffffff,
 "ucmpi0": lambda a, b: int(a & 0xffffffff == 0),
 "ucmpi1": lambda a, b: int(a & 0xffffffff == 0),
 "ucmpi8": lambda a, b: int(a & 0xffffffff == 0),
 "ucmpi10": lambda a, b: int(a & 0xffffffff == 0),
 "ucmpi2": lambda a, b: int((a & 1) == (b & 1)),
 "ucmpi3": lambda a, b: int((a & b & 1) == 0),
 "uaddi0": lambda a, b: (a + b) & 0xffffffff,
 # $signed(a) >>> b  (b = shift amount, here generic) -- python >> on negative is arithmetic
 "ushrsi": lambda a, b: (s32(a) >> min(b, 63)) & 0xffffffff,
}

if __name__ == "__main__":
    js, leandir = sys.argv[1], sys.argv[2]
    j = json.load(open(js))
    rnd = random.Random(14)
    for unit in sys.argv[3:]:
        mname, m, inb, drv, cnt = compare(j, leandir, unit)
        widths = {p: max(k for (pp, k) in inb.values() if pp == p) + 1 for p in set(pp for pp, _ in inb.values())}
        spec = SPEC["ushrsi" if unit.startswith("ushrsi") else unit]
        bad = 0; bad_other = 0
        for _ in range(3000):
            a = rnd.getrandbits(widths[0]); b = rnd.getrandbits(widths.get(1, 1)) if 1 in widths else 0
            if unit.startswith("ushrsi"): b1 = 1
            elif unit in ("ucmpi0", "ucmpi1", "ucmpi8", "ucmpi10"):
                b1 = b
                if rnd.random() < 0.3: a = 0
            else: b1 = b
            iv = {0: a, 1: b1}
            if simulate(m, inb, drv, iv) != spec(a, b1): bad += 1
            if unit.startswith("ushrsi"):
                bb = rnd.getrandbits(5)
                if simulate(m, inb, drv, {0: a, 1: bb}) != spec(a, bb): bad_other += 1
        print("%-8s lean==json (luts,carry4,muxf,all-cells-in-module)=%s widths=%s; sim mismatches vs independent spec: %d/3000%s"
              % (unit, cnt, widths, bad, ("; other shift amounts 0..31 mismatches %d/3000" % bad_other) if unit.startswith("ushrsi") else ""))
