#!/usr/bin/env python3
"""Audit negative controls on a FASM.
  initflip FASM OUT TILE.SITE.xLUT BIT      flip one INIT bit of one LUT
  pinswap  FASM OUT [--skip N]              swap the IMUX sources of two pins of one LUT
"""
import os, re, sys, collections
DB = os.path.join(os.environ["PRJXRAY_DB_DIR"], "zynq7")
def segbits(kind):
    s = set()
    for l in open(os.path.join(DB, "segbits_%s.db" % kind)):
        s.add(l.split()[0])
    return s
mode = sys.argv[1]; src = sys.argv[2]; out = sys.argv[3]
lines = open(src).read().splitlines()
if mode == "initflip":
    key, bit = sys.argv[4], int(sys.argv[5])
    n = 0
    for i, l in enumerate(lines):
        if l.startswith(key + ".INIT[63:0]"):
            pre, v = l.split("64'b"); bits = list(v)
            j = 63 - bit; bits[j] = "1" if bits[j] == "0" else "0"
            lines[i] = pre + "64'b" + "".join(bits); n += 1
            print("old", l); print("new", lines[i])
    assert n == 1, n
elif mode == "pinswap":
    skip = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    SB = {"L": segbits("int_l"), "R": segbits("int_r")}
    # CLB pin -> IMUX: CLBLL_L_X16Y51.CLBLL_LL_A1.CLBLL_IMUX7
    pinmap = collections.defaultdict(dict)   # (clbtile, lutprefix) -> {pin: imux#}
    for l in lines:
        m = re.match(r"(CLBL[LM]_([LR])_X(\d+)Y(\d+))\.CLBL[LM]_((?:LL|L|M)_[A-D])([1-6])\.CLBL[LM]_IMUX(\d+)$", l)
        if m: pinmap[(m.group(1), m.group(2), m.group(3), m.group(4), m.group(5))][m.group(6)] = int(m.group(7))
    imux = {}
    for i, l in enumerate(lines):
        m = re.match(r"(INT_([LR])_X(\d+)Y(\d+))\.(IMUX(?:_L)?)(\d+)\.(\S+)$", l)
        if m: imux[(m.group(1), int(m.group(6)))] = (i, m.group(2), m.group(5), m.group(7))
    found = 0
    for (clb, side, x, y, lut), pins in sorted(pinmap.items()):
        inttile = "INT_%s_X%sY%s" % (side, x, y)
        ps = sorted(pins)
        for a in range(len(ps)):
            for b in range(a + 1, len(ps)):
                ka, kb = (inttile, pins[ps[a]]), (inttile, pins[ps[b]])
                if ka not in imux or kb not in imux: continue
                ia, sd, pa, sa = imux[ka]; ib, _, pb, sb = imux[kb]
                if sa == sb or "VCC" in sa or "VCC" in sb or "GND" in sa or "GND" in sb: continue
                ta = "INT_%s.%s%d.%s" % (sd, pa, pins[ps[a]], sb); tb = "INT_%s.%s%d.%s" % (sd, pb, pins[ps[b]], sa)
                if ta in SB[sd] and tb in SB[sd]:
                    if found == skip:
                        print("swap", clb, lut, ps[a], ps[b]); print(" ", lines[ia], "->", ta); print(" ", lines[ib], "->", tb)
                        lines[ia] = "%s.%s%d.%s" % (inttile, pa, pins[ps[a]], sb)
                        lines[ib] = "%s.%s%d.%s" % (inttile, pb, pins[ps[b]], sa)
                        open(out, "w").write("\n".join(lines) + "\n"); sys.exit(0)
                    found += 1
    sys.exit("no swappable pair")
open(out, "w").write("\n".join(lines) + "\n")
