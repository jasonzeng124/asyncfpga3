#!/usr/bin/env python3
"""Print / check the RAMB18E1 numbers used by Formal/Core/Prims/RamXray.lean.

Reads prjxray-db zynq7/timings/BRAM_L.sdf (the toolchain copy) and prints, in integer ps,
every arc RamXray.lean transcribes. With --check FILE it greps each `name := value` line of
the Lean file and reports DRIFT for any number that differs from the SDF.

    python3 -I bram_xray.py [SDF] [--check ../../Formal/Core/Prims/RamXray.lean]

Conventions (prjxray utils/makesdf.py): IOPATH = (FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX);
TIMINGCHECK = (SLOW_MIN::SLOW_MAX) only. Window used: [-SETUP_MAX, HOLD_MAX].
"""
import hashlib, re, sys

SDF = "/root/dev2/lib/fpgatoolchain/openxc7/share/nextpnr/prjxray-db/zynq7/timings/BRAM_L.sdf"
args = [a for a in sys.argv[1:] if not a.startswith("--")]
chk = None
if "--check" in sys.argv:
    chk = sys.argv[sys.argv.index("--check") + 1]
    args = [a for a in args if a != chk]
path = args[0] if args else SDF
txt = open(path).read()
print("sha256", hashlib.sha256(txt.encode()).hexdigest())

cells = {}
for m in re.finditer(r'\(CELLTYPE "([^"]+)"\)(.*?)\n    \)', txt, re.S):
    cells[m.group(1)] = m.group(2)

def ps(x):
    return int(round(float(x) * 1000))

def iopath(cell, src, dst):
    m = re.search(r"\(IOPATH %s %s \(([-\d.]+)::([-\d.]+)\)\(([-\d.]+)::([-\d.]+)\)\)" % (src, dst), cells[cell])
    return tuple(ps(v) for v in m.groups())

def check(cell, kind, pin, clk):
    m = re.search(r"\(%s %s \(posedge %s\) \(([-\d.]+)::([-\d.]+)\)\)" % (kind, pin, clk), cells[cell])
    return tuple(ps(v) for v in m.groups())

P = "RAMBFIFO36E1"
TDP0 = P + "RAM_MODE_U_RAMB18TDP_U_DOA_REG_U_0_EN_ECC_READ_FALSE"
TDP1 = P + "RAM_MODE_U_RAMB18TDP_U_DOA_REG_U_1_EN_ECC_READ_FALSE"
WF = P + "RAM_MODE_RAMB18TDP_U_WRITE_MODE_U_WF_EN_ECC_READ_FALSE_EN_ECC_WRITE_FALSE"
RF = P + "RAM_MODE_RAMB18TDP_U_WRITE_MODE_U_RF_EN_ECC_READ_FALSE_EN_ECC_WRITE_FALSE"
NC = P + "RAM_MODE_RAMB18TDP_U_WRITE_MODE_U_NC_EN_ECC_READ_FALSE_EN_ECC_WRITE_FALSE"

vals = {}
f0 = iopath(TDP0, "CLKARDCLKU", "DOADOU")
vals.update(coFastLo=f0[0], coFastHi=f0[1], coSlowLo=f0[2], coSlowHi=f0[3])
f1 = iopath(TDP1, "CLKARDCLKU", "DOADOU")
vals.update(coRegFastLo=f1[0], coRegFastHi=f1[1], coRegSlowLo=f1[2], coRegSlowHi=f1[3])
for nm, pin, cell in [("addr", "ADDRAU", P), ("we", "WEAU", P), ("diWF", "DIADIU", WF),
                      ("diRF", "DIADIU", RF), ("diNC", "DIADIU", NC)]:
    s = check(cell, "SETUP", pin, "CLKARDCLKU")
    h = check(cell, "HOLD", pin, "CLKARDCLKU")
    vals[nm + "SetupMin"], vals[nm + "SetupMax"] = s
    vals[nm + "HoldMin"], vals[nm + "HoldMax"] = h
for k, v in vals.items():
    print(f"{k} {v}")
# coverage facts quoted in the notes
for pin in ["ADDRAL", "WEAL", "DIADIL"]:
    print(f"lower-half TDP check for {pin}:", "present" if re.search(r"\b%s\b.*CLKARDCLKL" % pin, txt) else "ABSENT")
print("lower-half TDP CLKARDCLKL->DOADOL:",
      "present" if any("RAMB18TDP" in c and "CLKARDCLKL DOADOL" in b for c, b in cells.items()) else "ABSENT")

if chk:
    lean = open(chk).read()
    bad = 0
    for k, v in vals.items():
        m = re.search(r"\b%s\s*:\s*Int\s*:=\s*\(?(-?\d+)" % k, lean) or re.search(r"\b%s\s*:\s*Nat\s*:=\s*(\d+)" % k, lean)
        if not m:
            print("MISSING", k); bad += 1
        elif int(m.group(1)) != v:
            print("DRIFT", k, m.group(1), "!=", v); bad += 1
    print("check:", "OK" if bad == 0 else f"{bad} problem(s)")
    sys.exit(1 if bad else 0)
