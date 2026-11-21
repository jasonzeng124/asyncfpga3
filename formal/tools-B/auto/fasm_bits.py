#!/usr/bin/env python3
"""tools-B/auto/fasm_bits.py IN.fasm OUT.fasm  (shard B): prjxray's bit2fasm writes a DSP site's input-inverter bits as one
vector line (`...ZIS_OPMODE_INVERTED[2:0] = 3'b101`); nextpnr writes one line per set bit (`...ZIS_OPMODE_INVERTED[0]`),
which is the form margin/dsp/decode_dsp.py reads. This rewrites only ZIS_*_INVERTED vector lines into per-bit lines
(bit i present iff it is 1 in the value); every other line is copied unchanged. Prints how many lines were rewritten."""
import re, sys
V = re.compile(r"^(\S+\.ZIS_[A-Z]+_INVERTED)\[(\d+):(\d+)\]\s*=\s*(\d+)'b([01]+)\s*$")
n = 0; out = []
for line in open(sys.argv[1]):
    m = V.match(line.strip())
    if not m: out.append(line); continue
    base, hi, lo, w, bits = m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)), m.group(5)
    assert w == hi - lo + 1 == len(bits), line
    for k, b in enumerate(reversed(bits)):
        if b == "1": out.append("%s[%d]\n" % (base, lo + k))
    n += 1
open(sys.argv[2], "w").writelines(out); print("fasm_bits: %d vector lines split" % n)
