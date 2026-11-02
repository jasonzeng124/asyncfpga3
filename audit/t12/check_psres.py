#!/usr/bin/env python3
"""check_psres.py (audit T12): recompute every PSRES line's answer with math.gcd (ignores the tb's own verdict)."""
import math, re, sys
n = ok = bad = hang = 0
for line in open(sys.argv[1], errors="replace"):
    m = re.match(r"PSRES vec=(\d+) a=([0-9a-f]{8}) b=([0-9a-f]{8}) got=(\S+)", line)
    if not m: continue
    n += 1; a, b = int(m.group(2), 16), int(m.group(3), 16)
    if m.group(4).startswith("-"): hang += 1; print("HANG", line.strip()); continue
    if int(m.group(4), 16) == math.gcd(a, b): ok += 1
    else: bad += 1; print("WRONG", line.strip(), "gcd=%08x" % math.gcd(a, b))
print("OWN-ORACLE n=%d ok=%d wrong=%d hang=%d" % (n, ok, bad, hang))
