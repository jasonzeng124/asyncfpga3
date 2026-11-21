#!/usr/bin/env python3
"""Shard B (UNTRUSTED): per corner, bisect the smallest κ at which the cex_ua1 assignment makes ua1
oscillate (watch: > 6 flips). usage: kmap.py NET.json BND.json POSMAP CORNERS..."""
import subprocess, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
NET, BND, PM = sys.argv[1:4]
def osc(c, k):
    out = subprocess.run([sys.executable, "-I", os.path.join(HERE, "simb.py"), NET, BND, "--pairs", "0xC,0x12",
                          "--corner", str(c), "--kappa", str(k), "--tmax", "2000000", "--posmap", PM,
                          "--watch", "SLICE_X2Y18.DLUT.O6", "--maxflips", "6"], capture_output=True, text=True)
    return "WATCH" in out.stderr, ("RESULT OK" in out.stdout)
for c in [float(x) for x in sys.argv[4:]]:
    lo, hi = 0.0, 0.6
    o_hi, _ = osc(c, hi)
    if not o_hi:
        print("corner %.2f: no oscillation up to κ = %.2f" % (c, hi), flush=True); continue
    o_lo, ok_lo = osc(c, lo)
    if o_lo:
        print("corner %.2f: oscillates already at κ = 0" % c, flush=True); continue
    for _ in range(7):
        mid = (lo + hi) / 2
        if osc(c, mid)[0]: hi = mid
        else: lo = mid
    print("corner %.2f: clean at κ = %.4f, oscillates at κ = %.4f" % (c, lo, hi), flush=True)
