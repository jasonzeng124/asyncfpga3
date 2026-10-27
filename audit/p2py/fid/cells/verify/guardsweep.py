#!/usr/bin/env python3
"""What does rule E's guardband COST?  One row per width, on one routed design.

    verify/guardsweep.py [sdf]

Rule E's GUARD_LO/GUARD_HI come from five ring oscillators measured on silicon,
and the honest objection to them is statistical rather than physical: they are
the observed min and max of five samples used as if they bounded the
population.  They do not.  A one-sided 95/95 normal tolerance interval at n=5
(k ~ 4.20) on the same residuals lands near 0.79/1.15, roughly 2.5x the band.

Widening is only worth arguing about once the price is known, which is what
this prints: violations, links touched, and total bd_delay elements at each
width.  Measured on gcd_hw the raw row is ZERO -- nothing fails nominally -- so
the whole question is how much scatter to insure against, and going from the
shipping band to +/-15% cost nine extra LUT1s.  The curve is also STEPPED (1.5x
and 2x both sat at 7 violations), so pick the far side of a plateau rather than
the near side.

What this cannot tell you, and you must check before choosing: whether the
links it names sit in the kernel's inner loop, where a couple of elements is
~550 ps paid per iteration rather than once.

It monkeypatches the two constants and re-runs skew.main(), so it reports what
rule E would say -- it does not change what rule E does say.
"""
import sys, pathlib, io, contextlib, re, math
V = pathlib.Path(__file__).resolve().parent
SDF = sys.argv[1] if len(sys.argv) > 1 else str(
    V.parent / "build/hw/gcd_hw/gcd_hw.sdf")
sys.path.insert(0, str(V))
sys.argv = [sys.argv[0], SDF]
import skew
# Force every site's row to print, ok or not -- main() otherwise prints only
# violations.  Without this, a case with 0 violations leaves no margin lines
# behind at all, and "worst margin" cannot be read off a width that passes.
skew.VERBOSE = True

cases = [
    ("raw (no guardband)",      1.000, 1.000),

    ("MEASURED (shipping)",     0.915, 1.022),
    ("1.5x the band",           0.873, 1.033),
    ("2x the band",             0.830, 1.044),

    ("+/-15% flat",             0.850, 1.150),
    ("95/95 tolerance (n=5)",   0.772, 1.155),

]
print(f"{'guardband':<22} {'lo':>6} {'hi':>6} {'viol':>5} {'links':>6} "
      f"{'elems':>6} {'worst':>7}")
for name, lo, hi in cases:
    skew.GUARD_LO, skew.GUARD_HI = lo, hi
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        try:
            skew.main()
        except SystemExit:
            pass
    out = buf.getvalue()
    m = re.search(r"(\d+) select gates, (\d+) measured, (\d+) violated", out)
    viol = int(m.group(3)) if m else -1
    fixes = re.findall(r"fix: (\d+) more bd_delay element\(s\) on (\S+)", out)
    per = {}
    for n, link in fixes:
        per[link] = max(per.get(link, 0), int(n))
    # Worst (most negative, or least positive) GUARDED margin over every site
    # measured at this width -- available for every row because VERBOSE is
    # forced on above, not just the violating ones.
    margins = [int(g) for _, g in
               re.findall(r"margin ([+-]\d+) ps raw, ([+-]\d+) ps guarded", out)]
    worst = min(margins) if margins else None
    wstr = f"{worst:+d}" if worst is not None else "n/a"
    print(f"{name:<22} {lo:>6.3f} {hi:>6.3f} {viol:>5} {len(per):>6} "
          f"{sum(per.values()):>6} {wstr:>7}")
