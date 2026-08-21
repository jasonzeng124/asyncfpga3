#!/usr/bin/env python3
"""GUARD_LO-derated rule A margins for the multiply, across a seed sweep.

Rule A's own guard is max(0.2*peak, 200 ps) and it protects against the DATA
path being slower than the SDF predicts.  It does not protect against the
matched delay chain being FASTER than predicted, which is the direction that
breaks a bundled-data handshake: the request arrives before the data it is
supposed to be shadowing.  cells/verify/skew.py's GUARD_LO = 0.772 is the
95/95 one-sided bound for that, from five silicon ring oscillators built out
of the same bd_delay primitive.

Three columns, because they answer different questions and only the third is
about correctness:

    raw                     the margin tighten.py already prints
    derated + ruleA guard   both conservatisms stacked.  Informative, but a
                            negative here is not by itself a defect -- it
                            double-counts two independent guards
    derated, ordering only  with the chain at the 95/95 low corner, does the
                            request still arrive AFTER the data?  A negative
                            HERE is a real functional exposure on silicon

Usage:  python3 verify/mulderate.py <variant>      # e.g. dsp64
run from a sweep directory holding <variant>.seed*/tighten.txt.
"""
import re, sys, pathlib, statistics as st

GUARD_LO = 0.772
RE = re.compile(r"^\s+(\S+)\s+(\d+) links\s+(\d+) ps\s+req\s+(\d+)\s+peak\s+(\d+)"
                r"\s+guard\s+(\d+)\s+margin\s+(-?\d+)")

def main(variant, inst_prefix="umuli"):
    rows = []
    for p in sorted(pathlib.Path('.').glob(variant + '.seed*/tighten.txt')):
        seed = p.parent.name.split('.')[-1]
        for line in p.read_text().splitlines():
            m = RE.match(line)
            if not m:
                continue
            inst, n, chain, req, peak, guard, margin = m.groups()
            inst = inst.split('.')[-1]
            if not inst.startswith(inst_prefix):
                continue
            n, chain, req, peak, guard, margin = map(
                int, (n, chain, req, peak, guard, margin))
            off = req - chain                  # non-chain part of the request
            dreq = off + GUARD_LO * chain      # chain at the 95/95 low corner
            rows.append(dict(seed=seed, inst=inst, peak=peak, raw=margin,
                             derated=dreq - peak - guard,
                             bare=dreq - peak))
    if not rows:
        print(f"no {inst_prefix}* rows under {variant}.seed*/tighten.txt")
        return 1
    print(f"variant {variant}   samples {len(rows)}   "
          f"seeds {len(set(r['seed'] for r in rows))}   GUARD_LO={GUARD_LO}")
    for key, label in (("raw", "raw margin"),
                       ("derated", "derated (+ruleA guard)"),
                       ("bare", "derated, ordering only")):
        v = sorted(r[key] for r in rows)
        neg = [x for x in v if x < 0]
        print(f"  {label:<26} min {v[0]:>7.0f}  p10 {v[len(v)//10]:>7.0f}  "
              f"med {st.median(v):>7.0f}  max {v[-1]:>7.0f}"
              f"   negative: {len(neg)}/{len(v)}")
    print("  worst samples by derated margin:")
    for r in sorted(rows, key=lambda r: r['derated'])[:6]:
        print(f"    seed {r['seed']:<7} {r['inst']}  peak {r['peak']}  "
              f"raw {r['raw']:>6}  derated {r['derated']:>7.0f}"
              f"  ordering {r['bare']:>7.0f}")
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "dsp64"))
