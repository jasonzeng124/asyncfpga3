#!/usr/bin/env python3
"""ring2_judge.py MEASURED_TSV PREDICTED_TSV -- the band-transfer test on a SECOND ring route, judged against
predictions committed BEFORE the board ran it.

    python3 research/tools/ring2_judge.py cells/build/hw/ro_many_top/measured.tsv \
        research/board/ro_many_2/predicted.tsv; echo "exit $?"

MEASURED_TSV: hw/ro_many_measure.py's RO_MEAS_TSV output (g b links measured_ps ...).
PREDICTED_TSV: ring, links, fastmin_ps, slowmax_ps, band_ps (cells/gls/fid/ring_predict.py on this route's prjxray
SDF; band_ps = FAST_MIN + 0.288 * (SLOW_MAX - FAST_MIN), the band ring128 fixed on the first route).

Pass criterion (acceptance.py's, unchanged): the median error and every ring length's median error of
band_ps / measured - 1 within +/-5%, and every ring between its FAST_MIN and SLOW_MAX prediction. It also prints
the second route's own x (median of (measured - FAST_MIN) / (SLOW_MAX - FAST_MIN)) next to the first route's 0.288.
Prints "=== PASS ===" or "=== FAIL: ... ===" and exits 0 / 1.
"""
import statistics as st
import sys


def main():
    meas = {}
    for ln in open(sys.argv[1]).read().splitlines()[1:]:
        f = ln.split("\t")
        meas["g%s.b%s" % (f[0], f[1])] = (int(f[2]), float(f[3]))
    errs, xs, out, bylen = [], [], 0, {}
    for ln in open(sys.argv[2]).read().splitlines()[1:]:
        r, n, lo, hi, band = ln.split("\t")
        if r not in meas:
            print("missing measurement for %s" % r)
            out += 1
            continue
        m = meas[r][1]
        lo, hi, band = float(lo), float(hi), float(band)
        e = 100 * (band / m - 1)
        errs.append(e)
        bylen.setdefault(int(n), []).append(e)
        xs.append((m - lo) / (hi - lo))
        if not lo <= m <= hi:
            out += 1
            print("outside [FAST_MIN, SLOW_MAX]: %s measured %.1f, %.0f-%.0f" % (r, m, lo, hi))
    if not errs:
        sys.exit("ring2_judge: nothing to compare")
    med = st.median(errs)
    meds = {n: st.median(v) for n, v in sorted(bylen.items())}
    print("rings %d; band_ps error median %+.2f%% (p05 %+.2f, p95 %+.2f); by length %s"
          % (len(errs), med, sorted(errs)[int(.05 * len(errs))], sorted(errs)[int(.95 * len(errs)) - 1],
             " ".join("%d:%+.2f" % kv for kv in meds.items())))
    print("this route's own x: median %.4f (first route: 0.288)" % st.median(xs))
    why = []
    if abs(med) > 5 or any(abs(v) > 5 for v in meds.values()):
        why.append("median errors beyond +/-5%")
    if out:
        why.append("%d ring(s) missing or outside the corners" % out)
    print("=== PASS ===" if not why else "=== FAIL: %s ===" % "; ".join(why))
    sys.exit(0 if not why else 1)


if __name__ == "__main__":
    main()
