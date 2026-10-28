#!/usr/bin/env python3
"""Fit the pure-link ring sweep: what does one handshake stage actually cost?

    python3 hw/ro_link_fit.py [build/hw/ro_link_sweep]

Two levels of fit, because one alone answers the wrong question.

  WITHIN one RO_DELAY, lap time against ring length.  The slope is
  nanoseconds per stage at that delay; the intercept is whatever a lap pays
  once rather than once per stage.  A single ring measures their sum and
  cannot separate them -- ro_top.v's argument, and the reason there are five
  lengths.

  ACROSS RO_DELAY, that slope against the delay.  The slope of THAT is what
  one bd_delay element costs inside a running handshake, and its intercept is
  the stage with no matched delay at all: the protocol floor.  A kernel stage
  is protocol plus a delay line sized for its logic, and no kernel measurement
  can pull those apart, because every kernel stage has both.

The low-pulse width gets the same treatment and is a genuine cross-check, not
a restatement: it comes from the occupancy census -- asynchronous samples of
the controller nodes -- while the slope comes from lap counts.  Different
signals, different paths through the design.  If the two disagree on the
per-element cost, one of them is wrong and neither number should be quoted.

And the per-element number has an external check waiting for it: verify/
tighten.py's measure_delay_element reads the routed SDF of this very build
and reports one element's one-way delay.  A four-phase stage crosses its
matched line twice per handshake -- once carrying the request up, once
carrying it back down -- so a fully serial delay would cost twice that.  How
close the measured cost lands to 2x is how much of the return to zero is
actually hidden.
"""
import glob, os, re, statistics, sys

RE_RING = re.compile(
    r"\s+ring (\d): +(\d+) stages\s+(\d+) laps\s+([\d.]+) ns/lap"
    r".*?low ([\d.]+) ns(.*)$")


def fit(xs, ys):
    n = len(xs)
    sx, sy = sum(xs), sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    den = n * sxx - sx * sx
    m = (n * sxy - sx * sy) / den
    b = (sy - m * sx) / n
    yb = sy / n
    ssr = sum((y - (m * x + b)) ** 2 for x, y in zip(xs, ys))
    sst = sum((y - yb) ** 2 for y in ys)
    return m, b, (1 - ssr / sst if sst else 0.0)


def main():
    d = sys.argv[1] if len(sys.argv) > 1 else "build/hw/ro_link_sweep"
    runs = {}
    for f in sorted(glob.glob(os.path.join(d, "run_d*.log"))):
        delay = int(re.search(r"run_d(\d+)\.log$", f).group(1))
        pts = []
        for line in open(f):
            m = RE_RING.match(line)
            if m:
                pts.append((int(m.group(2)), float(m.group(4)),
                            float(m.group(5)), "VOID" in m.group(6)))
        if pts:
            runs[delay] = pts
    if not runs:
        sys.exit(f"no run_d*.log under {d}")

    print("== lap time vs ring length, one fit per RO_DELAY ==")
    print("   (only points that cleared the counter-closure gate)")
    print(f"{'delay':>5} {'pts':>4} {'ns/stage':>9} {'icept ns':>9} {'R^2':>8}"
          f" {'low ns':>13}")
    rows = []
    for delay, pts in sorted(runs.items()):
        ok = [p for p in pts if not p[3]]
        if len(ok) < 3:
            print(f"{delay:5d} {len(ok):4d}   too few gated points -- see the "
                  f"header on why a 3-stage ring outruns a 32-bit counter")
            continue
        m, b, r2 = fit([p[0] for p in ok], [p[1] for p in ok])
        lows = [p[2] for p in ok]
        print(f"{delay:5d} {len(ok):4d} {m:9.4f} {b:9.4f} {r2:8.5f}"
              f" {min(lows):6.2f}-{max(lows):<6.2f}")
        rows.append((delay, m, statistics.mean(lows)))

    if len(rows) < 3:
        sys.exit("\nnot enough RO_DELAY points to fit the second level")

    ds = [r[0] for r in rows]
    ms, bs, r2s = fit(ds, [r[1] for r in rows])
    ml, bl, r2l = fit(ds, [r[2] for r in rows])

    print()
    print("== and those slopes against RO_DELAY ==")
    print(f"  from lap counts : ns/stage  = {ms:.4f}*delay + {bs:.4f}"
          f"   (R^2={r2s:.5f})")
    print(f"  from the census : low pulse = {ml:.4f}*delay + {bl:.4f}"
          f"   (R^2={r2l:.5f})")
    agree = 100.0 * abs(ms - ml) / ((ms + ml) / 2)
    print(f"  the two agree on the per-element cost within {agree:.1f}%"
          f"  {'--  ok' if agree < 10 else '<== THEY DO NOT; quote neither'}")

    print()
    print("== the answer ==")
    print(f"  one handshake stage, no matched delay : {bs:.3f} ns")
    print(f"  each bd_delay element on that stage   : {ms:.3f} ns per handshake")

    sdf = os.path.join(os.path.dirname(d.rstrip("/")), "ro_link_ps",
                       "ro_link_ps.sdf")
    if os.path.exists(sdf):
        sys.path.insert(0, "verify")
        try:
            import tighten
            e = tighten.measure_delay_element(open(sdf).read())
        except Exception as exc:                      # noqa: BLE001
            e = None
            print(f"  (routed cross-check unavailable: {exc})")
        if e:
            print()
            print("  cross-check against this build's own routed SDF:")
            print(f"    one element, one way, from the SDF : {e/1000:.3f} ns")
            print(f"    both edges of a four-phase stage   : {2*e/1000:.3f} ns")
            print(f"    measured cost inside the handshake : {ms:.3f} ns"
                  f"  = {100.0*ms/(2*e/1000):.0f}% of that")
            print()
            print("    A matched delay is crossed twice per handshake, once")
            print("    on the way up and once on the return to zero.  The")
            print("    percentage is how much of the second crossing is real")
            print("    rather than hidden behind forward progress.")


if __name__ == "__main__":
    main()
