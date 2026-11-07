# Compare tb_c2 runs with the closed form of GLSResolve.run_runt / run_wide.
# Expected edges are computed from the Lean model (t0 = tb + T2, L = TW + T3), using only the
# decision the resolver printed (reject / commit / back and trp), never the q trace itself.
import sys, re
L, T2, TR = 200, 50, 50          # loop, b arc, rst arc (tb_c2.v parameters)
WIN = 150
bad = 0; n = 0; outc = {}
for fn in sys.argv[1:]:
    ev = []; pulses = []; dec = {}
    for line in open(fn):
        m = re.match(r"(\d+) q=(\S)", line)
        if m: ev.append((int(m.group(1)), m.group(2))); continue
        m = re.match(r"PULSE tb=(\d+) w=(\d+)", line)
        if m: pulses.append((int(m.group(1)), int(m.group(2)))); continue
        m = re.match(r"RUNT \S+ t=(\d+) runt=(\d+) .*rejected", line)
        if m: dec[int(m.group(1))] = ("reject", 0, None); continue
        m = re.match(r"META \S+ t=(\d+) runt=(\d+) loop=\d+ delta=(-?\d+) runt_val=1 -> (\d) after (\d+) ps", line)
        if m:
            d = int(m.group(3)); r = "commit" if m.group(4) == "1" else "back"
            # resolve: commit iff delta > 0 ; back iff -win/2 < delta <= 0 (fid_core.vh:83,92)
            if (r == "commit") != (d > 0) or d <= -(WIN // 2): print("DECISION MISMATCH", fn, line); bad += 1
            # ResLaw: trp = 0 when 2|delta| >= win (fid_core.vh:95-98)
            if 2 * max(abs(d), 1) >= WIN and int(m.group(5)) != 0: print("RESLAW MISMATCH", line); bad += 1
            dec[int(m.group(1))] = (r, int(m.group(5)), d)
    for i, (tb, w) in enumerate(pulses):
        n += 1
        t0 = tb + T2
        trst = tb + w + 10000            # rst rises (tb_c2.v)
        if w >= L:
            exp = [(t0, '1'), (trst + TR, '0')]; key = "wide"
        else:
            if (t0 + w) not in dec: print("NO DECISION", fn, tb, w); bad += 1; continue
            r, trp, d = dec[t0 + w]; key = r + ("0" if r == "commit" and trp == 0 else "")
            if r in ("reject", "back"): exp = [(t0, '1'), (t0 + w, '0')]
            elif trp == 0: exp = [(t0, '1'), (trst + TR, '0')]
            else: exp = [(t0, '1'), (t0 + w, '0'), (t0 + w + trp, '1'), (trst + TR, '0')]
        outc[key] = outc.get(key, 0) + 1
        got = [(t, v) for (t, v) in ev if tb < t <= trst + 2000]
        # collapse non-changes ($monitor can print a same-value line after a 0-width glitch)
        g2 = []
        for t, v in got:
            if not g2 or g2[-1][1] != v: g2.append((t, v))
        if g2 != exp: print("MISMATCH", fn, tb, w, exp, got); bad += 1
print("pulses checked:", n, "outcomes:", outc, "mismatches:", bad)
