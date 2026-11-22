#!/usr/bin/env python3
"""v10table.py SCREEN_LINES...  (shard B, 2026-11-21): v10screen.sh's one-line results -> one markdown row per route:
route, kind, min kappa_lo (bounded / steers), weakest steer, its race-only adversary's first failure, xtol first failure,
latch-fed race (ctlsweep) first failure.  Lines are read from the files given (screen.txt, or a log of them)."""
import re, sys
rows = []
for f in sys.argv[1:]:
    for l in open(f):
        m = re.search(r"(\S+_s\d+) \|", l)
        if not m: continue
        nm = m.group(1); mem = "| MEM |" in l
        st = re.search(r"steers (\d+), bounded (\d+), min kappa_lo (-?[0-9.]+|-)", l)
        wk = re.search(r"weakest (ucond_br\d+)", l)
        adv = re.search(r"weakest-steer adversary first failure: (kappa [0-9.]+ \(([^)]*)\)|none up to [0-9.]+|[^|]*)", l)
        xt = re.search(r"first failure (x=[0-9.]+(: [A-Z]+)?|none to [0-9.]+)\s*\| output", l)
        ct = re.search(r"latch-fed race: (steer \S+ ctl slack ([^|]*?) \| first failure: ([^|]*)|none)", l)
        if "Traceback" in l or "decode failed" in l:   # no decoded net: nothing was screened (2026-11-22: test_int16)
            rows.append((nm, "MEM" if mem else "", "decode failed: not screened", "-", "-", "-", "-")); continue
        rb = re.search(r"rebuild: (.*)", l)
        if rb: rows.append((nm, "MEM" if mem else "", "rebuild: " + rb.group(1)[:60], "", "", "", "")); continue
        a = adv.group(1).strip() if adv else "-"
        a = re.sub(r"\(.*", "", a).strip() if a.startswith("kappa") else a
        rows.append((nm, "MEM" if mem else "", "%s (%s / %s)" % (st.group(3), st.group(2), st.group(1)) if st else "-",
                     wk.group(1) if wk else "-", a, xt.group(1) if xt else ("-" if mem else "?"),
                     ("%s; %s" % (ct.group(2).strip(), ct.group(3).strip())) if ct and ct.group(2) else ("none" if ct else "-")))
def key(r):
    try: return float(r[2].split()[0])
    except ValueError: return 9
print("| route | | min kappa_lo (bounded / steers) | weakest steer | its race-only adversary: first failure | xtol first failure | latch-fed race: ctl slack; first failure |")
print("|---|---|---|---|---|---|---|")
for r in sorted(rows, key=key): print("| " + " | ".join(r) + " |")
