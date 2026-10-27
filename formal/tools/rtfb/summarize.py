#!/usr/bin/env python3
"""Probe C-10f: mean / range of RT_FB results over placer seeds (evidence, Python).

    python3 -I formal/tools/rtfb/summarize.py REPORT.rt.txt... [--f2l-dir DIR]

Reads the per-seed reports written by rt_all.py (10d) / rtfb_design.py (10f) and,
for the pin statistics, the fasm2lean JSON next to each report (site-pin delays per
physical pin).  Prints: per variant, failing count per seed, mean, range, worst slack;
the physical pin the feedback lands on (all / failing, slowE) and the prjxray
site-pin delay of each pin.
"""
import json
import os
import re
import sys
from collections import Counter, defaultdict

VARIANTS = ["indep", "fast", "slow", "fastE", "slowE", "sdf"]


def parse(path):
    rows = []
    hdr = None
    for line in open(path):
        f = line.split()
        if f and f[0] == "LUT":
            hdr = f
            continue
        if hdr and f and f[0].startswith("SLICE"):
            d = dict(zip(hdr, f))
            rows.append(d)
    return hdr, rows


def main():
    reps = [a for a in sys.argv[1:] if not a.startswith("--")]
    allrows = []
    print("%-28s %s" % ("report", "  ".join("%13s" % v for v in VARIANTS)))
    fails = defaultdict(list); worst = defaultdict(list)
    for r in reps:
        hdr, rows = parse(r)
        allrows.append((r, rows))
        cells = []
        for v in VARIANTS:
            sl = [int(x[v]) for x in rows]
            nf = sum(1 for s in sl if s < 0)
            fails[v].append(nf); worst[v].append(min(sl))
            cells.append("%3d/%-3d %5d" % (nf, len(rows), min(sl)))
        print("%-28s %s" % (os.path.basename(r).replace(".rt.txt", ""), "  ".join("%13s" % c for c in cells)))
    print("failing C-elements: mean [min..max]; worst slack ps: mean [min..max]")
    for v in VARIANTS:
        f, w = fails[v], worst[v]
        print("  %-6s fail %5.1f [%d..%d]   worst %7.1f [%d..%d]" % (v, sum(f) / len(f), min(f), max(f),
                                                                  sum(w) / len(w), min(w), max(w)))
    # pins
    pin_all, pin_fail = Counter(), Counter()
    nb_fail = Counter()
    sitepin = defaultdict(set)
    for r, rows in allrows:
        js = r.replace(".rt.txt", ".f2l.json")
        if os.path.exists(js):
            for l in json.load(open(js))["luts"]:
                for p in l["pins"]:
                    sitepin[p["pin"][1]].add(tuple(p["sitepin_delay_ps"]))
        for x in rows:
            k = x["fb"][1]
            pin_all[k] += 1
            if int(x["slowE"]) < 0:
                pin_fail[k] += 1
                for n in x["neighbours"].split(","):
                    nb_fail[n[1]] += 1
    print("feedback physical pin (all C-elements / failing at slowE), and prjxray site-pin delay "
          "[fast_min fast_max slow_min slow_max] ps")
    for k in "123456":
        print("  pin %s: %4d / %3d   site pin %s" % (k, pin_all[k], pin_fail[k], sorted(sitepin[k])))
    print("neighbour pins of the failing C-elements (slowE):", dict(sorted(nb_fail.items())))


if __name__ == "__main__":
    main()
