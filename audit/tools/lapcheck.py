#!/usr/bin/env python3
"""lapcheck.py -- stall and double-completion check for full-stack GLS sweep logs.

    lapcheck.py <run_dir_with_sweep/>... [--min-gap-ps 1000] [--tend-ps 150000000]

research's seeds_fid judge passes a run when every vector has laps > 0 and the summed errs are 0 (audit r23 I).
That misses (a) a vector that stalls after a few laps and (b) a completion that pulses twice (two LAP/OK events a
few ps apart, counted as two correct laps; audit r23 M). Per vector this prints laps, errs, the last-lap time, the
number of LAP pairs closer than --min-gap-ps among the printed LAP lines (printing stops at the bench's QUIET),
and a verdict: STALL if the last lap is earlier than TEND minus 3 median lap periods, DOUBLE if any close pair.
"""
import argparse, glob, os, re, statistics, sys

ap = argparse.ArgumentParser()
ap.add_argument("runs", nargs="+")
ap.add_argument("--min-gap-ps", type=int, default=1000)
ap.add_argument("--tend-ps", type=int, default=None, help="default: t_end from the SUMMARY line")
a = ap.parse_args()

bad = 0
for run in a.runs:
    vlogs = glob.glob(os.path.join(run, "sweep", "v*.log"))
    if not vlogs:
        print(f"{run}: NO VECTOR LOGS (build failed or not run)"); bad += 1; continue
    for f in sorted(glob.glob(os.path.join(run, "sweep", "v*.log")), key=lambda p: int(re.findall(r"v(\d+)", p)[-1])):
        t = open(f, errors="replace").read()
        m = re.search(r"SUMMARY vec=(\d+) laps=(\d+) errs=(\d+) oks=(\d+).*?t_end=(\d+).*?t_last_lap=(\d+)", t)
        if not m:
            print(f"{f}: NO SUMMARY"); bad += 1; continue
        vec, laps, errs, oks, tend, tlast = map(int, m.groups())
        tend = a.tend_ps or tend
        lt = [int(x) for x in re.findall(r"^LAP \d+ t=(\d+)", t, re.M)]
        gaps = [y - x for x, y in zip(lt, lt[1:])]
        close = sum(g < a.min_gap_ps for g in gaps)
        wide = [g for g in gaps if g >= a.min_gap_ps]
        period = statistics.median(wide) if wide else None
        v = []
        if errs: v.append("ERR")
        if laps == 0: v.append("NOLAP")
        if period and tend - tlast > 3 * period: v.append("STALL")
        if close: v.append("DOUBLE")
        bad += bool(v)
        print(f"{run} vec {vec:2d} laps {laps:6d} errs {errs} oks {oks} last {tlast} period {period} close_pairs {close} "
              f"{'/'.join(v) or 'ok'}")
print("LAPCHECK", "FLAGS" if bad else "CLEAN", bad)
sys.exit(1 if bad else 0)
