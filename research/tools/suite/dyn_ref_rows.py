#!/usr/bin/env python3
"""dyn_ref_rows.py DYNROOT KERNEL... -- Dynamatic's figures from routed periods (research/tools/suite/dyn_all.sh's
output under DYNROOT/K/): one row per kernel for research/tools/suite/dynamatic_ref.tsv (ns per iteration) and, with
--lat, rows for research/data/suite/dynamatic/dynamatic_lat.tsv (latency per call).

A kernel gets a row only when (1) dyn_vsim.py found the exported Verilog equal to dynamatic_est.py's model in every
call -- results (and arrays) equal to the C, cycles equal -- and (2) dyn_route.sh routed it on every seed asked. Then:
  ns per iteration = the routed period (mean over the seeds) x dynamatic_est.py's simulated cycles per iteration
  (its fit over the calls), tag "measured, N routes";
  latency per call = the simulated cycles of each call x the routed period (mean over the seeds), per the calls in
  the existing dynamatic_lat.tsv row (same vectors), tag "cycles simulated, period measured (N routes)".
Kernels without a loop get no ns-per-iteration row (as before). Prints the rows; nothing is written."""
import os
import re
import statistics
import sys


def read_kernel(root, k):
    d = os.path.join(root, k)
    try:
        vs = open(os.path.join(d, "vsim.txt")).read()
        rt = open(os.path.join(d, "route.txt")).read()
        est = open(os.path.join(d, "est.txt")).read()
    except OSError as e:
        return None, "missing %s" % os.path.basename(e.filename)
    m = re.search(r"dyn_vsim \S+: (\d+) calls, (\d+) differ", vs)
    if not m or m.group(2) != "0":
        return None, "Verilog check not clean (%s)" % (m.group(0) if m else vs.strip().splitlines()[-1:] or "no line")
    ncalls = int(m.group(1))
    ps = [float(x) for x in re.findall(r"seed \d+ Fmax [0-9.]+ MHz period ([0-9.]+) ns", rt)]
    seeds = re.findall(r"seed (\d+) Fmax", rt)
    fails = re.findall(r"seed (\d+) (?:PNR FAILED|: no Fmax)", rt)
    if not ps or fails:
        return None, "route failed on seed(s) %s" % (fails or "all")
    if not re.search(r"^%s period %d routes:" % (re.escape(k), len(ps)), rt, re.M):
        return None, "routes not finished (%d so far)" % len(ps)
    sha = re.search(r"nextpnr ([0-9a-f]{16})", rt)
    cpi = re.search(r"^cycles per iteration: ([0-9.]+)", est, re.M)
    cyc = [int(x) for x in re.findall(r"^\s*call .*?cycles\s+(\d+)\s+result", est, re.M)]
    return dict(k=k, n=ncalls, periods=ps, seeds=seeds, mean=statistics.mean(ps), lo=min(ps), hi=max(ps),
                sha=sha.group(1) if sha else "?", cpi=float(cpi.group(1)) if cpi else None, cycles=cyc), None


def main():
    root = sys.argv[1]
    lat = "--lat" in sys.argv
    ks = [a for a in sys.argv[2:] if not a.startswith("--")]
    for k in ks:
        r, why = read_kernel(root, k)
        if r is None:
            print("# %s: no row (%s)" % (k, why), file=sys.stderr)
            continue
        how = ("Dynamatic on-merges buffers, exported by research/tools/suite/dyn_export.py (checked: %d calls, results "
               "and cycles = dynamatic_est.py's model, results = the C), routed by dyn_route.sh on seeds %s "
               "(period %.2f ns mean, %.2f-%.2f; nextpnr %s)" % (r["n"], ",".join(r["seeds"]), r["mean"], r["lo"],
                                                                 r["hi"], r["sha"]))
        if not lat:
            if r["cpi"] is None:
                print("# %s: no loop (no ns-per-iteration row); period %.3f ns" % (k, r["mean"]), file=sys.stderr)
                continue
            print("%s\t%.2f\tmeasured, %d routes\t%s x %.2f simulated cycles per iteration" % (
                k, r["mean"] * r["cpi"], len(r["periods"]), how, r["cpi"]))
        else:
            if not r["cycles"]:
                continue
            print("%s\t%d\t%.2f\tcycles simulated, period measured (%d routes)\t%s" % (
                k, len(r["cycles"]), statistics.mean(r["cycles"]) * r["mean"], len(r["periods"]), how))


if __name__ == "__main__":
    main()
