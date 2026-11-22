#!/usr/bin/env python3
"""dyn_apply.py DYNROOT [--write] -- put Dynamatic's ROUTED periods (research/tools/suite/dyn_all.sh's output under
DYNROOT/K/) into the two tables research/tools/suite/suite_table.py reads:

  research/tools/suite/dynamatic_ref.tsv  (ns per iteration; a row here overrides the estimator's table): every kernel
      whose export dyn_vsim.py found exact and that routed on every seed gets "period (mean over the seeds) x the
      estimator's simulated cycles per iteration", tagged "measured, N routes" (dyn_ref_rows.py).  A row of the form
      "simulated A + B cycles x period P" (gcd's composite unit) keeps its cycles and takes the routed period.
  research/data/suite/dynamatic/dynamatic_lat.tsv  (latency per call on the suite's calls): the same kernels' rows
      keep their simulated cycles per call and take the routed period: mean ns per call recomputed, the period column
      replaced, tagged "cycles simulated, period measured (N routes)".

Kernels without a clean check or a full set of routes keep their rows (estimates stay estimates).  Prints every change
(old -> new); --write writes both files."""
import os
import re
import statistics
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dyn_ref_rows as R  # noqa: E402

REF = os.path.join(HERE, "dynamatic_ref.tsv")
LAT = os.path.join(HERE, "..", "..", "data", "suite", "dynamatic", "dynamatic_lat.tsv")


def main():
    root = sys.argv[1]
    write = "--write" in sys.argv
    meas = {}
    for k in sorted(os.listdir(root)):
        if not os.path.isdir(os.path.join(root, k)):
            continue
        r, why = R.read_kernel(root, k)
        if r:
            meas[k] = r
        else:
            print("# %s: kept as it was (%s)" % (k, why))
    # dynamatic_ref.tsv
    lines = open(REF).read().splitlines()
    out, seen = [], set()
    for l in lines:
        f = l.split("\t")
        if l.startswith("#") or len(f) < 4 or f[0] not in meas:
            out.append(l)
            continue
        r = meas[f[0]]
        seen.add(f[0])
        m = re.search(r"simulated ([0-9.]+) \+ ([0-9.]+) cycles x period ([0-9.]+)", f[3])
        if m:
            cyc = float(m.group(1)) + float(m.group(2))
            new = "%s\t%.2f\tmeasured, %d routes\t%s (cycles as before: %s + %s per unit; the period routed: %s)" % (
                f[0], cyc * r["mean"], len(r["periods"]), f[3], m.group(1), m.group(2), howof(r))
        elif r["cpi"] is not None:
            new = row(r)
        else:
            out.append(l)
            continue
        print("ref %s: %s %s -> %s" % (f[0], f[1], f[2], new.split("\t")[1] + " " + new.split("\t")[2]))
        out.append(new)
    for k, r in sorted(meas.items()):
        if k not in seen and r["cpi"] is not None:
            out.append(row(r))
            print("ref %s: (estimator's table) -> %.2f measured, %d routes" % (k, r["mean"] * r["cpi"], len(r["periods"])))
    # dynamatic_lat.tsv
    lat = open(LAT).read().splitlines()
    hdr = [l for l in lat if l.startswith("#")][-1].lstrip("# ").split("\t")
    ci = {h: i for i, h in enumerate(hdr)}
    lout = []
    for l in lat:
        f = l.split("\t")
        if l.startswith("#") or len(f) < len(hdr) or f[0] not in meas:
            lout.append(l)
            continue
        r = meas[f[0]]
        cyc = [int(x) for x in f[ci["cycles per call"]].split(",") if x]
        old = f[ci["mean ns per call"]]
        f[ci["mean ns per call"]] = "%.2f" % (statistics.mean(cyc) * r["mean"])
        f[ci["tag"]] = "cycles simulated, period measured (%d routes)" % len(r["periods"])
        pk = [h for h in hdr if h.startswith("period ns")][0]
        f[ci[pk]] = "%.3f" % r["mean"]
        f[-1] = f[-1] + "; period ROUTED: " + howof(r)
        print("lat %s: %s -> %s ns per call" % (f[0], old, f[ci["mean ns per call"]]))
        lout.append("\t".join(f))
    if write:
        open(REF, "w").write("\n".join(out) + "\n")
        open(LAT, "w").write("\n".join(lout) + "\n")
        print("written: %s, %s" % (REF, LAT))


def howof(r):
    return ("Dynamatic's own Verilog (dyn_export.py; checked on %d calls: results = the C, cycles = dynamatic_est.py's "
            "model) routed on seeds %s, %.2f ns mean (%.2f-%.2f), nextpnr %s" % (
                r["n"], ",".join(r["seeds"]), r["mean"], r["lo"], r["hi"], r["sha"]))


def row(r):
    return "%s\t%.2f\tmeasured, %d routes\tDynamatic on-merges buffers: %s x %.2f simulated cycles per iteration" % (
        r["k"], r["mean"] * r["cpi"], len(r["periods"]), howof(r), r["cpi"])


if __name__ == "__main__":
    main()
