#!/usr/bin/env python3
"""trim_table.py OUTROOT... : one row per trim_farm.sh run (OUTROOT/REQ_TASK/): the farm's untrimmed route against the
same route trimmed by the flow's trim step, judged on the same draw points.

Columns: kernel, seed, shipped it, sdf (the same route on both sides: trim_farm.sh refuses a different one), the rule
before -> after (short constraints and total miss, from the trim step's own rule runs: step 1 is the untrimmed route),
the lines moved (MACRO old -> new), P untrimmed (the farm's) and trimmed, dP, the draws (farm; trimmed) and the trimmed
route's bits verdict.  Last lines: the paired dP over the routes with both P, and the draws in total.
"""
import glob, os, re, statistics, sys


def fields(line):
    return dict(re.findall(r"(\w+)=(\S+)", line or ""))


def first(path):
    try:
        with open(path) as f:
            return f.readline().strip()
    except OSError:
        return ""


rows = []
for root in sys.argv[1:]:
    for d in sorted(glob.glob(os.path.join(root, "*_*"))):
        if not os.path.isdir(d):
            continue
        task = first(os.path.join(d, "farm", "task.txt")).split()
        if len(task) < 5:
            continue
        k, s = task[2], task[4]
        farm = fields(first(os.path.join(d, "farm", "result.txt")))
        tr = fields(first(os.path.join(d, "result.txt")))
        log = os.path.join(d, "auto", "log.txt")
        loglines = open(log).read().splitlines() if os.path.exists(log) else []
        steps = [l for l in loglines if l.startswith("trim")]
        moved = []
        it = farm.get("it", "?")
        sz = {}
        try:   # the loop's own sizes of the shipped iteration (as built), against the trim record (MACRO=LEN)
            for l in open(os.path.join(d, "farm", "auto", "sizes_%s.vh" % it)):
                m = re.match(r"`define\s+(\S+)\s+(\d+)", l)
                if m:
                    sz[m.group(1)] = m.group(2)
        except OSError:
            pass
        rec = os.path.join(d, "auto", "trim_%s.txt" % it)
        if os.path.exists(rec):
            for l in open(rec):
                if "=" in l:
                    k_, v_ = l.strip().split("=")
                    moved.append("%s %s->%s" % (k_.replace("BD_SZ_BRIDGE_I_UDUT_", "").lower(), sz.get(k_, "?"), v_))
        rule = ""
        m0 = re.search(r"before: (\d+) short, (-?\d+) ps", " ".join(steps))
        mlast = [re.search(r"\((\d+) short, (-?\d+) ps\)", l) for l in steps]
        mlast = [x for x in mlast if x]
        if m0:
            rule = "%s/%sps" % (m0.group(1), m0.group(2))
            if mlast:
                rule += " -> %s/%sps" % (mlast[-1].group(1), mlast[-1].group(2))
        if any("DIFFERENT ROUTE" in l for l in loglines):
            rule = "DIFFERENT ROUTE"
        pf, pt = farm.get("P"), tr.get("P")
        dp = ""
        if pf and pt and pf.isdigit() and pt.isdigit():
            dp = int(pt) - int(pf)
        rows.append(dict(k=k, s=s, it=farm.get("it", "?"), sdf=farm.get("sdf", "?"), rule=rule or "-",
                         moved=", ".join(moved) or "-", pf=pf or "-", pt=pt or "-", dp=dp,
                         df=farm.get("draws", "-"), dt=tr.get("draws", "-"), st=tr.get("status", "-"),
                         bits=tr.get("bits", "-"), latf=farm.get("lat_call_med_ns", "-"), latt=tr.get("lat_call_med_ns", "-")))

print("| kernel | seed | it | sdf | rule before -> after trim (short / miss) | lines moved | P farm | P trimmed | dP ps | "
      "lat/call farm -> trimmed ns | draws farm; trimmed | trimmed status | bits |")
print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
for r in rows:
    print("| %(k)s | %(s)s | %(it)s | %(sdf)s | %(rule)s | %(moved)s | %(pf)s | %(pt)s | %(dp)s | %(latf)s -> %(latt)s | "
          "%(df)s; %(dt)s | %(st)s | %(bits)s |" % r)
dps = [r["dp"] for r in rows if isinstance(r["dp"], int)]
if dps:
    rel = [r["dp"] / int(r["pf"]) for r in rows if isinstance(r["dp"], int)]
    print("\npaired dP over %d routes: median %d ps (%.1f %%), range %d .. %d; faster on %d, equal on %d, slower on %d"
          % (len(dps), statistics.median(dps), 100 * statistics.median(rel), min(dps), max(dps),
             sum(1 for x in dps if x < 0), sum(1 for x in dps if x == 0), sum(1 for x in dps if x > 0)))
dt = [r["dt"] for r in rows if "/" in r["dt"]]
if dt:
    print("draws on the trimmed routes: %d / %d" % (sum(int(x.split("/")[0]) for x in dt), sum(int(x.split("/")[1]) for x in dt)))
