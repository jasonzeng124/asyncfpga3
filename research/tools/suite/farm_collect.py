#!/usr/bin/env python3
"""farm_collect.py RESULTS_DIR OUTDIR -- read a suite farm request (suite1/suite2/suite3 layout), copy each task's
sizes_final.vh to OUTDIR/<kernel>_<seed>_sizes_final.vh, and print one line per task:
  kernel seed verdict-of-the-suite (or of the loop when the suite's result.txt was overwritten) P bits
and a list of rejudge candidates (routes the farm called NOT EQUIVALENT or never drew) as 'kernel seed sizes_path'."""
import glob, os, re, shutil, sys
res, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
rows, cand = [], []
for t in sorted(glob.glob(os.path.join(res, "*", "task.txt")), key=lambda p: int(p.split(os.sep)[-2])):
    d = os.path.dirname(t); head = open(t).read().split("\n")[0]
    m = re.search(r"kernel (\S+) seed (\d+)", head)
    if not m:
        continue
    k, s = m.group(1), m.group(2)
    txt = open(t).read()
    suite = re.search(r"^%s %s status=.*$" % (re.escape(k), s), txt, re.M)
    line = suite.group(0) if suite else ""
    for f in ("result.txt",):
        p = os.path.join(d, f)
        if not line and os.path.exists(p):
            line = open(p).read().strip().split("\n")[-1]
    sz = None
    for p in (os.path.join(d, "auto", "sizes_final.vh"), os.path.join(d, "sizes_final.vh")):
        if os.path.exists(p):
            sz = os.path.join(out, "%s_%s_sizes_final.vh" % (k, s)); shutil.copy(p, sz); break
    st = re.search(r"status=(\S+)", line)
    st = st.group(1) if st else ("NOT-EQUIVALENT" if "NOT EQUIVALENT" in line else ("LOOP-ONLY" if line else "NO-RESULT"))
    P = re.search(r"P=(\S+)", line); P = P.group(1) if P else "NA"
    rows.append((k, s, st, P, line[:160]))
    if sz and (st in ("NOT-A-BOARD-ROUTE", "NOT-EQUIVALENT", "LOOP-ONLY") or "NOT EQUIVALENT" in line):
        cand.append("%s %s %s" % (k, s, sz))
for r in rows:
    print("%-10s %2s %-22s P=%-6s" % r[:4])
print("# rejudge candidates (%d):" % len(cand))
for c in cand:
    print("REJUDGE " + c)
