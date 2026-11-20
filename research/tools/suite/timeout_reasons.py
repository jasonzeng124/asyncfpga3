#!/usr/bin/env python3
"""timeout_reasons.py LABEL RESULTS_DIR PART... -- reasons TSV (suite_table.py --reasons) for the kernels with no
result line in any task of the given farm suite parts.

For each such kernel: how many of its tasks ended at the time limit (TIMEOUT), failed (FAILED / NODE_FAIL / ...),
are still running or waiting, and how far each timed-out loop got (its auto/log.txt as returned: "loop shipped it I"
when a final stack was written, else "loop at it I"). Kernels with at least one result line are not printed (the table
has their row). Output: kernel<TAB>reason, one line each, to stdout."""
import os
import re
import sys


def task_kernel(d):
    t = os.path.join(d, "task.txt")
    if not os.path.exists(t):
        return None, None
    m = re.search(r"kernel (\S+) seed (\d+)", open(t).read())
    return (m.group(1), int(m.group(2))) if m else (None, None)


def how_far(d):
    lg = os.path.join(d, "auto", "log.txt")
    if not os.path.exists(lg):
        return "no loop state returned"
    txt = open(lg).read()
    fin = re.findall(r"^final it (\d+) ", txt, re.M)
    its = re.findall(r"^(?:search )?it (\d+) \S+ [0-9a-f]{8} ", txt, re.M)
    if fin:
        return "loop shipped it %s" % fin[-1]
    if its:
        return "loop at it %s" % its[-1]
    return "loop at it 0"


def main():
    label, res = sys.argv[1], sys.argv[2]
    per = {}
    for part in sys.argv[3:]:
        st = os.path.join(res, part, "status.txt")
        if not os.path.exists(st):
            continue
        states = {}
        for ln in open(st):
            m = re.match(r"^(\d+)\s+(\S+)", ln)
            if m:
                states[int(m.group(1))] = m.group(2)
        for t, s in states.items():
            d = os.path.join(res, part, str(t))
            k, seed = task_kernel(d)
            if k is None:
                continue
            rf = os.path.join(d, "result.txt")
            ok = os.path.exists(rf) and "status=" in open(rf).read()
            per.setdefault(k, []).append((seed, s, ok, how_far(d) if s == "TIMEOUT" else ""))
    for k in sorted(per):
        rows = per[k]
        if any(ok for _, _, ok, _ in rows):
            continue
        to = sorted((sd, hf) for sd, s, ok, hf in rows if s == "TIMEOUT")
        fa = sorted(sd for sd, s, ok, _ in rows if s in ("FAILED", "NODE_FAIL", "OUT_OF_MEMORY", "CANCELLED"))
        ru = sorted(sd for sd, s, ok, _ in rows if s in ("RUNNING", "PENDING"))
        parts = []
        if to:
            parts.append("%d task(s) stopped at the farm's 240-min limit (%s)" % (
                len(to), "; ".join("s%d: %s" % (sd, hf) for sd, hf in to)))
        if fa:
            parts.append("%d failed on the machine (s%s)" % (len(fa), ", s".join(map(str, fa))))
        if ru:
            parts.append("%d still running (s%s)" % (len(ru), ", s".join(map(str, ru))))
        print("%s\t%s: no result line yet -- %s" % (k, label, "; ".join(parts) or "no task returned"))


if __name__ == "__main__":
    main()
