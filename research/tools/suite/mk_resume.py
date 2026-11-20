#!/usr/bin/env python3
"""mk_resume.py RESULTS_DIR NEW_SUFFIX PART... -- resume requests for the tasks of farm suite parts that did not finish.

For each PART (a request name under research/cluster/requests/, whose body keeps its loop state in $SHARED: the
"$SHARED state" block of suite13t_s5a_v10_* / suite13t_s3a_rwa), read RESULTS_DIR/PART/status.txt (a claude/cluster
checkout's results/) and list the tasks that ended without a result line: TIMEOUT, FAILED, NODE_FAIL, OUT_OF_MEMORY,
CANCELLED, or COMPLETED with no result.txt. Write research/cluster/requests/PART_NEW_SUFFIX.sh: the same body (so the
same kernel and seed per task number, and the same $SHARED state directory), with
  * `#CLUSTER array=` the unfinished tasks only,
  * cores=4 and DRAW_JOBS=4 (the four draws at once; CA_JOBS unchanged: the rule's results do not depend on it),
  * a header line naming what it resumes.
A part with nothing unfinished gets no file. Prints one line per part. The flow is unchanged: a resumed task goes on
from its state (AUTO_RESUME), or rebuilds and trims its shipped route (AUTO_TRIM_ONLY) and draws it; with no state
(a task that died before its first save) it starts from the top."""
import os
import re
import sys

BAD = ("TIMEOUT", "FAILED", "NODE_FAIL", "OUT_OF_MEMORY", "CANCELLED")


def unfinished(res, part):
    st = os.path.join(res, part, "status.txt")
    if not os.path.exists(st):
        return None, "no status.txt"
    txt = open(st).read()
    if not re.search(r"^state\s+done", txt, re.M):
        return None, "not done (%s)" % re.search(r"^state\s+(.*)$", txt, re.M).group(1)[:60]
    out = []
    for ln in txt.splitlines():
        m = re.match(r"^(\d+)\s+(\S+)", ln)
        if not m:
            continue
        t, state = int(m.group(1)), m.group(2)
        rf = os.path.join(res, part, str(t), "result.txt")
        has = os.path.exists(rf) and "status=" in open(rf).read()
        if state in BAD or not has:
            out.append(t)
    return out, ""


def main():
    res, suf = sys.argv[1], sys.argv[2]
    here = os.path.dirname(os.path.abspath(__file__))
    reqdir = os.path.normpath(os.path.join(here, "../../cluster/requests"))
    for part in sys.argv[3:]:
        tasks, why = unfinished(res, part)
        if tasks is None:
            print("%s: skipped (%s)" % (part, why))
            continue
        if not tasks:
            print("%s: every task has a result line" % part)
            continue
        src = open(os.path.join(reqdir, part + ".sh")).read()
        if "$SHARED/state_" not in src:
            print("%s: skipped (its body keeps no state in $SHARED: a resume would start from the top)" % part)
            continue
        name = "%s_%s" % (part, suf)
        arr = ",".join(str(t) for t in tasks)
        body = re.sub(r"^#CLUSTER .*$", "#CLUSTER array=%s cores=4 mem=16G time=240" % arr, src, count=1, flags=re.M)
        body = body.replace("DRAW_JOBS=2", "DRAW_JOBS=4")
        hdr = ("# %s: resumes %s's %d task(s) that ended without a result line (%s), from their $SHARED state; the same\n"
               "# body otherwise (same kernel / seed per task number), 4 cores with the four draws at once.\n"
               % (name, part, len(tasks), arr))
        lines = body.split("\n")
        ci = next(i for i, l in enumerate(lines) if l.startswith("#CLUSTER"))
        lines.insert(ci + 1, hdr.rstrip("\n"))
        out = os.path.join(reqdir, name + ".sh")
        if len(name) > 40 or not re.fullmatch(r"[a-z0-9_-]+", name):
            print("%s: name %s not allowed by the farm" % (part, name))
            continue
        open(out + ".tmp", "w").write("\n".join(lines))
        os.replace(out + ".tmp", out)
        print("%s: %d unfinished -> %s" % (part, len(tasks), os.path.relpath(out)))


if __name__ == "__main__":
    main()
