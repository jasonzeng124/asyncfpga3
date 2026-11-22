#!/usr/bin/env python3
"""cmp_flows.py --a NAME RESULT... --b NAME RESULT... -- two flows' suite results, paired by (kernel, seed).

Each RESULT is a suite_one.sh result.txt (a farm task's, a resume's, a local completion's); per (kernel, seed) the
last file given with a judged status (PASS / FAIL) wins, so list a part's resumes after it; a status like PNR-TIMEOUT
counts only when nothing judged exists. Classes, per pair present in both flows:
  same route     the same sdf (so the same bits: the flows did not differ on this task)
  both clean     rule-CLEAN PASS in both on different routes: P_b / P_a (and the geometric mean over these)
  newly clean    B rule-CLEAN PASS, A not (NOT CLEAN, FAIL, no judged result)
  lost clean     A rule-CLEAN PASS, B not
  neither        neither rule-CLEAN PASS
and every FAIL (a wrong answer in a draw) is listed with its rule status. Prints a markdown summary."""
import math
import re
import sys


def parse(files):
    best = {}
    for f in files:
        try:
            lines = [l for l in open(f).read().splitlines() if l.strip()]
        except OSError:
            continue
        if not lines:
            continue
        line = lines[-1]
        m = re.match(r"(\S+) (\d+) status=(\S+)", line)
        if not m:
            continue
        k, s, st = m.group(1), int(m.group(2)), m.group(3)
        kv = dict(re.findall(r"(\w+)=(\S+)", line))
        kv["status"] = st
        kv["file"] = f
        judged = st in ("PASS", "FAIL")
        old = best.get((k, s))
        if old is None or judged or old["status"] not in ("PASS", "FAIL"):
            best[(k, s)] = kv
    return best


def clean(r):
    return r is not None and r["status"] == "PASS" and r.get("rule") == "clean"


def pn(r):
    try:
        return int(r.get("P", "NA"))
    except ValueError:
        return None


def main():
    args = sys.argv[1:]
    ia, ib = args.index("--a"), args.index("--b")
    if ia < ib:
        na, fa, nb, fb = args[ia + 1], args[ia + 2:ib], args[ib + 1], args[ib + 2:]
    else:
        nb, fb, na, fa = args[ib + 1], args[ib + 2:ia], args[ia + 1], args[ia + 2:]
    A, B = parse(fa), parse(fb)
    keys = sorted(set(A) | set(B))
    cls = {"same route": [], "both clean": [], "newly clean": [], "lost clean": [], "neither": [],
           "only in %s" % na: [], "only in %s" % nb: []}
    fails, ratios = [], []
    for key in keys:
        a, b = A.get(key), B.get(key)
        for nm, r in ((na, a), (nb, b)):
            if r is not None and r["status"] == "FAIL":
                fails.append("%s %s s%d (rule %s, draws %s, sdf %s)" % (nm, key[0], key[1], r.get("rule"), r.get("draws"),
                                                                       r.get("sdf")))
        if a is None or b is None:
            cls["only in %s" % (na if b is None else nb)].append("%s s%d" % key)
            continue
        if a.get("sdf") and a.get("sdf") == b.get("sdf") and a["status"] in ("PASS", "FAIL") and b["status"] in ("PASS", "FAIL"):
            cls["same route"].append("%s s%d" % key)
        elif clean(a) and clean(b):
            pa, pb = pn(a), pn(b)
            if pa and pb:
                ratios.append(pb / pa)
                cls["both clean"].append("%s s%d %.2f -> %.2f (%.2f)" % (key[0], key[1], pa / 1e3, pb / 1e3, pb / pa))
            else:
                cls["both clean"].append("%s s%d (P %s -> %s)" % (key[0], key[1], a.get("P"), b.get("P")))
        elif clean(b):
            cls["newly clean"].append("%s s%d (%s: %s / %s)" % (key[0], key[1], na, a["status"], a.get("rule", "-")))
        elif clean(a):
            cls["lost clean"].append("%s s%d (%s: %s / %s)" % (key[0], key[1], nb, b["status"], b.get("rule", "-")))
        else:
            cls["neither"].append("%s s%d (%s %s/%s, %s %s/%s)" % (key[0], key[1], na, a["status"], a.get("rule", "-"),
                                                                   nb, b["status"], b.get("rule", "-")))
    print("## %s vs %s, paired by (kernel, seed): %d pairs in %s, %d in %s" % (nb, na, len(B), nb, len(A), na))
    for c, v in cls.items():
        print("- **%s**: %d%s" % (c, len(v), (" -- " + ", ".join(v)) if v and c != "same route" else ""))
    if ratios:
        g = math.exp(sum(math.log(r) for r in ratios) / len(ratios))
        print("- P ratio %s / %s over the %d both-clean pairs on different routes: geometric mean %.3f (%.2f-%.2f)"
              % (nb, na, len(ratios), g, min(ratios), max(ratios)))
    print("- FAIL (a wrong answer in a draw): %s" % ("; ".join(fails) if fails else "none"))


if __name__ == "__main__":
    main()
