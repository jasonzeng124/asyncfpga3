#!/usr/bin/env python3
"""pair_cmp.py [--a-field F] [--b-field F] [--clean] [--group NAME=k1,k2,...] A_DIR... -- B_DIR... -- two farm runs of
the suite compared route by route: the same (kernel, seed) in both, A's P (or --a-field, e.g. P_untrimmed) against
B's.  Each DIR is a farm results/NAME (TASK/result.txt) or a file of result lines; a later DIR overrides an earlier one
for the same (kernel, seed).  Only routes judged in both (status PASS or FAIL, a numeric field) are paired; --clean
keeps only pairs rule-clean on both sides.  Prints per kernel the pairs (B/A - 1 in %), the median per kernel, and
per group (--group, repeatable; "rest" = the others) the median and the geometric mean of B/A over all pairs, with how
many pairs are faster / slower.  The two runs are different routes (a netlist change moves the placement), so a pair
carries route-to-route scatter (~5 % on P): read medians over many pairs, not single rows."""
import glob
import math
import os
import re
import statistics as st
import sys


def read(dirs):
    out = {}
    for d in dirs:
        fs = sorted(glob.glob(os.path.join(d, "*", "result.txt"))) if os.path.isdir(d) else [d]
        for f in fs:
            for l in open(f):
                w = l.split()
                if len(w) < 3:
                    continue
                kv = dict(re.findall(r"(\w+)=(\S+)", l))
                out[(w[0], w[1])] = kv
    return out


def main():
    args = sys.argv[1:]
    af = bf = "P"
    clean = False
    groups = []
    while args and args[0].startswith("--"):
        o = args.pop(0)
        if o == "--a-field":
            af = args.pop(0)
        elif o == "--b-field":
            bf = args.pop(0)
        elif o == "--clean":
            clean = True
        elif o == "--group":
            n, ks = args.pop(0).split("=", 1)
            groups.append((n, set(ks.split(","))))
    i = args.index("--")
    A, B = read(args[:i]), read(args[i + 1:])
    pairs = {}
    for key in sorted(set(A) & set(B)):
        a, b = A[key], B[key]
        if a.get("status") not in ("PASS", "FAIL") or b.get("status") not in ("PASS", "FAIL"):
            continue
        if clean and not (a.get("rule") == "clean" and b.get("rule") == "clean"):
            continue
        pa, pb = a.get(af, "NA"), b.get(bf, "NA")
        if not (pa.isdigit() and pb.isdigit()) or not int(pa):
            continue
        pairs.setdefault(key[0], []).append((key[1], int(pa), int(pb), a.get("rule"), b.get("rule")))
    print("A field %s, B field %s%s" % (af, bf, ", rule-clean on both sides only" if clean else ""))
    for k in sorted(pairs):
        ps = pairs[k]
        r = [pb / pa for _, pa, pb, _, _ in ps]
        print("%-20s %s  median %+.1f %%" % (k, "  ".join("s%s %d->%d (%+.1f%%)%s" % (
            s, pa, pb, 100 * (pb / pa - 1), "" if (ra == "clean" and rb == "clean") else "*")
            for s, pa, pb, ra, rb in ps), 100 * (st.median(r) - 1)))
    def summ(name, ks):
        r = [pb / pa for k in ks if k in pairs for _, pa, pb, _, _ in pairs[k]]
        if not r:
            return
        gm = math.exp(sum(map(math.log, r)) / len(r))
        print("%-12s pairs %3d (kernels %d): median %+.1f %%, geometric mean %+.1f %%, faster %d, slower %d"
              % (name, len(r), sum(1 for k in ks if k in pairs), 100 * (st.median(r) - 1), 100 * (gm - 1),
                 sum(1 for x in r if x < 1), sum(1 for x in r if x > 1)))
    used = set()
    for n, ks in groups:
        summ(n, ks)
        used |= ks
    if groups:
        summ("rest", set(pairs) - used)
    summ("all", set(pairs))
    print("(* = a NOT CLEAN route on at least one side)")


if __name__ == "__main__":
    main()
