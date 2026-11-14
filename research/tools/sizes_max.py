#!/usr/bin/env python3
"""sizes_max.py BASE.vh OUT.vh PROPOSAL.vh [PROPOSAL.vh ...] -- per-cell maximum of several routes' corner_audit.py
proposals (each a sizes.vh of the same kernel), so the candidate holds every constraint on every route it was measured
on.  A cell absent from a proposal keeps BASE's size for that route.  Prints, per changed cell, base -> candidate and
the per-route proposals.  The candidate is only a candidate: the full stack (>= 8 routes, both corners and the combined
worst case) decides.
"""
import re, sys

RX = re.compile(r"^`define\s+(\S+)\s+(\d+)")


def read(p):
    d = {}
    for ln in open(p):
        m = RX.match(ln)
        if m:
            d[m.group(1)] = int(m.group(2))
    return d


def main():
    base, out, props = sys.argv[1], sys.argv[2], sys.argv[3:]
    b = read(base)
    ps = [read(p) for p in props]
    cand = {k: max(p.get(k, v) for p in ps) for k, v in b.items()}
    extra = sorted(set().union(*ps) - set(b))
    if extra:
        sys.exit("sizes_max: proposals name cells not in %s: %s" % (base, extra[:5]))
    with open(out, "w") as f:
        f.write("// per-cell max of %d corner_audit.py proposals over %s: %s\n" % (len(ps), base.split("/")[-1],
                " ".join(props)))
        for k in sorted(b):
            f.write("`define %s %d%s\n" % (k, cand[k], "   // was %d" % b[k] if cand[k] != b[k] else ""))
    ch = [k for k in sorted(b) if cand[k] != b[k]]
    for k in ch:
        print("  %-42s %3d -> %3d   (%s)" % (k, b[k], cand[k], " ".join(str(p.get(k, b[k])) for p in ps)))
    print("%s: %d of %d cells changed, links %d -> %d" % (out, len(ch), len(b), sum(b.values()), sum(cand.values())))


if __name__ == "__main__":
    main()
