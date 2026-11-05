#!/usr/bin/env python3
"""shrink_sizes.py IN.vh FACTOR OUT.vh -- one PROGRAM item-3 shrink step: every matched-delay size n in IN.vh becomes
ceil(FACTOR * n) (never below 1).

    python3 research/tools/shrink_sizes.py research/data/gcd_hw_sizes_R5.vh 0.9 research/data/gcd_hw_sizes_R5s90.vh

ceil keeps a step small: at 0.9 only sizes >= 10 links move (the compute and select delays that set the per-iteration
cost); the 1-2 link link/uack sizes stay.  Whether the step holds is the full stack's call (both corners and the
combined worst case, >= 8 routes); this script only writes the candidate.
"""
import math, re, sys


def main():
    src, f, out = sys.argv[1], float(sys.argv[2]), sys.argv[3]
    lines, moved = [], 0
    for ln in open(src):
        m = re.match(r"(`define\s+\S+\s+)(\d+)(.*)$", ln.rstrip("\n"))
        if m:
            n = int(m.group(2)); k = max(1, math.ceil(f * n - 1e-9))
            moved += k != n
            ln = "%s%d%s\n" % (m.group(1), k, m.group(3))
        lines.append(ln)
    with open(out, "w") as o:
        o.write("// %s x %s (ceil), research/tools/shrink_sizes.py: %d sizes moved\n" % (src.split("/")[-1], f, moved))
        o.writelines(lines)
    print("%s: %d sizes moved -> %s" % (src, moved, out))


if __name__ == "__main__":
    main()
