#!/usr/bin/env python3
"""vecsub.py IN.hex OUT.hex J [J ...]: the calls J (0-based) of a v2 vector file, in that order, header kept
(a shorter prefix/subset for the decoded-netlist gate, as smoke.sh's gatevec files)."""
import sys
L = open(sys.argv[1]).read().splitlines()
head, calls, cur = [], [], None
for l in L:
    if l.startswith("// call"):
        cur = [l]; calls.append(cur)
    elif cur is None:
        head.append(l)
    else:
        cur.append(l)
sel = [int(j) for j in sys.argv[3:]]
head[1] += " | subset of calls %s of %s" % (",".join(map(str, sel)), sys.argv[1].split("/")[-1])
open(sys.argv[2], "w").write("\n".join(head + [x for j in sel for x in calls[j]]) + "\n")
print("%s: calls %s" % (sys.argv[2], sel))
