#!/usr/bin/env python3
"""max_sizes.py BASE.vh OUT.vh PROPOSAL.vh [PROPOSAL.vh ...] -- per-cell max of corner_audit proposals over routes.

Each PROPOSAL is a corner_audit out/sizes.vh (the route's sizes with its changed lines).  OUT gets, for every macro
in BASE, max over the proposals (a line no proposal mentions keeps BASE); macros only in proposals are added.  Every
line that moved is commented with base and the per-route values, so the file says where each number came from.
"""
import re, sys


def read(p):
    d = {}
    for ln in open(p):
        m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
        if m:
            d[m.group(1)] = int(m.group(2))
    return d


base_p, out_p, props = sys.argv[1], sys.argv[2], sys.argv[3:]
base = read(base_p)
P = [read(p) for p in props]
keys = list(base) + sorted({k for p in P for k in p} - set(base))
lines = ["// per-cell max over %d corner_audit proposals (research/tools/fifteen/max_sizes.py), base %s" % (len(P), base_p)]
lines += ["//   %s" % p for p in props]
moved = 0
for k in keys:
    vals = [p.get(k, base.get(k)) for p in P]
    vals = [v for v in vals if v is not None]
    v = max(vals) if vals else base[k]
    note = ""
    if v != base.get(k):
        moved += 1
        note = "   // base %s, per route %s" % (base.get(k, "-"), "/".join(map(str, vals)))
    lines.append("`define %s %d%s" % (k, v, note))
open(out_p, "w").write("\n".join(lines) + "\n")
print("%d of %d lines moved -> %s" % (moved, len(keys), out_p))
