#!/usr/bin/env python3
"""cmp_ca.py A B -- two corner_audit --out dirs: byte-identity per output file (the out dir's own path replaced by OUT), then (if different) what differs:
rows by key (rule, margin) in report.txt's constraint list, lines.tsv as a set of rows, sizes.vh values."""
import os, re, sys, filecmp
a, b = sys.argv[1], sys.argv[2]
files = ["report.txt", "lines.tsv", "sizes.vh", "verify.txt", "negative_sized.tsv", "tighten.log", "skew.log", "arb_fork.log"]
same = True
for f in files:
    pa, pb = os.path.join(a, f), os.path.join(b, f)
    if not (os.path.exists(pa) and os.path.exists(pb)):
        print("  %-20s missing (%s %s)" % (f, os.path.exists(pa), os.path.exists(pb))); same = False; continue
    # every file may name the out dir (report.txt's header, the logs' "rule E <dir>/soak.sdf"): compared with it
    # replaced by OUT; nothing else is normalised
    la = [l.replace(os.path.abspath(a), "OUT") for l in open(pa)]; lb = [l.replace(os.path.abspath(b), "OUT") for l in open(pb)]
    eq = la == lb
    print("  %-20s %s" % (f, "IDENTICAL" if eq else "DIFFERENT")); same &= eq
print("RESULT", "IDENTICAL" if same else "DIFFERENT")
if not same and "-v" in sys.argv:
    def sizes(p):
        return {m.group(1): int(m.group(2)) for l in open(p) for m in [re.match(r"`define\s+(\S+)\s+(\d+)", l)] if m}
    sa, sb = sizes(os.path.join(a, "sizes.vh")), sizes(os.path.join(b, "sizes.vh"))
    for k in sorted(set(sa) | set(sb)):
        if sa.get(k) != sb.get(k):
            print("  sizes %-55s %s -> %s" % (k, sa.get(k), sb.get(k)))
    la = set(open(os.path.join(a, "lines.tsv"))); lb = set(open(os.path.join(b, "lines.tsv")))
    print("  lines.tsv rows only in A: %d, only in B: %d" % (len(la - lb), len(lb - la)))
    for l in sorted(la - lb): print("   A " + l.rstrip()[:220])
    for l in sorted(lb - la): print("   B " + l.rstrip()[:220])
