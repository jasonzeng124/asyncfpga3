#!/usr/bin/env python3
"""merge_rules.py OUT RULEDIR... -- the sizing rule at several corners, merged: OUT/sizes.vh holds per line the LARGEST
size any corner proposes, OUT/negative_sized.tsv every corner's negative rows (each tagged with its corner dir).
auto_size.sh runs corner_audit CA_SIZERULE=1 at the delay model's worst vertices (bench_gate.sh draw:K draws delay
chains and the rest independently from [0.20, 0.31], CARRY4 / F7F8 / FF from [0.20, 1.0]) and sizes for all of them."""
import os, re, sys
out, dirs = sys.argv[1], sys.argv[2:]
os.makedirs(out, exist_ok=True)
best, order, hdr = {}, [], []
for d in dirs:
    for ln in open(os.path.join(d, "sizes.vh")):
        m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
        if not m:
            if ln.startswith("//"):
                hdr.append(ln.rstrip("\n") + "  [%s]" % os.path.basename(d))
            continue
        k, v = m.group(1), int(m.group(2))
        if k not in best:
            order.append(k); best[k] = (v, d)
        elif v > best[k][0]:
            best[k] = (v, d)
with open(os.path.join(out, "sizes.vh"), "w") as f:
    f.write("// merge_rules.py: per line the largest proposal of %s\n" % ", ".join(os.path.basename(d) for d in dirs))
    for h in hdr:
        f.write(h + "\n")
    for k in order:
        f.write("`define %s %d   // %s\n" % (k, best[k][0], os.path.basename(best[k][1])))
with open(os.path.join(out, "negative_sized.tsv"), "w") as f:
    f.write("rule\tmargin\tkey\tfix\tcorner\n")
    for d in dirs:
        p = os.path.join(d, "negative_sized.tsv")
        for ln in open(p):
            if ln.startswith("rule\t") or not ln.strip():
                continue
            f.write(ln.rstrip("\n") + "\t" + os.path.basename(d) + "\n")
