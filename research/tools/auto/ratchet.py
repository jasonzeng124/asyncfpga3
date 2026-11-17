#!/usr/bin/env python3
"""ratchet.py CUR.vh PROP.vh NEG.tsv OUT.vh -- one step of the automatic sizing loop (auto_size.sh).
OUT = per macro max(CUR, PROP): a line the rule asks to lengthen on this route is lengthened; a line it would shorten
keeps its size (sizes only go up after the first proposal, so the loop terminates; tighten_loop.sh's header shows the
period-2 oscillation a loop without this falls into).  Prints "raised N unfixable M": N lines raised, M sized
constraints still negative on this route that no line could be raised for (NEG.tsv rows marked unfixable)."""
import re, sys

def rd(p):
    out, order = {}, []
    for ln in open(p):
        m = re.match(r"`define\s+(\S+)\s+(\d+)", ln)
        if m:
            out[m.group(1)] = int(m.group(2)); order.append(m.group(1))
    return out, order

cur, order = rd(sys.argv[1])
prop, _ = rd(sys.argv[2])
neg = [l.rstrip("\n").split("\t") for l in open(sys.argv[3]) if l.strip() and not l.startswith("rule\t")]
raised = []
with open(sys.argv[4], "w") as f:
    f.write("// ratchet.py: max(%s, %s)\n" % (sys.argv[1], sys.argv[2]))
    for mac in order:
        v = max(cur[mac], prop.get(mac, cur[mac]))
        if v > cur[mac]:
            raised.append("%s %d->%d" % (mac, cur[mac], v))
        f.write("`define %s %d%s\n" % (mac, v, "" if v == cur[mac] else "   // was %d" % cur[mac]))
unf = [r for r in neg if len(r) > 3 and r[3] == "unfixable"]
print("raised %d unfixable %d negative %d" % (len(raised), len(unf), len(neg)))
for r in raised:
    print("  raised " + r)
for r in unf:
    print("  unfixable " + " ".join(r[:3]))
