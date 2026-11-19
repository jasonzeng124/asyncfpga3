#!/usr/bin/env python3
"""vcd_pulses.py VCD RUNT_NETS_TSV MON_LOG [T3] -- the runt monitor checked against an independent reading of the same run.

Reads the watched nets (runt_nets.tsv: index, wire) from a VCD of the run (cost.sh's w.vcd or all.vcd), finds every
pulse narrower than T3 (default 1000 ps) by the monitor's definition -- a level bounded by the same 0/1 level on both
sides, width = time between its edges, an edge undone in the same time step erased -- and compares the list with the
monitor's RUNT lines in MON_LOG (cost.sh runs it with +RUNT_MAXLINES=1000000, so every pulse is printed).
Prints the counts per net from both and every difference; exit 0 only when the two lists are identical.
"""
import sys, re, collections
vcd, tsv, mlog = sys.argv[1:4]
T3 = int(sys.argv[4]) if len(sys.argv) > 4 else 1000
wk = {}
for l in open(tsv):
    if l.startswith("#"): continue
    f = l.rstrip("\n").split("\t"); wk[f[6]] = int(f[0])
idk = collections.defaultdict(list)
t = 0
hist = collections.defaultdict(list)    # k -> [(t, v)]
scope = []
with open(vcd) as fh:
    for ln in fh:
        if ln.startswith("$scope"):
            scope.append(ln.split()[2]); continue
        if ln.startswith("$upscope"):
            scope.pop(); continue
        if ln.startswith("$var"):
            p = ln.split()
            if p[4] in wk and scope and scope[-1] == "dut": idk[p[3]].append(wk[p[4]])
            continue
        if not ln or ln[0] in "$ \n": continue
        if ln[0] == "#": t = int(ln[1:]); continue
        if ln[0] in "01xzXZ":
            i = ln[1:].strip()
            if i in idk:
                v = ln[0].lower(); v = v if v in "01" else "x"
                for k in idk[i]: hist[k].append((t, v))
mine = []
for k, h in hist.items():
    # collapse same-time changes to the last value of that time step (the monitor erases zero-width excursions)
    seq = []
    for tt, v in h:
        if seq and seq[-1][0] == tt: seq[-1] = (tt, v)
        else: seq.append((tt, v))
    # drop repeats of the same value (a step whose excursion was erased)
    s2 = []
    for tt, v in seq:
        if not s2 or s2[-1][1] != v: s2.append((tt, v))
    for a in range(1, len(s2) - 1):
        (t0, v0), (t1, v1), (t2, v2) = s2[a - 1], s2[a], s2[a + 1]
        if v0 in "01" and v2 == v0 and v1 != v0 and t2 - t1 < T3 and t2 - t1 > 0:
            mine.append((k, t1, t2 - t1, v1))
theirs = []
for l in open(mlog):
    if l.startswith("RUNT t="):
        d = dict(re.findall(r"(\w+)=(\S+)", l)); theirs.append((int(d["k"]), int(d["t"]), int(d["w"]), d["lvl"]))
a, b = collections.Counter(mine), collections.Counter(theirs)
print("vcd: %d pulses < %d ps on %d nets; monitor: %d RUNT lines on %d nets" % (
    len(mine), T3, len({x[0] for x in mine}), len(theirs), len({x[0] for x in theirs})))
only_v, only_m = a - b, b - a
for x in sorted(only_v)[:20]: print("only in vcd    ", x)
for x in sorted(only_m)[:20]: print("only in monitor", x)
print("IDENTICAL" if not only_v and not only_m else "DIFFERENT (%d only in vcd, %d only in monitor)" % (
    sum(only_v.values()), sum(only_m.values())))
sys.exit(0 if not only_v and not only_m else 1)
