#!/usr/bin/env python3
"""ring_walk_own.py (audit T16): own walk of every ring of the owner's ro_many_top build through the prjxray SDF.
    python3 -I ring_walk_own.py XRAY.sdf PRED.tsv
Ring grp[g].ro[b] = inv -> d.chain.g[0].u -> ... -> g[L-1].u -> inv. For each hop drv -> snk: the INTERCONNECT
drv/O6 -> snk/<pin> plus snk's IOPATH <pin> -> O6, taking the FAST_MIN (first) and SLOW_MAX (third) numbers of each
(min:typ:max) triple (rise and fall equal in this SDF; checked). Period = 2 x loop sum. Compared with research's
pred.tsv (cells/gls/fid/ring_predict.py) ring by ring."""
import re, sys, csv, collections
sdf = open(sys.argv[1]).read()
unesc = lambda s: s.replace("\\", "")
IC = collections.defaultdict(dict)      # snk_cell -> {(drv_cell, pin): (fast, slowmax)}
for m in re.finditer(r"\(INTERCONNECT (\S+)/(\S+) (\S+)/(\S+) \((\d+):(\d+):(\d+)\) \((\d+):(\d+):(\d+)\)\)", sdf):
    d, dp, s, sp = unesc(m.group(1)), m.group(2), unesc(m.group(3)), m.group(4)
    r, f = (int(m.group(5)), int(m.group(7))), (int(m.group(8)), int(m.group(10)))
    assert r == f
    IC[s][(d, sp)] = r
IOP = collections.defaultdict(dict)     # cell -> {in_pin: (fast, slowmax)} for -> O6
for blk in re.finditer(r"\(INSTANCE (\S+)\)(.*?)(?=\(CELL|\Z)", sdf, re.S):
    inst = unesc(blk.group(1))
    if not inst: continue
    for m in re.finditer(r"\(IOPATH (\S+) O6 \((\d+):(\d+):(\d+)\) \((\d+):(\d+):(\d+)\)\)", blk.group(2)):
        r, f = (int(m.group(2)), int(m.group(4))), (int(m.group(5)), int(m.group(7)))
        IOP[inst][m.group(1)] = (max(r[0], f[0]), max(r[1], f[1])) if r != f else r
def hop(d, s):
    cands = [(pin, v) for (dd, pin), v in IC[s].items() if dd == d]
    assert len(cands) == 1, (d, s, cands)
    pin, ic = cands[0]
    io = IOP[s][pin]
    return ic[0] + io[0], ic[1] + io[1]
P = {r["ring"]: r for r in csv.DictReader(open(sys.argv[2]), delimiter="\t")}
worst = 0; n = 0
for ring, r in P.items():
    g, b = ring[1:].split(".b"); L = int(r["links"])
    base = "grp[%s].ro[%s]" % (g, b)
    seq = [base + ".inv"] + [base + ".d.chain.g[%d].u" % i for i in range(L)] + [base + ".inv"]
    fs = ss = 0
    for d, s in zip(seq, seq[1:]):
        a, c = hop(d, s); fs += a; ss += c
    pf, ps = 2 * fs, 2 * ss
    dev = max(abs(pf - float(r["xray_fastmin_ps"])), abs(ps - float(r["xray_slowmax_ps"])))
    worst = max(worst, dev); n += 1
    if n <= 3: print(ring, L, "own FAST %d SLOW %d | pred %s %s" % (pf, ps, r["xray_fastmin_ps"], r["xray_slowmax_ps"]))
print("rings walked %d; worst |own - pred| over FAST and SLOW: %d ps" % (n, worst))
