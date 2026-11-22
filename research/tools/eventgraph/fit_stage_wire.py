#!/usr/bin/env python3
"""fit_stage_wire.py RUNS -- fit whatif's per-inserted-stage wire term on the second-latch builds (xorshift x0.5, seeds
1-4: p8, all3, mo, p8mo, p11, p12) and test it, unchanged, on this session's step-4 builds (pmf, ipowfm, colb,
col cd+merge link, colfm).  Prints mean / max |error| on both sets for each candidate value."""
import sys, os, statistics as st
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search, whatif  # noqa: E402
R = sys.argv[1]
P8, P11, P12 = "depth:ulink_n_trueResult_8:3:0", "depth:ulink_n11__1:3:0", "depth:ulink_n_trueResult_12:1:0"
MO = "stage:ucontrol_merge0_req:ucontrol_merge0_ack:4:6:fastrise"
FF = "fastfall:BDC"
train, test = [], []
for s in (1, 2, 3, 4):
    for v, e in (("p8", [P8]), ("all3", [P8, P11, P12]), ("mo", [MO]), ("p8mo", [P8, MO])):
        train.append(("x50_%d" % s, "%s_%d" % (v, s), e))
for s in (1, 2, 3, 4):
    test += [("col_cd_%d" % s, "col_cdmo_%d" % s, [MO]), ("col_cd_%d" % s, "colfm_%d" % s, [FF, MO]),
             ("colcdb_%d" % s, "colb_%d" % s, [FF, MO]), ("ipow_%d" % s, "ipowfm_%d" % s, [FF, MO])]
for s in (1, 3, 4, 5):
    test.append(("x50_%d" % s, "pmf_%d" % s, [P8, FF, MO]))
for s in (5, 6, 8):
    test.append(("ipow_%d" % s, "ipowfm_%d" % s, [FF, MO]))
cache = {}
def meas(n):
    if n not in cache: cache[n] = whatif.G("%s/r/%s/eventgraph" % (R, n)).P
    return cache[n]
bases = {}
def err(rows, x):
    out = []
    for b, v, e in rows:
        if not os.path.exists("%s/r/%s/eventgraph/kernel.v" % (R, v)): continue
        if b not in bases: bases[b] = whatif.G("%s/r/%s/eventgraph" % (R, b))
        g = bases[b]; g.stage_wire = x
        (l, c), _ = search.predict(g, e)
        out.append(l - meas(v))
    return out
for x in (0, 500, 1000, 1500, 2000, 2500):
    a, b = err(train, x), err(test, x)
    print("stage_wire %4d ps: train n=%d mean %+.2f |err| %.2f max %.2f   test n=%d mean %+.2f |err| %.2f max %.2f" % (
        x, len(a), st.mean(a) / 1e3, st.mean(map(abs, a)) / 1e3, max(map(abs, a)) / 1e3,
        len(b), st.mean(b) / 1e3, st.mean(map(abs, b)) / 1e3, max(map(abs, b)) / 1e3))
