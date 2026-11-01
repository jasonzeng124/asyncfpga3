#!/usr/bin/env python3
"""zero_readers.py (audit T9): which nodes of the decoded net are read by a zero-delay pin (arc 0/0/0/0, so Spec's
Adm forces read delay 0 and Gate.start = 0)?  Under SpecRunt's H_RUNT(w) such a node can never carry a pulse narrower
than w (the reader cannot skip it).   python3 -I zero_readers.py NET.json BND.json"""
import json, sys, collections
N = json.load(open(sys.argv[1])); G = N["gates"]; idx = {n: i for i, n in enumerate(N["nodes"])}
B = json.load(open(sys.argv[2]))["boundary"]
zero = lambda e: e["fmin"] == e["fmax"] == e["smin"] == e["smax"] == 0
readers = collections.defaultdict(list)
for g in G:
    for p, i in enumerate(g["ins"]):
        readers[i].append((g, p))
c = collections.Counter()
for g in G:
    if g["kind"] in ("lut6", "lut5", "muxf", "carry"):
        rs = readers.get(g["out"], [])
        c["no reader" if not rs else "read by a zero-delay pin" if any(zero(r["arcs"][p]) for r, p in rs) else "only nonzero-delay readers"] += 1
print("LUT/MUXF/CARRY outputs:", dict(c))
print("zero-arc pins by reading gate kind:", dict(collections.Counter(g["kind"] for g in G for e in g["arcs"] if zero(e))))
for k in ("out0_req", "a_ack", "b_ack", "start_ack", "pend_ack"):
    n = idx[B[k]]
    print("boundary output %-9s %s read by:" % (k, B[k]), [(g["name"], g["kind"], "ZERO-DELAY" if zero(g["arcs"][p]) else "delay") for g, p in readers[n]])
