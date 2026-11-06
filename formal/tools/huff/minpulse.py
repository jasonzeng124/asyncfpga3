#!/usr/bin/env python3
"""Shard C (UNTRUSTED): narrowest pulse after reset on any node of a dumped run, and the nodes with pulses < w.
usage: minpulse.py net.json dump.json R w"""
import json, sys
N = json.load(open(sys.argv[1]))["nodes"]; d = json.load(open(sys.argv[2])); R = int(sys.argv[3]); w = int(sys.argv[4])
bad = []; mn = None
for k, v in d["nodes"].items():
    ts = [t for t in v[1] if t > R + 5000]
    for a, b in zip(ts, ts[1:]):
        if mn is None or b - a < mn: mn = b - a
        if b - a < w: bad.append((b - a, N[int(k)], a)); break
print("narrowest pulse after R+5ns:", mn, "; nodes with a pulse <", w, "ps:", len(bad))
for x in sorted(bad)[:12]: print("  ", x)
