#!/usr/bin/env python3
"""aug_synth.py (shard A, 2026-11-17; untrusted): a yosys-style netlist JSON for boundary_bench.py, made from an August
board build's ROUTED JSON (research/board/aug/builds/<k>_bench_gen/, the yosys JSON was not kept) and the bench
Verilog regenerated from the same commit.

    python3 aug_synth.py ROUTED.json BENCH.v OUT.json

nextpnr's routed JSON bit-blasts vectors ("x[3]") and drops nets that are only aliases. For every net the bench's udut
instantiation names, this restores: (1) vectors, regrouped from "x[i]"; (2) an alias through "assign A = B;" in BENCH.v,
either way round; (3) a register's Q, as the Q of the flop whose D net is yosys's "$0\\name"; (4) bd_fork's req_out,
which is its req broadcast (bd_fork .req(R) .req_out(V): every bit of V is R). Prints what it could not resolve.
"""
import json, re, sys
R = json.load(open(sys.argv[1])); bv = open(sys.argv[2]).read()
top = R["modules"]["top"]; nn = top["netnames"]; cells = top["cells"]
P = "bridge_i."
names = {n: v["bits"] for n, v in nn.items()}
vec = {}
for n, v in nn.items():
    m = re.match(r"(.*)\[(\d+)\]$", n)
    if m and len(v["bits"]) == 1: vec.setdefault(m.group(1), {})[int(m.group(2))] = v["bits"][0]
for b, d in vec.items():
    if b not in names and sorted(d) == list(range(len(d))): names[b] = [d[i] for i in range(len(d))]
assigns = re.findall(r"assign\s+(\w+)\s*=\s*(\w+)\s*;", bv)
qof = {}
for cn, c in cells.items():
    if c["type"] == "SLICE_FFX" and "D" in c["connections"] and "Q" in c["connections"]:
        qof[c["connections"]["D"][0]] = c["connections"]["Q"]
def resolve(w, depth=0):
    full = P + w
    if full in names: return names[full]
    if w in names: return names[w]
    if depth > 4: return None
    for a, b in assigns:
        if a == w:
            r = resolve(b, depth + 1)
            if r: return r
        if b == w:
            r = resolve(a, depth + 1)
            if r: return r
    for n, v in nn.items():
        if re.search(r"\$0\\\\?%s(\[\d+:\d+\])?$" % re.escape(w), n):
            q = qof.get(v["bits"][0])
            if q: return q
    m = re.search(r"assign\s+%s\s*=\s*([^;]+);" % re.escape(w), bv)
    if m and depth == 0:          # an expression: the LUT that reads every resolvable operand
        ops = [o for o in re.findall(r"[A-Za-z_]\w*", m.group(1)) if o != w]
        bits = set()
        for o in ops:
            r = resolve(o, depth + 1)
            if r and len(r) == 1: bits.add(r[0])
        if len(bits) >= 2:
            hits = [c["connections"]["O6"] for c in cells.values() if c["type"] == "SLICE_LUTX" and "O6" in c["connections"]
                    and bits <= set(b for pn, bb in c["connections"].items() if pn.startswith("A") for b in bb)]
            if len(hits) == 1: return hits[0]
    m = re.search(r"bd_fork\b[^;]*?\.req\((\w+)\)[^;]*?\.req_out\(%s\)" % re.escape(w), bv, re.S)
    if m:
        r = resolve(m.group(1), depth + 1)
        if r:
            wd = re.search(r"wire\s*\[(\d+):0\]\s*%s\b" % re.escape(w), bv)
            return r * (int(wd.group(1)) + 1 if wd else 1)
    return None
inst = re.search(r"\)\s*udut\s*\((.*?)\);", bv, re.S).group(1)
missing = []
for port, expr in re.findall(r"\.(\w+)\s*\(([^)]*)\)", inst):
    for w in re.findall(r"[A-Za-z_]\w*", expr):          # a name, or each part of a {a, b} concatenation
        if P + w in names: continue
        r = resolve(w)
        if r: names[P + w] = r
        else: missing.append((port, w))
# last resort, one 1-bit kernel INPUT left: the only net driven outside udut and read inside it not yet named
if len(missing) == 1:
    drv = {}; rd = {}
    for cn, c in cells.items():
        inside = cn.startswith(P + "udut.")
        for pn, bits in c["connections"].items():
            d = c.get("port_directions", {}).get(pn)
            for b in bits:
                if d == "output": drv[b] = inside
                elif d == "input" and inside: rd[b] = True
    named = set(b for n, bb in names.items() if n.startswith(P) and not n.startswith(P + "udut.") for b in bb)
    cand = [b for b in rd if drv.get(b) is False and b not in named]
    print("aug_synth: last-resort candidates for %s: %d" % (missing[0][1], len(cand)), file=sys.stderr)
    if len(cand) == 1:
        names[P + missing[0][1]] = cand; missing = []
out = {"modules": {"top": {"netnames": {n: {"bits": b} for n, b in names.items()}, "cells": cells, "ports": top.get("ports", {})}}}
json.dump(out, open(sys.argv[3], "w"))
print("aug_synth: unresolved udut nets: %s" % (missing or "none"), file=sys.stderr)
