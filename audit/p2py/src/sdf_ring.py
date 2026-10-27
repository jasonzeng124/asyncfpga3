#!/usr/bin/env python3
"""Audit: independent ring-loop period from a nextpnr SDF (own parser, no repo imports).
For each ring prefix P (grp[g].ro[b]. or ro[i].), walk INTERCONNECT edges among cells
whose name starts with P, starting from P+'inv', until back; loop = sum(IC + IOPATH pin->out).
Period = 2*loop (max field, rise). Prints prefix, n_cells, period."""
import re, sys, json, collections
sdf = open(sys.argv[1]).read()
un = lambda s: s.replace("\\", "")
ic = collections.defaultdict(list)   # src_cell -> [(dst_cell, dst_pin, srcpin, ps)]
for m in re.finditer(r"\(INTERCONNECT (\S+)/(\w+) (\S+)/(\w+) \(([\d.]+):([\d.]+):([\d.]+)\)", sdf):
    s, sp, d, dp = un(m.group(1)), m.group(2), un(m.group(3)), m.group(4)
    ic[s].append((d, dp, sp, float(m.group(7))))
iop = {}
for m in re.finditer(r"\(INSTANCE ([^)]+)\)(.*?)(?=\(CELL|\Z)", sdf, re.S):
    inst = un(m.group(1).strip())
    for k in re.finditer(r"\(IOPATH (\w+) (\w+) \(([\d.]+):([\d.]+):([\d.]+)\)", m.group(2)):
        iop[(inst, k.group(1), k.group(2))] = float(k.group(5))
prefixes = sorted({re.match(r"(.*\.)inv$", c).group(1) for c in ic if re.match(r".*\.inv$", c)})
out = {}
for P in prefixes:
    cur, outpin, tot, n, seen = P + "inv", None, 0.0, 0, set()
    # inverter output pin: the IC whose dst is inside the ring
    while True:
        nxt = [e for e in ic[cur] if e[0].startswith(P) and e[0] != cur]
        assert len(nxt) == 1, (P, cur, nxt)
        d, dp, sp, ps = nxt[0]
        tot += ps
        outs = [k for k in iop if k[0] == d and k[1] == dp]
        # the output that feeds the next ring cell
        nn = [e for e in ic[d] if e[0].startswith(P) and e[0] != d]
        o = nn[0][2]
        tot += iop[(d, dp, o)]; n += 1
        cur = d
        if cur == P + "inv": break
        assert n < 200
    out[P] = (n, 2 * tot)
    print(P, n, int(round(2 * tot)))
if len(sys.argv) > 2: json.dump(out, open(sys.argv[2], "w"))
