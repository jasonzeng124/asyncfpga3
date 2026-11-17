#!/usr/bin/env python3
"""tools-B/preload/joinscan.py KERNEL_BENCH.v SIZES.vh (shard B, UNTRUSTED, static): joins fed by two or more sized operators.

For every bd_join in the kernel module, each request input is traced back through assigns and forks to what produced it:
an operator instance with a matched delay (.DELAY(DELAY_X), size BD_SZ_BRIDGE_I_UDUT_X from SIZES), a link (a capture
point: its latches hold the data, so the trace stops), or anything else. A join whose inputs come from two or more sized
operators releases its request at the LATER of their delayed requests, so (hypothesis, tested only on xorshift's ucond_br6:
FOR-RESEARCH B2) the operators other than the slowest pay for a capture that does not happen at their own request. Prints
those joins, their inputs' sizes, and the inputs that are not the largest (candidates to try at 0, by draws + preload).
Limit: it compares SIZES, not arrival times. Two operators fed by the same token (xorshift's uaddi0 / ucmpi1, collatz's
uaddi1 / ucmpi2) start together, so size ~ arrival; an operator deeper in a chain (xori2, uselect0) starts later, and
its size says nothing about which request is last. The draws decide; this only proposes.
"""
import re, sys
V = open(sys.argv[1]).read(); S = open(sys.argv[2]).read()
size = {m.group(1): int(m.group(2)) for m in re.finditer(r"`define BD_SZ_BRIDGE_I_UDUT_(\w+)\s+(\d+)", S)}
m = re.search(r"\nmodule bdc_(?!fused|amerge)\w+[\s\S]*?\nendmodule", V)
K = m.group(0) if m else V
alias = {}
for a in re.finditer(r"assign\s+(\w+)_req\s*=\s*(\w+)_req\s*;", K): alias[a.group(1)] = a.group(2)
src = {}   # net -> ("op", inst, param) | ("link", inst) | ("fork", srcnet)
for inst in re.finditer(r"\n\s*(\w+)\s*(#\(([^;]*?)\))?\s*(\w+)\s*\(([^;]*?)\);", K):
    typ, params, name, body = inst.group(1), inst.group(3) or "", inst.group(4), inst.group(5)
    if typ in ("module", "assign", "wire", "input", "output"): continue
    if typ == "bd_fork":
        s = re.search(r"\.req\((\w+)_req\)", body); outs = re.search(r"\.req_out\(\{([^}]*)\}\)", body)
        if s and outs:
            for o in outs.group(1).split(","): src[o.strip()[:-4]] = ("fork", s.group(1))
        continue
    z = re.search(r"\.(?:z_req|req_out)\((\w+)_req\)", body)
    if not z: continue
    if typ in ("bd_link", "bd_pipe") or name.startswith("ulink"): src[z.group(1)] = ("link", name); continue
    d = re.search(r"\.DELAY\(DELAY_(\w+)\)", params)
    src[z.group(1)] = ("op", name, d.group(1) if d else None)
def trace(n, depth=0):
    while n in alias and depth < 50: n = alias[n]; depth += 1
    s = src.get(n)
    if s is None: return ("?", n)
    if s[0] == "fork": return trace(s[1], depth + 1)
    return s
rows = 0
for j in re.finditer(r"bd_join\s*#\(\.N\((\d+)\)\)\s*(\w+)\s*\(([^;]*?)\);", K):
    ins = [x.strip()[:-4] for x in re.search(r"\.req_in\(\{([^}]*)\}\)", j.group(3)).group(1).split(",")]
    tr = [trace(i) for i in ins]
    ops = [(t[1], t[2], size.get(t[2]) if t[2] else None) for t in tr if t[0] == "op" and t[2]]
    if len([o for o in ops if o[2]]) < 2: continue
    mx = max(o[2] for o in ops if o[2] is not None)
    desc = ", ".join("%s(%s)" % (t[1], ("size %s" % size.get(t[2])) if t[0] == "op" else t[0]) for t in tr)
    cand = [o[0] for o in ops if o[2] is not None and o[2] < mx]
    print("%-14s <- %s ; not the largest: %s" % (j.group(2), desc, ", ".join(cand) or "(tie)")); rows += 1
print("# %d joins fed by >= 2 sized operators" % rows)
