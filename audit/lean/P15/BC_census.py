#!/usr/bin/env python3
"""Auditor P15bc: independent re-implementation (Python, own parser of the generated
Formal/Net/CapstoneNet.lean ops list; producers/consumers computed here, not taken from prodT/consT)
of shard B's link-side binding census:
  v63  = FiniteNetBound.reqSrc/ackSrc            (claimed 63/64/23/25)
  v124 = FiniteNetBoundM before 22c1807e         (claimed 124/25/25/1)
  v136 = FiniteNetBoundM at HEAD (1-input joins traced both ways)   (claimed 136/15/24/0)
and the end classes of unbound sides (claimed amerge 28, muxn 4, fork trees 6, source 1).
Also: which links are bound ONLY because a request is traced backwards through a 1-input
join, and whether those joins are bdc_fused compute units (with a matched delay chain).
Usage: python3 -I BC_census.py CapstoneNet.lean"""
import re, sys
src = open(sys.argv[1]).read()
body = src.split("def ops : List (K NC) := [", 1)[1].split("\n]\n", 1)[0]
ops = []
for line in body.split("\n"):
    line = line.strip().rstrip(",")
    if not line: continue
    m = re.match(r"K\.(\w+) (.*)", line); kind, rest = m.groups()
    def nums(s): return [int(x) for x in re.findall(r"\d+", s)]
    if kind == "forkG":
        mm = re.match(r"(\d+) \[(.*?)\]", rest); op = (kind, [int(mm.group(1))], nums(mm.group(2)))
    elif kind == "forkH":
        mm = re.match(r"(\d+) \[(.*?)\]", rest)
        outs = [int(a) for a, _ in re.findall(r"\((\d+), (\d+)\)", mm.group(2))]
        op = (kind, [int(mm.group(1))], outs)
    elif kind in ("join", "bjoin"):
        mm = re.match(r"\[(.*?)\] (\d+)", rest); op = (kind, nums(mm.group(1)), [int(mm.group(2))])
    elif kind in ("steerC", "steerD"):
        j, t, f = [int(x) for x in rest.split()[:3]]; op = (kind, [j], [t, f])
    elif kind == "mux":
        c, x, y, z = [int(x) for x in rest.split()[:4]]; op = (kind, [c, x, y], [z])
    elif kind == "muxn":
        c, x0, x1, x2, z = [int(x) for x in rest.split()[:5]]; op = (kind, [c, x0, x1, x2], [z])
    elif kind == "amerge":
        x, y, z = [int(x) for x in rest.split()[:3]]; op = (kind, [x, y], [z])
    elif kind == "link":
        i, o = [int(x) for x in rest.split()[:2]]; op = (kind, [i], [o])
    elif kind == "src":
        op = (kind, [], [int(rest.split()[0])])
    elif kind == "sink":
        op = (kind, [int(rest.split()[0])], [])
    else: raise SystemExit(kind)
    ops.append(op)
assert len(ops) == 367
prod, cons = {}, {}
for o, (k, ins, outs) in enumerate(ops):
    for c in outs: assert c not in prod; prod[c] = o
    for c in ins: assert c not in cons, (c, o); cons[c] = o
assert len(prod) == 465 and len(cons) == 465

def small_fork(op): return op[0] in ("forkG", "forkH") and 2 <= len(op[2]) <= 4

def req(c, mode, F=40, trail=None):
    if F == 0: return None
    o = prod[c]; op = ops[o]; k = op[0]
    if k == "link": return ("lk", o)
    if k in ("steerC", "steerD"): return ("sb", o)
    if k in ("join", "bjoin"):
        if len(op[1]) == 2: return ("jr", o)
        if len(op[1]) == 1 and mode == 136:
            if trail is not None: trail.append(o)
            return req(op[1][0], mode, F - 1, trail)
        return None
    if k in ("forkG", "forkH"): return req(op[1][0], mode, F - 1, trail) if small_fork(op) else None
    if k == "mux" and mode >= 124: return ("md", o)
    return None

def ack(c, mode, F=40):
    if F == 0: return None
    o = cons[c]; op = ops[o]; k = op[0]
    if k == "link": return ("lk", o)
    if k in ("steerC", "steerD"): return ("ao", o)
    if k in ("forkG", "forkH"): return ("fa", o) if small_fork(op) else None
    if k in ("join", "bjoin"):
        n = len(op[1])
        if n == 2 or (n == 1 and mode == 136): return ack(op[2][0], mode, F - 1)
        return None
    if k == "mux" and mode >= 124:
        cc, x, y = op[1]
        return ack(op[2][0], mode, F - 1) if c == cc else ("ma", o)
    return None

def endcls(c, side, F=40):
    o = prod[c] if side == "req" else cons[c]; op = ops[o]; k = op[0]
    if side == "req":
        if k in ("forkG", "forkH") and small_fork(op): return endcls(op[1][0], side, F - 1)
        if k in ("join", "bjoin") and len(op[1]) == 1: return endcls(op[1][0], side, F - 1)
    else:
        if k in ("join", "bjoin") and len(op[1]) in (1, 2): return endcls(op[2][0], side, F - 1)
        if k == "mux" and c == op[1][0]: return endcls(op[2][0], side, F - 1)
    if k in ("forkG", "forkH"): return "%s%d" % (k, len(op[2]))
    return k

links = [(o, op[1][0], op[2][0]) for o, op in enumerate(ops) if op[0] == "link"]
print("links:", len(links))
res = {}
for mode in (63, 124, 136):
    both = rq = ak = none = 0
    for o, i, z in links:
        r, a = req(i, mode) is not None, ack(z, mode) is not None
        both += r and a; rq += r and not a; ak += a and not r; none += not r and not a
        res.setdefault(o, {})[mode] = (r, a)
    print("mode %d: both %d, req-only %d, ack-only %d, neither %d; unbound sides %d"
          % (mode, both, rq, ak, none, rq + ak + 2 * none))
from collections import Counter
ur = Counter(endcls(i, "req") for o, i, z in links if req(i, 136) is None)
ua = Counter(endcls(z, "ack") for o, i, z in links if ack(z, 136) is None)
print("HEAD unbound request sides end at:", dict(ur))
print("HEAD unbound ack sides end at:", dict(ua))
# links whose binding at HEAD depends on a request traced back through a 1-input join
dep = []
for o, i, z in links:
    tr = []
    r = req(i, 136, trail=tr)
    if r is not None and tr: dep.append((o, i, tr, r))
j1 = [o for o, op in enumerate(ops) if op[0] in ("join", "bjoin") and len(op[1]) == 1]
print("1-input joins:", [(o, ops[o][0]) for o in j1])
print("links whose request driver at HEAD is reached by tracing back through a 1-input join: %d" % len(dep))
for o, i, tr, r in dep:
    print("  link op %d (in ch %d): through join ops %s -> driver %s; v124 req bound=%s, v136 both=%s"
          % (o, i, tr, r, res[o][124][0], all(res[o][136])))
new = [o for o, _, _ in links if all(res[o][136]) and not all(res[o][124])]
newreq = [o for o in new if not res[o][124][0]]
newack = [o for o in new if not res[o][124][1]]
print("links newly both-bound 124->136: %d (request side newly bound: %d, ack side newly bound: %d)"
      % (len(new), len(newreq), len(newack)))
print("  of these, both-bound at HEAD only thanks to a request traced through a 1-input join:",
      len([o for o in new if any(d[0] == o for d in dep)]))
# request drivers that are compute-join C-elements ('jr' of a .join = a bdc_fused unit, whose real
# z_req driver is the unit's uor + bd_delay_gated chain) vs steer-internal bjoins
cj = [(o, req(i, 136)) for o, i, z in links if req(i, 136) and req(i, 136)[0] == "jr" and ops[req(i, 136)[1]][0] == "join"]
bj = [(o, req(i, 136)) for o, i, z in links if req(i, 136) and req(i, 136)[0] == "jr" and ops[req(i, 136)[1]][0] == "bjoin"]
print("HEAD: link request sides bound to a 2-input COMPUTE join's C-element: %d %s" % (len(cj), sorted(set(d[1] for _, d in cj))))
print("HEAD: link request sides bound to a steer-internal bjoin C-element: %d" % len(bj))
