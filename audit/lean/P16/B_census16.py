#!/usr/bin/env python3
"""Auditor P16 (copied parser/rules from P15 BC_census.py): independent re-implementation (Python, own parser of the generated
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
from collections import Counter
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


# ---- P16 extensions: arbiter (FiniteNetBoundA) and fork-tree (FiniteNetBoundT) rules ----
# mode 'A': request: M's rule (mode 136) else walk back through 2..4-forks and 1-input joins to an
#   amerge (arbReq); ack: M's rule else walk forward through 1-/2-input joins and a mux control
#   ack to an amerge (arbAck).  mode 'T': A plus, on the ack side, forward walk to a 5/6-way fork.
# j1req=False: RTL-faithful variant (P15 B1): a request is NOT traced back through a 1-input join.
def reqX(c, mode, j1req=True, F=40, trail=None):
    if F == 0: return None
    o = prod[c]; op = ops[o]; k = op[0]
    if k == "link": return ("lk", o)
    if k in ("steerC", "steerD"): return ("sb", o)
    if k in ("join", "bjoin"):
        if len(op[1]) == 2: return ("jr", o)
        if len(op[1]) == 1 and j1req:
            if trail is not None: trail.append(o)
            return reqX(op[1][0], mode, j1req, F - 1, trail)
        return None
    if k in ("forkG", "forkH"): return reqX(op[1][0], mode, j1req, F - 1, trail) if small_fork(op) else None
    if k == "mux": return ("md", o)
    if k == "amerge" and mode in ("A", "T"): return ("aR", o)
    return None
def ackX(c, mode, F=40):
    if F == 0: return None
    o = cons[c]; op = ops[o]; k = op[0]
    if k == "link": return ("lk", o)
    if k in ("steerC", "steerD"): return ("ao", o)
    if k in ("forkG", "forkH"):
        if small_fork(op): return ("fa", o)
        if mode == "T" and 5 <= len(op[2]) <= 6: return ("tR", o)
        return None
    if k in ("join", "bjoin"):
        if len(op[1]) in (1, 2): return ackX(op[2][0], mode, F - 1)
        return None
    if k == "mux":
        cc, x, y = op[1]
        return ackX(op[2][0], mode, F - 1) if c == cc else ("ma", o)
    if k == "amerge" and mode in ("A", "T"): return ("aA", o, c == op[1][1])
    return None
links = [(o, op[1][0], op[2][0]) for o, op in enumerate(ops) if op[0] == "link"]
print("links:", len(links))
for mode in ("M", "A", "T"):
    for j1 in (True, False):
        both = sum(1 for o, i, z in links if reqX(i, mode, j1) and ackX(z, mode))
        ur = Counter(endcls(i, "req") for o, i, z in links if reqX(i, mode, j1) is None)
        ua = Counter(endcls(z, "ack") for o, i, z in links if ackX(z, mode) is None)
        print("mode %s (1-input-join request tracing %s): both-bound %d; unbound req ends %s; unbound ack ends %s"
              % (mode, "ON (theirs)" if j1 else "OFF (RTL-faithful)", both, dict(ur), dict(ua)))
# which arbiter/tree-bound links rely on a 1-input join on the request side
for mode in ("A", "T"):
    dep = []
    for o, i, z in links:
        tr = []; r = reqX(i, mode, True, trail=tr)
        if r and tr and ackX(z, mode): dep.append((o, i, tr, r))
    print("mode %s: both-bound links whose request driver is reached through a 1-input join: %s" % (mode, dep))
newA = [o for o, i, z in links if reqX(i, "A") and ackX(z, "A") and not (reqX(i, "M") and ackX(z, "M"))]
newT = [o for o, i, z in links if reqX(i, "T") and ackX(z, "T") and not (reqX(i, "A") and ackX(z, "A"))]
print("newly both-bound M->A: %d %s" % (len(newA), newA))
print("newly both-bound A->T: %d %s" % (len(newT), newT))
left = [(o, i, z, reqX(i, "T") is not None, ackX(z, "T") is not None) for o, i, z in links if not (reqX(i, "T") and ackX(z, "T"))]
print("left unbound under T (link op, in ch, out ch, req bound, ack bound):", left)
trees = [(o, ops[o][0], len(ops[o][2])) for o, op in enumerate(ops) if op[0] in ("forkG", "forkH") and 5 <= len(op[2]) <= 6]
print("5/6-way forks:", trees)
