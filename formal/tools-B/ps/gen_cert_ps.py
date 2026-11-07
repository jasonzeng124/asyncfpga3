#!/usr/bin/env python3
"""Shard B (UNTRUSTED generator; the rows are checked in Lean by RaceCertPS.krowOK): Lean rows for a hold certificate
(ctlcert.py --tree) on THE target: per LUT node its pins (copy chain, source), the controlling pin set P with the
pre-cause source values (the reset pin counts as P with value low), the held value w, the feedback pin for a memory
hold, and the tied pins (constant gates).  usage: gen_cert_ps.py NET.json DUMP.json T0 SPEC...  where SPEC = NODE:P1,P2[:mem]"""
import json, sys
N = json.load(open(sys.argv[1])); D = json.load(open(sys.argv[2]))["nodes"]; T0 = int(sys.argv[3])
idx = {n: i for i, n in enumerate(N["nodes"])}; gates = N["gates"]; drv = {g["out"]: gi for gi, g in enumerate(gates)}
RST = 186905
def chain(n):
    m, ch = n, []
    while m in drv and gates[drv[m]]["k"] == 1 and gates[drv[m]]["init"] == 2:
        ch.append(drv[m]); m = gates[drv[m]]["ins"][0]
    return ch, m
def val(n, t):
    d = D.get(str(n)); v = d[0] if d else False
    for s in (d[1] if d else []):
        if s <= t: v = not v
        else: break
    return v
bl = lambda l: "[" + ", ".join("true" if b else "false" for b in l) + "]"
nl = lambda l: "[" + ", ".join(str(x) for x in l) + "]"
for spec in sys.argv[4:]:
    parts = spec.split(":"); q = idx[parts[0]]; P = [int(x) for x in parts[1].split(",")]; mem = len(parts) > 2
    g = gates[drv[q]]; k = g["k"]; pins = [chain(n) for n in g["ins"]]
    held = [False] * k; ov = [False] * k; bv = [False] * k; fb = k
    for i, (ch, s) in enumerate(pins):
        if s in drv and gates[drv[s]]["k"] == 0: held[i] = True; ov[i] = bool(gates[drv[s]]["init"] & 1)
        elif s == q: fb = i
        elif s == RST and i not in P: P.append(i)
    for i in P: bv[i] = val(pins[i][1], T0)
    w = val(q, T0)
    print("  ⟨%d, [%s], %s, %s, %s, %d, %s, %s, %s⟩,  -- %s" % (q, ", ".join("(%s, %d)" % (nl(ch), s) for ch, s in pins),
          nl(sorted(P)), bl(bv), "true" if w else "false", fb if mem else k, "true" if mem else "false", bl(held), bl(ov), parts[0]))
    print("    -- sources:", [(i, N["nodes"][s]) for i, (ch, s) in enumerate(pins)], file=sys.stderr)
