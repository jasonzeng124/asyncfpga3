#!/usr/bin/env python3
"""Explicit-state reachability of the bd_link (Muller) model used by
Formal/Net/OpsLink.lean (SI node, DI wires to ack_in and req_out, four-phase
environment on both sides).  Counters: d = 1 + #or^ - #ia_fall,
q = 1 + #ia^ - #oa_fall.  Checks the protocol guarantees and the offer facts,
prints the table with -lean.  Proves nothing: Lean re-checks the closure."""
import sys, itertools

def ctl(r, n, q):          # C(req_in, ~ack_out): ctlB r n q false
    return (r and not n) or (q and (r or not n))

def succ(s):
    ir, ia, c, orq, oa, d, q = s
    for ir2 in ([ir, not ir] if ir == ia else [ir]):
        for oa2 in ([oa, not oa] if oa != orq else [oa]):
            t = ctl(ir, oa, c)
            for c2 in ([c, t] if t != c else [c]):
                for ia2 in ([ia, c] if c != ia else [ia]):
                    for or2 in ([orq, c] if c != orq else [orq]):
                        d2 = d + (not orq and or2) - (ia and not ia2)
                        q2 = q + (not ia and ia2) - (oa and not oa2)
                        yield (ir, ia, c, orq, oa, d, q), (ir2, ia2, c2, or2, oa2, d2, q2)

init = (False, False, False, False, False, 1, 1)
seen = {init}; todo = [init]; bad = []
while todo:
    s = todo.pop()
    for e, n in succ(s):
        ir, ia, c, orq, oa, d, q = e
        ir2, ia2, c2, or2, oa2, d2, q2 = n
        if ia2 != ia and ia == ir: bad.append(("recv", e, n))
        if or2 != orq and orq != oa: bad.append(("send", e, n))
        if (not orq) and or2:
            if not (c and c2 and (ir or ia) and (ir2 or ia2) and d == 1 and not (ia and not ia2)):
                bad.append(("offer", e, n))
        if (orq or oa) and (or2 or oa2):
            if not ((not c2) or (c and (ir or ia) and (ir2 or ia2))):
                bad.append(("held", e, n))
        if c and not (ir or ia): bad.append(("tx", e, n))
        if q2 < 0 or q2 > 2 or d2 < 0 or d2 > 2: bad.append(("ctr", e, n))
        if n not in seen:
            seen.add(n); todo.append(n)
print("link reachable states:", len(seen), "violations:", len(bad), file=sys.stderr)
for b in bad[:5]: print(b, file=sys.stderr)
fun = {}
for s in seen: fun.setdefault(s[:5], set()).add(s[5:])
print("counters a function of the state:", all(len(v) == 1 for v in fun.values()), file=sys.stderr)
print("q range:", sorted({s[6] for s in seen}), "d range:", sorted({s[5] for s in seen}), file=sys.stderr)
if "-lean" in sys.argv:
    b = lambda x: "true" if x else "false"
    rows = sorted(seen, key=lambda s: (s[5], s[6], s[:5]))
    print("def ltbl : List LS := [")
    print(",\n".join("  ⟨" + ", ".join([b(x) for x in s[:5]] + [str(s[5]), str(s[6])]) + "⟩" for s in rows))
    print("]")
