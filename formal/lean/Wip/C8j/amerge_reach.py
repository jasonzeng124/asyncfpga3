#!/usr/bin/env python3
"""Explicit-state reachability of the bdc_amerge2 SI model (C-8j), grants free
(H_ARB), with the counter differences the data proof needs.  Finds the
invariant that OpsCM.lean checks by `decide`.  It proves nothing.
Signals: xr xa yr ya g1 g2 zr za.
Rules: x, y senders and z receiver obey the protocol (environment);
g1 moves only to xr, and rises only if g2 and za are low (H_ARB, same for g2);
zr rises only while xa = ya = 0 (H_AMERGE_RTZ);
never g1 = g2 = 1 (H_ARB_EXCL);  zr moves only to g1|g2 (OR + delay);
xa = C(g1, za), ya = C(g2, za).
Counters: dxo = 1 + #x^ - #z^(won=0), dyo = 1 + #y^ - #z^(won=1),
won = g2 | ya (bdc's `won`), read after the step."""
import sys
names = "xr xa yr ya g1 g2 zr za".split()
N = len(names)
_B = [{n: (v >> i) & 1 for i, n in enumerate(names)} for v in range(1 << N)]
def bits(v): return _B[v]
_A = {}
def allowed(c, n):
    k = (id(c), id(n))
    if k not in _A: _A[k] = allowed0(c, n)
    return _A[k]
def allowed0(c, n):
    ch = lambda k: c[k] != n[k]
    if ch('xr') and c['xr'] != c['xa']: return False
    if ch('yr') and c['yr'] != c['ya']: return False
    if ch('za') and c['za'] == c['zr']: return False
    if ch('g1') and not (n['g1'] == c['xr'] and (not n['g1'] or (not c['g2'] and not c['za']))): return False
    if ch('g2') and not (n['g2'] == c['yr'] and (not n['g2'] or (not c['g1'] and not c['za']))): return False
    if n['g1'] and n['g2']: return False
    if ch('zr') and n['zr'] != (c['g1'] or c['g2']): return False
    if (not c['zr']) and n['zr'] and (c['xa'] or c['ya']): return False   # H_AMERGE_RTZ
    if ch('xa') and not (c['g1'] == n['xa'] and c['za'] == n['xa']): return False
    if ch('ya') and not (c['g2'] == n['ya'] and c['za'] == n['ya']): return False
    return True
init = (0, 1, 1)
seen = {init}; todo = [init]
while todo:
    v, dx, dy = todo.pop(); c = bits(v)
    for m in range(1 << N):
        n = bits(v ^ m)
        if not allowed(c, n): continue
        rz = (not c['zr']) and n['zr']; won = n['g2'] or n['ya']
        rx = (not c['xr']) and n['xr']; ry = (not c['yr']) and n['yr']
        s2 = (v ^ m, dx + rx - (rz and not won), dy + ry - (rz and won))
        if abs(s2[1]) > 3 or abs(s2[2]) > 3:
            print("diverge", c, n, dx, dy, file=sys.stderr); sys.exit(1)
        if s2 not in seen: seen.add(s2); todo.append(s2)
print("reachable:", len(seen), file=sys.stderr)
byb = {}
for v, dx, dy in seen: byb.setdefault(v, set()).add((dx, dy))
print("bit states:", len(byb), "functional:", all(len(s) == 1 for s in byb.values()),
      "dx", sorted({x[1] for x in seen}), "dy", sorted({x[2] for x in seen}), file=sys.stderr)
bad = 0
for v, dx, dy in seen:
    c = bits(v)
    for m in range(1 << N):
        n = bits(v ^ m)
        if not allowed(c, n): continue
        if c['xa'] != n['xa'] and c['xa'] == c['xr']: bad += 1
        if c['ya'] != n['ya'] and c['ya'] == c['yr']: bad += 1
        if c['zr'] != n['zr'] and c['zr'] != c['za']: bad += 1
        if (not c['zr']) and n['zr']:
            won = n['g2'] or n['ya']
            ok = c['za'] == 0 and ((won and c['yr'] and not c['ya'] and dy == 2 and n["g2"] and not c['g1'])
                                   or (not won and c['xr'] and not c['xa'] and dx == 2 and n["g1"] and not c['g2']))
            if not ok: bad += 1; print("bad offer", c, n, dx, dy, file=sys.stderr)
print("violations:", bad, file=sys.stderr)
if '-lean' in sys.argv:
    B = lambda b: 'true' if b else 'false'
    rows = ["⟨" + ", ".join(B(bits(v)[n]) for n in names) + f", {dx}, {dy}⟩" for v, dx, dy in sorted(seen)]
    print("def atbl : List AS := [\n  " + ",\n  ".join(rows) + "]")
