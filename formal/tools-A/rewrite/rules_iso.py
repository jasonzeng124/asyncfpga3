#!/usr/bin/env python3
"""rules_iso.py A B [MAPS.json] -- are two imported rule lists the same graph up to channel renaming and rule order?

A, B: either a dfimport .lean file (`def rules : List Rule := [...]`) or the output of Lean `#eval` of a List Rule.
Channels 0..2 (function arguments) are anchored to themselves; the rest is matched by propagation: a rule of A is
matched to the unique rule of B with the same kind, expression and parameters whose inputs agree with the channel
map so far; its channels are then mapped. Exit 0 and print ISOMORPHIC if every rule and channel is matched
consistently (a bijection), else exit 1 with what is left. Untrusted (a script, not a proof).
"""
import re, sys

def tokens(s):
    s = s.replace('Formal.Net.GcdHw.', '')
    s = re.sub(r'--[^\n]*', '', s)
    return re.findall(r'\[|\]|\(|\)|,|[A-Za-z_.][A-Za-z0-9_.]*|\d+', s)

def parse_list(ts, i):
    assert ts[i] == '['; i += 1; out = []
    while ts[i] != ']':
        v, i = parse_term(ts, i); out.append(v)
        if ts[i] == ',': i += 1
    return out, i + 1

def parse_term(ts, i):
    t = ts[i]
    if t == '[': return parse_list(ts, i)
    if t == '(':
        v, i = parse_app(ts, i + 1); assert ts[i] == ')'; return v, i + 1
    if t.isdigit(): return int(t), i + 1
    return (t.lstrip('.').split('.')[-1],), i + 1

def parse_app(ts, i):
    head = ts[i].lstrip('.').split('.')[-1]; i += 1; args = []
    while ts[i] not in (')', ',', ']'):
        v, i = parse_term(ts, i); args.append(v)
    return (head, *args), i

def load(path):
    s = open(path).read()
    if 'def rules' in s:
        s = s[s.index('def rules'):]; s = s[s.index('['):]
    else:
        s = s[s.index('['):]
    ts = tokens(s)
    # each element is an application: kind args...
    assert ts[0] == '['; i = 1; rules = []
    while ts[i] != ']':
        v, i = parse_app(ts, i); rules.append(v)
        if ts[i] == ',': i += 1
    return rules

def io(r):
    k = r[0]
    if k == 'comp': return list(r[1]), [r[2]], ('comp', r[3])
    if k == 'fork': return [r[1]], list(r[2]), ('fork', len(r[2]))
    if k == 'branch': return [r[1], r[2]], [r[3], r[4]], ('branch',)
    if k == 'mux': return [r[1]] + list(r[2]), [r[3]], ('mux', r[4], len(r[2]))
    if k == 'cm': return [r[1]], [r[2], r[3]], ('cm', r[4])
    if k == 'sink': return [r[1]], [], ('sink',)
    raise ValueError(r)

def main():
    A, B = load(sys.argv[1]), load(sys.argv[2])
    print(f"rules: {len(A)} vs {len(B)}")
    m = {0: 0, 1: 1, 2: 2}; used = set(m.values()); ma = {}; mb = set()
    changed = True
    while changed:
        changed = False
        for ia, ra in enumerate(A):
            if ia in ma: continue
            ina, outa, sa = io(ra)
            if not any(c in m for c in ina + outa): continue
            cands = []
            for ib, rb in enumerate(B):
                if ib in mb: continue
                inb, outb, sb = io(rb)
                if sa != sb or len(inb) != len(ina) or len(outb) != len(outa): continue
                ok = all(m.get(ca, cb) == cb for ca, cb in zip(ina + outa, inb + outb))
                ok = ok and all((cb not in used) or m.get(ca) == cb for ca, cb in zip(ina + outa, inb + outb))
                if ok: cands.append(ib)
            if len(cands) == 1:
                ib = cands[0]; inb, outb, _ = io(B[ib])
                for ca, cb in zip(ina + outa, inb + outb):
                    if ca not in m: m[ca] = cb; used.add(cb)
                ma[ia] = ib; mb.add(ib); changed = True
    if len(ma) == len(A) == len(B) and len(set(m.values())) == len(m):
        print("ISOMORPHIC (%d rules, %d channels)" % (len(A), len(m)))
        if len(sys.argv) > 3:
            import json
            json.dump({'chan': {str(a): b for a, b in m.items()}, 'rule': {str(a): b for a, b in ma.items()}},
                      open(sys.argv[3], 'w'))
        return 0
    print("NOT MATCHED: A rules", [i for i in range(len(A)) if i not in ma], "B rules", [i for i in range(len(B)) if i not in mb])
    return 1

sys.exit(main())
