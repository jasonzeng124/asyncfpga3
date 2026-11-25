#!/usr/bin/env python3
"""scan_inc.py MLIR... -- find loop tests of the form cmpi P, (addi i, c), b  (or b, (addi i, c)) in handshake MLIR.

For each match print: kernel, cmp name, predicate, side of the add, step c, what b is (ring mux / constant / other),
whether the ring value is read only by the compare and its own back edge, and whether i is a loop mux.
Untrusted scan (a census for the general rewrite), not a check.
"""
import re, sys, collections

OPRE = re.compile(r'^\s*(?P<res>(%[\w]+(?::\d+)?)(\s*,\s*%[\w]+)*)\s*=\s*(?P<op>[\w.]+)\s+(?P<rest>.*)$')

def parse(path):
    defs, ops = {}, []
    for ln in open(path):
        m = OPRE.match(ln)
        if not m:
            continue
        res = [r.strip() for r in m.group('res').split(',')]
        op, rest = m.group('op'), m.group('rest')
        name = re.search(r'handshake.name = "([^"]+)"', rest)
        name = name.group(1) if name else '?'
        args = rest.split('{')[0]
        pred = None
        if op == 'cmpi':
            pred, args = args.split(',', 1)
            pred = pred.strip()
        operands = re.findall(r'%[\w]+(?:#\d+)?', args)
        val = re.search(r'value = (-?\d+|true|false)', rest)
        o = dict(op=op, name=name, res=res, operands=operands, pred=pred, value=val.group(1) if val else None, line=ln)
        idx = len(ops); ops.append(o)
        for r in res:
            if ':' in r:
                base, n = r.split(':')
                for k in range(int(n)):
                    defs[f'{base}#{k}'] = idx
                defs[base] = idx
            else:
                defs[r] = idx
    uses = collections.defaultdict(list)
    for i, o in enumerate(ops):
        for k, a in enumerate(o['operands']):
            uses[a].append((i, k))
    # whole-text use counts for values used outside ops we parsed (sinks, end)
    text = open(path).read()
    return ops, defs, uses, text

def through_forks(ops, defs, v):
    i = defs.get(v)
    while i is not None and ops[i]['op'] in ('fork', 'lazy_fork'):
        v = ops[i]['operands'][0]; i = defs.get(v)
    return v, i

def main():
    for path in sys.argv[1:]:
        k = path.split('/')[-1].replace('.mlir', '')
        ops, defs, uses, text = parse(path)
        for o in ops:
            if o['op'] != 'cmpi':
                continue
            for side in (0, 1):
                a = o['operands'][side]; b = o['operands'][1 - side]
                av, ai = through_forks(ops, defs, a)
                if ai is None or ops[ai]['op'] not in ('addi', 'subi'):
                    continue
                add = ops[ai]
                step = None; ivar = None
                for s2 in (0, 1):
                    cv, ci = through_forks(ops, defs, add['operands'][s2])
                    if ci is not None and ops[ci]['op'] == 'constant' and ops[ci]['value'] not in (None, 'true', 'false'):
                        step = int(ops[ci]['value']) * (-1 if add['op'] == 'subi' else 1)
                        if add['op'] == 'subi' and s2 == 0:
                            step = None; continue
                        ivar = add['operands'][1 - s2]
                if step is None:
                    continue
                iv, ii = through_forks(ops, defs, ivar)
                ikind = ops[ii]['op'] if ii is not None else 'arg'
                bv, bi = through_forks(ops, defs, b)
                bkind = ops[bi]['op'] if bi is not None else 'arg'
                bconst = ops[bi]['value'] if bkind == 'constant' else None
                # who reads the condition: cond_br whose data is the add (the back edge)?
                cres = o['res'][0]
                creaders = [ops[u[0]] for f in [cres] + [x for x in defs if defs[x] == defs.get(cres) and False] for u in uses.get(f, [])]
                # follow the fork of the condition
                conds = []
                stack = [cres]
                while stack:
                    v = stack.pop()
                    for (ui, uk) in uses.get(v, []):
                        uo = ops[ui]
                        if uo['op'] in ('fork', 'lazy_fork'):
                            stack.extend(f"{uo['res'][0].split(':')[0]}#{j}" for j in range(int(uo['res'][0].split(':')[1])) ) if ':' in uo['res'][0] else stack.append(uo['res'][0])
                        else:
                            conds.append((uo['op'], uo['name'], uk))
                nbr = sum(1 for c in conds if c[0] == 'cond_br' and c[2] == 0)
                print(f"{k:24s} {o['name']:8s} {o['pred']:4s} side={side} {add['op']}{step:+d} i={ikind:8s} b={bkind}{'=' + bconst if bconst else ''} condbr={nbr} other={[c for c in conds if not (c[0]=='cond_br' and c[2]==0)]}")

main()
