#!/usr/bin/env python3
# Survey every bd_delay chain stage in a routed.json: inputs connected, LUT function (AND/OR/BUF) and
# which net feeds each input. usage: survey_chains.py routed.json
import json, re, sys
from collections import defaultdict, Counter
m = json.load(open(sys.argv[1]))['modules']['top']
cells = m['cells']
RE = re.compile(r'^(?P<base>.+)\.chain\.g\[(?P<i>\d+)\]\.u$')
def func(c):
    init = c['parameters'].get('INIT', '')
    ins = sorted([p for p, v in c['connections'].items() if p.startswith('A') and v], key=lambda p: int(p[1:]))
    bits = init[::-1]  # bit k = string[-1-k]
    idx = {p: int(p[1:]) - 1 for p in ins}
    # nextpnr-xilinx keeps the logical INIT (2^n bits over the n connected inputs, MSB first);
    # AND/OR/BUF are symmetric so the logical-to-physical pin order does not matter for them.
    assert len(init) == 1 << len(ins), (init, ins)
    return ins, bits
chains = defaultdict(dict)
for name, c in cells.items():
    mm = RE.match(name)
    if mm: chains[mm.group('base')][int(mm.group('i'))] = name
kinds = Counter(); ex = {}
for base, st in chains.items():
    n = max(st) + 1
    sig = []
    for i in range(1, n):
        ins, tt = func(cells[st[i]])
        sig.append(tt)
    kind = 'N=1' if n == 1 else ('SYM(BUF)' if all(t == '01' for t in sig) else
            'FASTFALL(AND)' if all(t == '0001' for t in sig) else 'FASTRISE(OR)' if all(t == '0111' for t in sig) else 'OTHER:' + ','.join(sorted(set(sig))))
    tag = base.split('.')[-1]
    kinds[(tag, kind)] += 1; ex.setdefault((tag, kind), (base, n))
for k, v in sorted(kinds.items()): print(f"{v:5d}  {k[0]:<10} {k[1]:<16} e.g. {ex[k][0]} N={ex[k][1]}")
