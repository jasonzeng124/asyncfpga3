#!/usr/bin/env python3
"""Independent token-level interpreter of Dynamatic handshake MLIR (auditor's own, agentG).
Unbounded FIFOs, fire any enabled op until quiescent (Kahn: result is schedule independent).
Semantics: two's complement wraparound at the op's width; shifts >= width follow Verilog
(shl/shrui -> 0, shrsi -> sign fill).  Usage: run(mlir_text, [x, n]) -> output value (unsigned) or None.
Optionally `narrow` maps i32 -> i<W> (for narrow-width exhaustive comparison)."""
import re, sys
from collections import deque

def parse(text):
    ops = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith(('module', 'handshake.func', '}')):
            continue
        # strip attribute dict {...} (first one after operands); keep type tail after last ':'
        m = re.match(r'^(?:(%[\w#:, %]+?)\s*=\s*)?(\w+)\s*(.*)$', line)
        lhs, op, rest = m.group(1), m.group(2), m.group(3)
        attrs = re.search(r'\{([^{}]*)\}', rest)
        attr = attrs.group(1) if attrs else ''
        body = rest[:attrs.start()] if attrs else rest
        tail = rest[attrs.end():] if attrs else ''
        # outputs
        outs = []
        if lhs:
            for part in [p.strip() for p in lhs.split(',')]:
                mm = re.match(r'^(%[\w]+)(?::(\d+))?$', part)
                if mm.group(2):
                    outs += [f'{mm.group(1)}#{i}' for i in range(int(mm.group(2)))]
                else:
                    outs.append(mm.group(1))
        ops.append(dict(op=op, outs=outs, body=body, attr=attr, tail=tail, line=line))
    return ops

def ints(s):
    return [int(x) for x in re.findall(r'<i(\d+)>', s)]

def mask(v, w):
    return v & ((1 << w) - 1)

def sgn(v, w):
    v = mask(v, w)
    return v - (1 << w) if v >> (w - 1) else v

def build(text):
    ops = parse(text)
    nodes = []
    for o in ops:
        op, body, tail, attr, outs = o['op'], o['body'], o['tail'], o['attr'], o['outs']
        operands = re.findall(r'%[\w#]+', body)
        widths = ints(tail)
        if op == 'end':
            operands = re.findall(r'%[\w#]+', tail)
        nodes.append(dict(op=op, ins=operands, outs=outs, attr=attr, body=body, w=widths, line=o['line']))
    return nodes

def run(text, args, maxfire=2_000_000):
    nodes = build(text)
    ch = {}
    def q(c):
        if c not in ch: ch[c] = deque()
        return ch[c]
    q('%arg0').append(args[0]); q('%arg1').append(args[1]); q('%arg2').append(0)
    result = None
    srcouts = {nd['outs'][0] for nd in nodes if nd['op'] == 'source'}
    fired_any = True; nf = 0
    while fired_any:
        fired_any = False
        for nd in nodes:
            op = nd['op']; ins = nd['ins']; outs = nd['outs']
            if op == 'source':
                if not q(outs[0]):
                    q(outs[0]).append(0); # bounded: one token buffered
                    fired_any = True
                continue
            if op == 'mux':
                s, a, b = ins
                if not q(s): continue
                sel = q(s)[0] & 1
                d = [a, b][sel]
                if not q(d): continue
                q(s).popleft(); v = q(d).popleft(); q(outs[0]).append(v)
                fired_any = True; nf += 1; continue
            if op == 'control_merge':
                for k, c in enumerate(ins):
                    if q(c):
                        v = q(c).popleft(); q(outs[0]).append(v); q(outs[1]).append(k)
                        fired_any = True; nf += 1
                        break
                continue
            if not all(q(c) for c in ins):
                continue
            if op == 'constant' and ins[0] in srcouts and q(outs[0]):
                continue  # eternal constant: keep one token buffered
            vals = [q(c).popleft() for c in ins]
            fired_any = True; nf += 1
            w = nd['w']
            if op == 'fork':
                for c in outs: q(c).append(vals[0])
            elif op == 'sink':
                pass
            elif op == 'end':
                result = vals[0]
            elif op == 'constant':
                mv = re.search(r'value = (-?\d+|true|false)', nd['attr']).group(1)
                ow = w[-1]
                v = {'true': 1, 'false': 0}.get(mv)
                if v is None: v = mask(int(mv), ow)
                q(outs[0]).append(v)
            elif op == 'cond_br':
                c, d = vals
                q(outs[0] if c & 1 else outs[1]).append(d)
            elif op in ('extui', 'extsi', 'trunci'):
                sw, dw = w[0], w[1]
                a = vals[0]
                if op == 'extui': v = mask(a, sw)
                elif op == 'extsi': v = mask(sgn(a, sw), dw)
                else: v = mask(a, dw)
                q(outs[0]).append(v)
            elif op == 'cmpi':
                pred = re.match(r'\s*(\w+)', nd['body']).group(1)
                ww = w[0]; a, b = mask(vals[0], ww), mask(vals[1], ww)
                sa, sb = sgn(a, ww), sgn(b, ww)
                r = dict(eq=a == b, ne=a != b, slt=sa < sb, sle=sa <= sb, sgt=sa > sb, sge=sa >= sb,
                         ult=a < b, ule=a <= b, ugt=a > b, uge=a >= b)[pred]
                q(outs[0]).append(int(r))
            else:
                ww = w[0]; a, b = mask(vals[0], ww), mask(vals[1], ww)
                if op == 'addi': v = a + b
                elif op == 'subi': v = a - b
                elif op == 'muli': v = a * b
                elif op == 'xori': v = a ^ b
                elif op == 'andi': v = a & b
                elif op == 'ori': v = a | b
                elif op == 'shli': v = (a << b) if b < ww else 0
                elif op == 'shrui': v = (a >> b) if b < ww else 0
                elif op == 'shrsi': v = (sgn(a, ww) >> min(b, ww))
                else: raise ValueError('unknown op ' + op + ' in ' + nd['line'])
                q(outs[0]).append(mask(v, ww))
            if nf > maxfire:
                return 'DIVERGE'
    # quiescent: check leftover tokens (other than sources' buffered ones)
    left = {c: list(v) for c, v in ch.items() if v and not any(nd['op']=='source' and c in nd['outs'] for nd in nodes)}
    return result, left

def narrow(text, W):
    t = text.replace('i32', f'i{W}')
    t = t.replace('2147483647', str((1 << (W - 1)) - 1))
    return t

if __name__ == '__main__':
    f, x, n = sys.argv[1], int(sys.argv[2], 0), int(sys.argv[3], 0)
    print(run(open(f).read(), [mask(x, 32), mask(n, 32)]))
