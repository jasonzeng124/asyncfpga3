#!/usr/bin/env python3
"""hsinterp.py -- a small token-level interpreter for Dynamatic handshake MLIR (handshake_transformed.mlir).

Written for the differential check of inc_cmp.py (original vs rewritten kernel on the same inputs); it is NOT a
model of bdc's circuits and NOT a reference for any kernel.  Semantics:

  * every SSA value is a FIFO channel of capacity CAP (default 1); an op fires when its inputs are present and its
    outputs have room; values are unsigned ints masked to the width named in the op's own type;
  * fork / lazy_fork are eager (each output takes its copy independently); merge takes the first present input;
    control_merge also emits the index; mux waits for its select, then that data input; cond_br, select, br,
    constant, source, sink, extui / extsi / trunci, add / sub / mul / and / or / xor / shl / shrui / shrsi /
    divsi / divui / remsi, cmpi (all predicates);
  * memory: mem_controller accesses execute as soon as their operands are present (load: read, store: write;
    store-count tokens consumed and ignored); memEnd fires on the end-control token;  lsq executes its accesses
    strictly in program order: a group's control token appends the group's accesses to a queue, and the head of
    the queue runs when its operands are present (sequential semantics).  `lsq[MC]` (an LSQ behind an MC) is
    refused.  handshake.ram is an internal array with its initial value.
  * scheduling: sweeps over the ops in file order (or in a seeded random order per sweep), firing every enabled op,
    until a sweep fires nothing (quiescence) or a step limit is hit.

Result of a run: the first token value on each `end` operand, the number of tokens each got, every memory's final
contents, and whether the run quiesced or hit the limit.
"""
import random
import re
from collections import deque

VALRE = re.compile(r'%[\w]+(?:#\d+)?')
DEFRE = re.compile(r'^\s*(?P<res>%[\w]+(?::\d+)?(?:\s*,\s*%[\w]+(?::\d+)?)*)\s*=\s*(?P<op>"?[\w.]+"?)\s*(?P<rest>.*)$')
NODEFRE = re.compile(r'^\s*(?P<op>sink|end)\s+(?P<rest>.*)$')


class Unsupported(Exception):
    pass


def expand(res):
    out = []
    for r in res.split(','):
        r = r.strip()
        if ':' in r:
            b, n = r.split(':')
            out.extend(f'{b}#{k}' for k in range(int(n)))
        else:
            out.append(r)
    return out


def ints(s):
    return [int(x) for x in re.findall(r'<i(\d+)>', s)]


def mask(v, w):
    return v & ((1 << w) - 1)


def sgn(v, w):
    v = mask(v, w)
    return v - (1 << w) if w and v >> (w - 1) else v


class Op:
    def __init__(self, **kw):
        self.__dict__.update(kw)


def parse(text):
    ops, args, mems = [], [], {}
    func = None
    for ln in text.splitlines():
        if 'handshake.func' in ln:
            sig = ln[ln.index('(') + 1:ln.index(') ->')]
            for name, ty in re.findall(r'(%arg\d+):\s*((?:memref<[^>]*>)|(?:!handshake\.\w+<[^>]*>))', sig):
                args.append((name, ty))
            func = re.search(r'@(\w+)', ln).group(1)
            continue
        m = DEFRE.match(ln)
        if m:
            res, op, rest = expand(m.group('res')), m.group('op').strip('"'), m.group('rest')
        else:
            m = NODEFRE.match(ln)
            if not m:
                continue
            res, op, rest = [], m.group('op'), m.group('rest')
        cut = rest.rfind('}')
        attrs = rest[:cut + 1] if cut >= 0 else ''
        tail = rest[cut + 1:]
        if op in ('end', 'sink'):
            operands = VALRE.findall((rest[:rest.index('{')] if '{' in rest else '') + tail.split(':')[0])
        else:
            pre = rest[:rest.index('{')] if '{' in rest else rest
            operands = VALRE.findall(pre)
        o = Op(op=op, res=res, rest=rest, attrs=attrs, tail=tail, operands=operands, line=ln.strip())
        if op == 'cmpi':
            o.pred = rest.split(',')[0].strip()
        if op == 'constant':
            v = re.search(r'value = (-?\d+|true|false)', attrs)
            o.w = ints(tail)[-1]
            o.val = mask({'true': 1, 'false': 0}.get(v.group(1), None) if v.group(1) in ('true', 'false')
                         else int(v.group(1)), o.w)
        if op in ('mem_controller', 'lsq'):
            mm = re.match(r'\[(%\w+|MC)', rest)
            if mm.group(1) == 'MC':
                raise Unsupported('lsq[MC]')
            o.mem = mm.group(1)
            inner = rest[rest.index(']') + 1:rest.index('{')]
            if op == 'mem_controller':
                pm = re.match(r'\s*(%[\w#]+)\s*\((.*)\)\s*(%[\w#]+)\s*$', inner)
                if not pm:
                    pm2 = re.match(r'\s*(%[\w#]+)\s*\(\)\s*(%[\w#]+)\s*$', inner)
                    raise Unsupported('mem_controller with no accesses')
                o.start, o.acc, o.endc = pm.group(1), VALRE.findall(pm.group(2)), pm.group(3)
            else:
                lst = VALRE.findall(inner)
                o.start, o.acc, o.endc = lst[0], lst[1:-1], lst[-1]
                o.groups = [int(x) for x in re.findall(r'(\d+) : i32', re.search(r'groupSizes = \[([^\]]*)\]', attrs).group(1))]
        if op == 'ram':
            o.memdecl = rest
        ops.append(o)
    return func, args, ops


class Sim:
    def __init__(self, text, cap=1):
        self.func, self.args, self.ops = parse(text)
        self.cap = cap
        self.ch = {}
        self.defop = {}
        for o in self.ops:
            for r in o.res:
                self.defop[r] = o
        for o in self.ops:
            for v in o.res + o.operands:
                self.ch.setdefault(v, deque())
        for a, _ in self.args:
            self.ch.setdefault(a, deque())
        self.mems = {}
        self.memw = {}
        for a, ty in self.args:
            if ty.startswith('memref'):
                n, w = re.match(r'memref<(\d+)xi(\d+)>', ty).groups()
                self.mems[a] = [0] * int(n)
                self.memw[a] = int(w)
        for o in self.ops:
            if o.op == 'handshake.ram':
                n, w = re.search(r'-> memref<(\d+)xi(\d+)>', o.rest).groups()
                n, w = int(n), int(w)
                dv = re.search(r'dense<([^>]*)>', o.rest).group(1)
                if dv.startswith('['):
                    vals = [mask(int(x), w) for x in dv.strip('[]').split(',')]
                else:
                    vals = [mask(int(dv), w)] * n
                self.mems[o.res[0]] = vals
                self.memw[o.res[0]] = w
        for o in self.ops:
            self.prep(o)
        self.ends = None
        self.fired = 0

    # -- helpers -----------------------------------------------------------
    def has(self, v):
        return len(self.ch[v]) > 0

    def room(self, v):
        return len(self.ch[v]) < self.cap

    def pop(self, v):
        return self.ch[v].popleft()

    def push(self, v, x):
        self.ch[v].append(x)

    def prep(self, o):
        op = o.op
        if op in ('fork', 'lazy_fork'):
            o.sent = [False] * len(o.res)
        if op in ('mem_controller', 'lsq'):
            # classify accesses by their producer
            o.kinds = []
            i = 0
            loads = 0
            while i < len(o.acc):
                d = self.defop.get(o.acc[i])
                if d is not None and d.op == 'load':
                    o.kinds.append(('ld', o.acc[i], loads))
                    loads += 1
                    i += 1
                elif d is not None and d.op == 'store':
                    o.kinds.append(('st', o.acc[i], o.acc[i + 1]))
                    i += 2
                elif op == 'lsq':
                    o.kinds.append(('ctl', o.acc[i]))
                    i += 1
                else:
                    o.kinds.append(('cnt', o.acc[i]))
                    i += 1
            o.nloads = loads
            o.outs = o.res[:loads]
            o.memend = o.res[loads]
            if len(o.res) != loads + 1:
                raise Unsupported(f'{op}: {len(o.res)} results for {loads} loads')
            o.started = False
            if op == 'lsq':
                # groups: [(ctl channel, [access...])]
                o.glist = []
                k = 0
                cur = None
                for kd in o.kinds:
                    if kd[0] == 'ctl':
                        cur = (kd[1], [])
                        o.glist.append(cur)
                    else:
                        cur[1].append(kd)
                if [len(g[1]) for g in o.glist] != o.groups:
                    raise Unsupported(f'lsq group layout {[len(g[1]) for g in o.glist]} != {o.groups}')
                o.queue = deque()

    def wid(self, o):
        t = ints(o.tail)
        return t

    # -- one op ------------------------------------------------------------
    def step(self, o):
        op = o.op
        I, R = o.operands, o.res
        if op in ('fork', 'lazy_fork'):
            if not self.has(I[0]):
                return False
            x = self.ch[I[0]][0]
            f = False
            for k, r in enumerate(R):
                if not o.sent[k] and self.room(r):
                    self.push(r, x)
                    o.sent[k] = True
                    f = True
            if all(o.sent):
                self.pop(I[0])
                o.sent = [False] * len(R)
                f = True
            return f
        if op == 'source':
            if self.room(R[0]):
                self.push(R[0], 0)
                return True
            return False
        if op == 'sink':
            if self.has(I[0]):
                self.pop(I[0])
                return True
            return False
        if op == 'end':
            f = False
            for k, v in enumerate(I):
                if self.has(v):
                    x = self.pop(v)
                    self.ends[k].append(x)
                    f = True
            return f
        if op == 'handshake.ram':
            return False
        if op in ('br', 'merge'):
            if not self.room(R[0]):
                return False
            for v in I:
                if self.has(v):
                    self.push(R[0], self.pop(v))
                    return True
            return False
        if op == 'control_merge':
            if not (self.room(R[0]) and self.room(R[1])):
                return False
            for k, v in enumerate(I):
                if self.has(v):
                    self.push(R[0], self.pop(v))
                    self.push(R[1], k)
                    return True
            return False
        if op == 'mux':
            if not (self.has(I[0]) and self.room(R[0])):
                return False
            s = self.ch[I[0]][0]
            d = I[1 + s]
            if self.has(d):
                self.pop(I[0])
                self.push(R[0], self.pop(d))
                return True
            return False
        if op == 'cond_br':
            if not (self.has(I[0]) and self.has(I[1])):
                return False
            c = self.ch[I[0]][0]
            r = R[0] if c & 1 else R[1]
            if not self.room(r):
                return False
            self.pop(I[0])
            self.push(r, self.pop(I[1]))
            return True
        if op == 'constant':
            if self.has(I[0]) and self.room(R[0]):
                self.pop(I[0])
                self.push(R[0], o.val)
                return True
            return False
        if op == 'load':
            f = False
            if self.has(I[0]) and self.room(R[0]):
                self.push(R[0], self.pop(I[0]))
                f = True
            if self.has(I[1]) and self.room(R[1]):
                self.push(R[1], self.pop(I[1]))
                f = True
            return f
        if op == 'store':
            f = False
            if self.has(I[0]) and self.room(R[0]):
                self.push(R[0], self.pop(I[0]))
                f = True
            if self.has(I[1]) and self.room(R[1]):
                self.push(R[1], self.pop(I[1]))
                f = True
            return f
        if op == 'mem_controller':
            return self.step_mc(o)
        if op == 'lsq':
            return self.step_lsq(o)
        if op == 'select':
            if all(self.has(v) for v in I) and self.room(R[0]):
                c, t, e = (self.pop(v) for v in I)
                self.push(R[0], t if c & 1 else e)
                return True
            return False
        # arithmetic: all inputs, one output
        if not (all(self.has(v) for v in I) and self.room(R[0])):
            return False
        xs = [self.pop(v) for v in I]
        t = ints(o.tail)
        if op in ('extui', 'extsi', 'trunci'):
            a, b = t
            x = xs[0]
            y = mask(sgn(x, a), b) if op == 'extsi' else mask(x, min(a, b))
            self.push(R[0], y)
            return True
        w = t[0]
        a, b = (mask(x, w) for x in xs)
        if op == 'cmpi':
            p = o.pred
            sa, sb = sgn(a, w), sgn(b, w)
            r = {'eq': a == b, 'ne': a != b, 'ult': a < b, 'ule': a <= b, 'ugt': a > b, 'uge': a >= b,
                 'slt': sa < sb, 'sle': sa <= sb, 'sgt': sa > sb, 'sge': sa >= sb}[p]
            self.push(R[0], int(r))
            return True
        if op == 'addi':
            y = a + b
        elif op == 'subi':
            y = a - b
        elif op == 'muli':
            y = a * b
        elif op == 'andi':
            y = a & b
        elif op == 'ori':
            y = a | b
        elif op == 'xori':
            y = a ^ b
        elif op == 'shli':
            y = a << b if b < w else 0
        elif op == 'shrui':
            y = a >> b if b < w else 0
        elif op == 'shrsi':
            y = sgn(a, w) >> min(b, w - 1)
        elif op in ('divsi', 'remsi'):
            sa, sb = sgn(a, w), sgn(b, w)
            if sb == 0:
                y = 0
            else:
                q = abs(sa) // abs(sb) * (1 if (sa < 0) == (sb < 0) else -1)
                y = q if op == 'divsi' else sa - q * sb
        elif op in ('divui', 'remui'):
            y = 0 if b == 0 else (a // b if op == 'divui' else a % b)
        else:
            raise Unsupported(op)
        self.push(R[0], mask(y, w))
        return True

    def step_mc(self, o):
        f = False
        mem, w = self.mems[o.mem], self.memw[o.mem]
        if not o.started and self.has(o.start):
            self.pop(o.start)
            o.started = True
            f = True
        for kd in o.kinds:
            if kd[0] == 'ld':
                if self.has(kd[1]) and self.room(o.outs[kd[2]]):
                    a = self.pop(kd[1])
                    self.push(o.outs[kd[2]], mem[a] if a < len(mem) else 0)
                    if a >= len(mem):
                        self.oob += 1
                    f = True
            elif kd[0] == 'st':
                if self.has(kd[1]) and self.has(kd[2]):
                    a, d = self.pop(kd[1]), self.pop(kd[2])
                    if a < len(mem):
                        mem[a] = mask(d, w)
                    else:
                        self.oob += 1
                    f = True
            elif kd[0] == 'cnt':
                if self.has(kd[1]):
                    self.pop(kd[1])
                    f = True
        if self.has(o.endc) and self.room(o.memend):
            self.pop(o.endc)
            self.push(o.memend, 0)
            f = True
        return f

    def step_lsq(self, o):
        f = False
        mem, w = self.mems[o.mem], self.memw[o.mem]
        if not o.started and self.has(o.start):
            self.pop(o.start)
            o.started = True
            f = True
        for ctl, accs in o.glist:
            if self.has(ctl):
                self.pop(ctl)
                o.queue.extend(accs)
                f = True
        while o.queue:
            kd = o.queue[0]
            if kd[0] == 'ld':
                if self.has(kd[1]) and self.room(o.outs[kd[2]]):
                    a = self.pop(kd[1])
                    self.push(o.outs[kd[2]], mem[a] if a < len(mem) else 0)
                    if a >= len(mem):
                        self.oob += 1
                    o.queue.popleft()
                    f = True
                    continue
            else:
                if self.has(kd[1]) and self.has(kd[2]):
                    a, d = self.pop(kd[1]), self.pop(kd[2])
                    if a < len(mem):
                        mem[a] = mask(d, w)
                    else:
                        self.oob += 1
                    o.queue.popleft()
                    f = True
                    continue
            break
        if not o.queue and self.has(o.endc) and self.room(o.memend):
            self.pop(o.endc)
            self.push(o.memend, 0)
            f = True
        return f

    # -- a run ---------------------------------------------------------------
    def run(self, inputs, meminit, limit=5_000_000, seed=None):
        """inputs: {argname: int} for data args (control args get a token); meminit: {argname: [ints]}."""
        self.oob = 0
        for a, ty in self.args:
            if ty.startswith('memref'):
                self.mems[a] = [mask(x, self.memw[a]) for x in meminit[a]]
            elif ty.startswith('!handshake.channel'):
                w = int(re.search(r'<i(\d+)>', ty).group(1))
                self.push(a, mask(inputs[a], w))
            else:
                self.push(a, 0)
        endop = [o for o in self.ops if o.op == 'end'][0]
        self.ends = [[] for _ in endop.operands]
        order = list(self.ops)
        rng = random.Random(seed) if seed is not None else None
        steps = 0
        while True:
            if rng:
                rng.shuffle(order)
            fired = False
            for o in order:
                if self.step(o):
                    fired = True
                    steps += 1
            if not fired:
                status = 'quiesced'
                break
            if steps > limit:
                status = 'LIMIT'
                break
        return dict(status=status, ends=[(e[0] if e else None, len(e)) for e in self.ends],
                    mems={k: list(v) for k, v in self.mems.items()}, oob=self.oob, steps=steps)
