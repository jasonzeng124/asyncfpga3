#!/usr/bin/env python3
"""inc_cmp.py IN.mlir OUT.mlir [--log LOG] -- move a loop test off the incremented counter.

Pattern (Dynamatic handshake MLIR, one op per line):

    E'  = extui  x : <i sw> to <i w>          (E reaches the add through zero or more forks)
    X   = addi  E, K : <i w>                   (K: a `constant` (through forks), either operand order)
    F:n = fork [n] X ...                       (X reaches the compare through one or more forks)
    B   = constant T {value = C : i w}         (through forks)
    R   = cmpi P, F#j, B : <i w>

Rewrite:  R = cmpi P, E, B'  with  B' = (C - k) mod 2^w, where E is now read through a new 2-way fork
(`forkincN`: output #0 to the addi, #1 to the cmpi), the fork output F#j is removed (a fork left with one output is
deleted and its remaining reader reads X directly), and B' is written into B's constant in place when the compare was
B's only reader, else a fresh `sourceincN` + `constantincN` is created and B's fork output removed.

Applied ONLY when exact for every value E can carry (semantics of formal/lean/Formal/Net/GcdHwLib.lean, Ops: values
are Nat, addi w a b = (a+b) % 2^w, extui sw a = a % 2^sw, cmpi compares operands mod 2^w):

  P = ult or ule, X on the left:  k = K mod 2^w >= 1, E traced (through forks) to an `extui` from <i sw> to <i w>
      with 2^sw - 1 + k < 2^w (the add never wraps for any v < 2^sw), and C mod 2^w >= k.
      Then ult(v+k, C) = ult(v, C-k) and ule(v+k, C) = ule(v, C-k) for every v < 2^sw.
  Bound constant: changed in place when the compare is its only reader (whatever fires it); when it has other
  readers (through a fork) a new `source`-fired constant is made ONLY if the old one is itself fired by a `source`;
  a control-fired bound with other readers is refused.
  P = eq or ne, X on either side:  always exact ((v+k) = C  (mod 2^w)  iff  v = C-k  (mod 2^w)); no other condition.

Every other match of `cmpi P, (addi i, K) via forks, b` is skipped and the reason logged.  As a belt-and-braces check
the tool also evaluates both sides of the identity for every v < 2^sw (ult/ule, when 2^sw <= 2^20) or every v < 2^w
(eq/ne, when w <= 20) and refuses if any disagrees.  OUT is byte-identical to IN when nothing applies.
"""
import argparse
import collections
import re
import sys

OPRE = re.compile(r'^(?P<ind>\s*)(?P<res>%[\w]+(?::\d+)?(?:\s*,\s*%[\w]+(?::\d+)?)*)\s*=\s*(?P<op>"?[\w.]+"?)\s*(?P<rest>.*)$')
VALRE = re.compile(r'%[\w]+(?:#\d+)?')


def vre(v):
    """regex matching exactly the SSA use `v` (not a longer name, not another fork output)."""
    return re.compile(re.escape(v) + (r'(?!\d)' if '#' in v else r'(?![\w#])'))


class Op:
    pass


def parse(lines):
    ops, defs = [], {}
    uses = collections.defaultdict(list)   # value -> [line index]
    for li, ln in enumerate(lines):
        m = OPRE.match(ln)
        body = ln
        if m:
            o = Op()
            o.li, o.op, o.rest = li, m.group('op'), m.group('rest')
            o.res = [r.strip() for r in m.group('res').split(',')]
            nm = re.search(r'handshake.name = "([^"]+)"', o.rest)
            o.name = nm.group(1) if nm else '?'
            bb = re.search(r'handshake.bb = (\d+) : ui32', o.rest)
            o.bb = bb.group(1) if bb else None
            args = o.rest.split('{')[0]
            o.pred = None
            if o.op == 'cmpi':
                o.pred, args = [s.strip() for s in args.split(',', 1)]
            o.operands = VALRE.findall(args)
            val = re.search(r'value = (-?\d+|true|false) : i(\d+)', o.rest)
            o.value = None
            if val:
                o.value = {'true': 1, 'false': 0}.get(val.group(1), None)
                if o.value is None:
                    o.value = int(val.group(1))
            ty = re.search(r':\s*(?:<>,\s*)?<i(\d+)>\s*(?:to\s*<i(\d+)>)?\s*$', ln.rstrip())
            o.tw = (int(ty.group(1)), int(ty.group(2)) if ty.group(2) else None) if ty else (None, None)
            o.nout = None
            for r in o.res:
                if ':' in r:
                    base, n = r.split(':')
                    o.nout = int(n)
                    for k in range(int(n)):
                        defs[f'{base}#{k}'] = o
                    defs[base] = o
                else:
                    defs[r] = o
            ops.append(o)
            body = ln[m.start('rest'):]
        for v in VALRE.findall(body):
            uses[v].append(li)
    return ops, defs, uses


def through_forks(defs, v):
    """follow v up through plain forks; return (value, op) where op is the first non-fork producer (or None)."""
    o = defs.get(v)
    while o is not None and o.op == 'fork':
        v = o.operands[0]
        o = defs.get(v)
    return v, o


def sfmt(c, w):
    """print a w-bit constant the way MLIR does (signed decimal; i1 as true/false)."""
    c %= 1 << w
    if w == 1:
        return 'true' if c else 'false'
    return str(c - (1 << w) if c >= 1 << (w - 1) else c)


def pred_eval(p, a, b, w):
    a %= 1 << w
    b %= 1 << w
    return {'ult': a < b, 'ule': a <= b, 'eq': a == b, 'ne': a != b}[p]


class Refuse(Exception):
    pass


def analyse(ops, defs, uses, cmp):
    """return a plan dict for an exact rewrite of `cmp`, raise Refuse(reason), or return None (no addi+const match)."""
    found = None
    for side in (0, 1):
        a = cmp.operands[side]
        av, add = through_forks(defs, a)
        if add is None or add.op not in ('addi', 'subi'):
            continue
        for s2 in (0, 1):
            kv, kop = through_forks(defs, add.operands[s2])
            if kop is not None and kop.op == 'constant' and kop.value is not None:
                found = (side, a, add, s2, kop)
                break
        if found:
            break
    if not found:
        return None
    side, a, add, s2, kop = found
    p = cmp.pred
    if add.op == 'subi':
        raise Refuse(f'subi counter ({add.name})')
    w = add.tw[0]
    if cmp.tw[0] != w or w is None:
        raise Refuse(f'width mismatch cmpi i{cmp.tw[0]} vs addi i{w}')
    if p not in ('ult', 'ule', 'eq', 'ne'):
        raise Refuse(f'predicate {p} (only ult/ule/eq/ne handled)')
    if p in ('ult', 'ule') and side != 0:
        raise Refuse(f'{p} with the add on the right-hand side')
    k = kop.value % (1 << w)
    E = add.operands[1 - s2]
    b = cmp.operands[1 - side]
    bv, bop = through_forks(defs, b)
    if bop is None or bop.op != 'constant' or bop.value is None:
        raise Refuse(f'bound is not a constant (it is {bop.op if bop else "a function argument"})')
    if bop.tw[0] != w:
        raise Refuse(f'bound constant width i{bop.tw[0]} != i{w}')
    C = bop.value % (1 << w)
    if p in ('ult', 'ule'):
        if not 1 <= k:
            raise Refuse(f'increment k = {k} (mod 2^{w}) < 1')
        ev, eop = through_forks(defs, E)
        if eop is None or eop.op != 'extui':
            raise Refuse(f'counter operand is not an extui (it is {eop.op if eop else "a function argument"})')
        sw, tw = eop.tw
        if tw != w:
            raise Refuse(f'extui target width i{tw} != i{w}')
        if not (sw < w and (1 << sw) - 1 + k < (1 << w)):
            raise Refuse(f'add may wrap: sw={sw}, k={k}, w={w}')
        if not C >= k:
            raise Refuse(f'bound C = {C} < k = {k} (mod 2^{w})')
        if sw <= 20:
            for v in range(1 << sw):
                if pred_eval(p, v + k, C, w) != pred_eval(p, v, C - k, w):
                    raise Refuse(f'brute-force mismatch at v={v} (internal error)')
    else:
        if w <= 20:
            for v in range(1 << w):
                lhs = pred_eval(p, v + k, C, w) if side == 0 else pred_eval(p, C, v + k, w)
                rhs = pred_eval(p, v, C - k, w) if side == 0 else pred_eval(p, C - k, v, w)
                if lhs != rhs:
                    raise Refuse(f'brute-force mismatch at v={v} (internal error)')
    F = defs.get(a)
    trig = defs.get(bop.operands[0]) if bop.operands else None
    bsrc = trig is not None and trig.op == 'source'
    if b not in bop.res and (defs.get(b) is None or defs[b].op != 'fork' or '#' not in b):
        raise Refuse(f'bound {b} is not a constant result nor a fork output')
    if b not in bop.res and not bsrc:
        raise Refuse(f'bound constant {bop.name} is fired by a control token and has other readers '
                     f'(only an in-place value change is allowed for a control-fired bound)')
    if F is add:
        raise Refuse('the compare is the add result\'s only reader (no fork to drop)')
    if F.op != 'fork':
        raise Refuse(f'compare reads the add through a {F.op}')
    for v in (a, E, b):
        if len(uses.get(v, [])) != 1:
            raise Refuse(f'value {v} has {len(uses.get(v, []))} uses (expected 1)')
    return dict(bsrc=bsrc, side=side, a=a, add=add, E=E, b=b, bop=bop, C=C, k=k, w=w, p=p, newC=(C - k) % (1 << w))


def fresh(existing_text, stem):
    n = 0
    while re.search(r'%' + stem + str(n) + r'(?![\w])', existing_text) or f'"{stem}{n}"' in existing_text:
        n += 1
    return f'{stem}{n}'


def sub_use(lines, li, old, new):
    """replace the single use `old` on line li (after the '=' if the line defines values) by `new`."""
    ln = lines[li]
    m = OPRE.match(ln)
    start = m.start('rest') if m else 0
    head, body = ln[:start], ln[start:]
    body2, n = vre(old).subn(new, body)
    if n != 1:
        raise RuntimeError(f'expected one use of {old} on line {li + 1}, found {n}')
    lines[li] = head + body2


def drop_fork_output(lines, defs, uses, v):
    """the use of fork output `v` (= F#j) has already been redirected; remove output j from F."""
    F = defs[v]
    base, j = v.split('#')
    j = int(j)
    n = F.nout
    if n == 2:
        other = f'{base}#{1 - j}'
        for li in uses.get(other, []):
            sub_use(lines, li, other, F.operands[0])
        lines[F.li] = None
    else:
        ln = lines[F.li]
        ln2 = re.sub(re.escape(base) + r':\d+\s*=\s*fork \[\d+\]', f'{base}:{n - 1} = fork [{n - 1}]', ln, count=1)
        if ln2 == ln:
            raise RuntimeError(f'cannot rewrite fork line {F.li + 1}')
        lines[F.li] = ln2
        for m_ in range(j + 1, n):
            for li in uses.get(f'{base}#{m_}', []):
                sub_use(lines, li, f'{base}#{m_}', f'{base}#{m_ - 1}')


def apply(lines, ops, defs, uses, pl, text):
    """mutate `lines` (list of str or None; extra lines inserted as list entries joined later)."""
    add, w = pl['add'], pl['w']
    cmp = pl['cmp']
    ind = re.match(r'\s*', lines[add.li]).group(0)
    fk = fresh(text, 'forkinc')
    bbattr = f'handshake.bb = {add.bb} : ui32, ' if add.bb is not None else ''
    newfork = f'{ind}%{fk}:2 = fork [2] {pl["E"]} {{{bbattr}handshake.name = "{fk}"}} : <i{w}>\n'
    sub_use(lines, add.li, pl['E'], f'%{fk}#0')
    sub_use(lines, cmp.li, pl['a'], f'%{fk}#1')
    drop_fork_output(lines, defs, uses, pl['a'])
    extra = {add.li: [newfork]}
    bop = pl['bop']
    note = ''
    if pl['b'] in bop.res:          # the compare reads the constant directly: it is the constant's only reader
        ln = lines[bop.li]
        ln2, n = re.subn(r'value = (-?\d+|true|false) : i' + str(w), f'value = {sfmt(pl["newC"], w)} : i{w}', ln)
        if n != 1:
            raise RuntimeError('cannot rewrite constant value')
        lines[bop.li] = ln2
        note = (f'{bop.name} value {sfmt(pl["C"], w)} -> {sfmt(pl["newC"], w)} in place '
                f'[bound fired by {"source" if pl["bsrc"] else "control"}]')
    else:
        text2 = text + newfork
        sr = fresh(text2, 'sourceinc')
        cn = fresh(text2, 'constantinc')
        bb = f'handshake.bb = {bop.bb} : ui32, ' if bop.bb is not None else ''
        bind = re.match(r'\s*', lines[bop.li]).group(0)
        newsrc = f'{bind}%{sr} = source {{{bb}handshake.name = "{sr}"}} : <>\n'
        newcst = (f'{bind}%{cn} = constant %{sr} {{{bb}handshake.name = "{cn}", value = {sfmt(pl["newC"], w)} : i{w}}}'
                  f' : <>, <i{w}>\n')
        sub_use(lines, cmp.li, pl['b'], f'%{cn}')
        drop_fork_output(lines, defs, uses, pl['b'])
        extra.setdefault(bop.li, []).extend([newsrc, newcst])
        note = f'new {sr}+{cn} value {sfmt(pl["newC"], w)} (bound {bop.name} = {sfmt(pl["C"], w)} has other readers)'
    return extra, note, fk


def run(text):
    log = []
    done = set()
    napplied = 0
    while True:
        lines = text.splitlines(keepends=True)
        ops, defs, uses = parse(lines)
        progressed = False
        for cmp in ops:
            if cmp.op != 'cmpi' or cmp.name in done:
                continue
            try:
                pl = analyse(ops, defs, uses, cmp)
            except Refuse as e:
                done.add(cmp.name)
                log.append(f'SKIP  {cmp.name}: cmpi {cmp.pred} -- {e}')
                continue
            done.add(cmp.name)
            if pl is None:
                continue
            pl['cmp'] = cmp
            new = list(lines)
            extra, note, fk = apply(new, ops, defs, uses, pl, text)
            out = []
            for i, ln in enumerate(new):
                out.extend(extra.get(i, []))
                if ln is not None:
                    out.append(ln)
            text = ''.join(out)
            napplied += 1
            log.append(f'APPLY {cmp.name}: cmpi {pl["p"]} (addi {pl["add"].name} +{pl["k"]}, i{pl["w"]}), '
                       f'{pl["a"]} -> %{fk}#1 [{pl["E"]} before the add]; {note}')
            progressed = True
            break
        if not progressed:
            return text, napplied, log


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('inp')
    ap.add_argument('out')
    ap.add_argument('--log')
    a = ap.parse_args()
    src = open(a.inp).read()
    text, n, log = run(src)
    if n == 0:
        text = src
    with open(a.out, 'w') as f:
        f.write(text)
    msg = '\n'.join(log + [f'{a.inp}: {n} applied, {sum(1 for l in log if l.startswith("SKIP"))} skipped'])
    if a.log:
        with open(a.log, 'w') as f:
            f.write(msg + '\n')
    else:
        print(msg)
    return 0


if __name__ == '__main__':
    sys.exit(main())
