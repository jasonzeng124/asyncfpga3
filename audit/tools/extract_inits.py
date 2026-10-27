#!/usr/bin/env python3
"""Independent INIT / pin-map transcription audit: RTL (Verilog) vs Lean.

Run:  python3 -I extract_inits.py [--rtl DIR] [--rtl2 DIR] [--lean DIR ...] [--json OUT]

Own extraction, nothing imported from the audited branches.
  * RTL: every LUT1..LUT6 / LUT6_2 instance (INIT may be a literal or a
    localparam / ternary over parameters -> set of possible values), its
    .I0..I5 / .O / .O5 / .O6 connections, the enclosing module.
  * Lean: every INIT-like constant (def X : Nat := 0x..., def x : Lut k :=
    <0x..#n>, inline `initTbl 0x..`, `Nat.testBit 0x..`), and every use site
    lutB/lutK/o5B/o6B/o5K/o6K INIT [pins], `.gate INIT [pins]`,
    `Gate INIT [(sig,lo,hi),...]`, `X.eval (bvec [pins] k)` / `.keval (kvec ..)`
    and wrapper defs `exc init a b q r` style.
  * Match each Lean constant/use to RTL instances by INIT value (or by the
    function the narrowed table computes when Lean uses a sub-table, e.g. LUT4
    0x00E8 for a LUT6 with I4=I5=0), then compare the pin list position by
    position: constants exactly; a Lean constant on a live RTL pin is a
    SPECIALISATION (reported with the pin's net); a Lean variable on an RTL
    constant is a GENERALISATION, accepted only if the LUT function is
    independent of that pin given the RTL constants (checked here by
    enumeration); variable vs net names are reported for review.
  * Independently evaluates truth tables of every RTL INIT under its pin map
    and checks them against (a) the RTL header-comment equations and (b) the
    Lean-claimed equations, both transcribed by hand below as Python lambdas.
"""
import argparse
import itertools
import json
import os
import re
import sys

# --------------------------------------------------------------------------
# Verilog
# --------------------------------------------------------------------------

def strip_vcomments(s):
    s = re.sub(r'/\*.*?\*/', ' ', s, flags=re.S)
    s = re.sub(r'//[^\n]*', '', s)
    return s


def vlit(tok):
    """Verilog number literal -> int (or None)."""
    tok = tok.strip()
    m = re.fullmatch(r"(\d+)?'([hHbBdD])([0-9A-Fa-f_xXzZ]+)", tok)
    if m:
        base = {'h': 16, 'b': 2, 'd': 10}[m.group(2).lower()]
        return int(m.group(3).replace('_', ''), base)
    if re.fullmatch(r'\d+', tok):
        return int(tok)
    return None


def eval_init_expr(expr, lparams):
    """Return sorted list of possible INIT values for an INIT expression."""
    expr = expr.strip()
    v = vlit(expr)
    if v is not None:
        return [v]
    if expr in lparams:
        return eval_init_expr(lparams[expr], lparams)
    m = re.fullmatch(r'(.+?)\?(.+):(.+)', expr, flags=re.S)
    if m:
        return sorted(set(eval_init_expr(m.group(2), lparams) +
                          eval_init_expr(m.group(3), lparams)))
    raise ValueError('cannot evaluate INIT expression %r' % expr)


LUT_RE = re.compile(
    r'(LUT[1-6](?:_2)?)\s*#\s*\(\s*\.INIT\s*\(\s*(.*?)\s*\)\s*\)\s*(\w+)\s*\((.*?)\)\s*;',
    re.S)
PIN_RE = re.compile(r'\.(\w+)\s*\(\s*([^()]*?)\s*\)')
MOD_RE = re.compile(r'\bmodule\s+(\w+)(.*?)\bendmodule\b', re.S)
LP_RE = re.compile(r'localparam\s*(?:\[[^\]]*\])?\s*(\w+)\s*=\s*(.*?);', re.S)


def parse_rtl(rtl_dir):
    insts = []
    for fn in sorted(os.listdir(rtl_dir)):
        if not fn.endswith('.v'):
            continue
        raw = open(os.path.join(rtl_dir, fn)).read()
        src = strip_vcomments(raw)
        for mm in MOD_RE.finditer(src):
            mod, body = mm.group(1), mm.group(2)
            lparams = {k: v for k, v in LP_RE.findall(body)}
            for li in LUT_RE.finditer(body):
                prim, init_expr, name, conns = li.groups()
                pins = dict(PIN_RE.findall(conns))
                # line number in raw file
                off = mm.start(2) + li.start()
                # map offset in stripped text back approximately: search raw
                line = None
                key = re.escape(name) + r'\s*\('
                for k, l in enumerate(raw.splitlines(), 1):
                    if re.search(r'\b' + prim + r'\b', l) and re.search(r'\b' + key, l) \
                            and k not in [i['line'] for i in insts if i['file'] == fn]:
                        line = k
                        break
                vals = eval_init_expr(init_expr, lparams)
                nin = 6 if prim == 'LUT6_2' else int(prim[3])
                insts.append(dict(file=fn, line=line, module=mod, prim=prim,
                                  name=name, init_expr=init_expr, inits=vals,
                                  nin=nin,
                                  ins=[norm_v(pins.get('I%d' % i, '?')) for i in range(nin)],
                                  out={k: norm_v(pins[k]) for k in ('O', 'O5', 'O6') if k in pins}))
    return insts


def norm_v(net):
    net = net.strip()
    if net in ("1'b0", "1'd0", "0"):
        return 0
    if net in ("1'b1", "1'd1", "1"):
        return 1
    net = re.sub(r'\[(.*?)\]', lambda m: '[' + m.group(1).replace(' ', '') + ']', net)
    return net

# --------------------------------------------------------------------------
# Lean
# --------------------------------------------------------------------------

def strip_lean_comments(s):
    # block comments /- ... -/ (nestable), and -- line comments
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and s.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            out.append('\n' if s[i] == '\n' else ' '); i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
            continue
        out.append(s[i]); i += 1
    return ''.join(out)


def lean_int(tok):
    tok = tok.replace('_', '')
    return int(tok, 16) if tok.lower().startswith('0x') else int(tok)


def bracket(s, i):
    """s[i] == '['; return (content, end index) with nesting."""
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c in '[(':
            depth += 1
        elif c in '])':
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j
        j += 1
    raise ValueError('unbalanced')


def split_top(s):
    parts, depth, cur = [], 0, ''
    for c in s:
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        if c == ',' and depth == 0:
            parts.append(cur.strip()); cur = ''
        else:
            cur += c
    if cur.strip():
        parts.append(cur.strip())
    return parts


def norm_l(e):
    """Normalise a Lean pin expression to 0/1 or a signal name."""
    e = ' '.join(e.split())
    if e in ('false', '.f', 'f', '.const false', 'K3.f', 'zero', '.zero', 'K3.zero',
             'winK zero 0 0 t'):
        return 0
    if e in ('true', '.t', 't', '.const true', 'K3.t', 'one', '.one', 'K3.one',
             'winK one 0 0 t'):
        return 1
    m = re.fullmatch(r'\(([^,()]+), *\w+, *\w+\)', e)      # Gate tuple (sig, lo, hi)
    if m:
        return norm_l(m.group(1))
    if e in ('s 0',):
        return 's[0]'
    if e in ('s i',):
        return 's[i]'
    if e in ('.x', 'X', 'K3.x', '.X'):
        return 'X'
    if e == '(if broad then ack else false)':
        return 'gate'
    if e == '(if L ≤ t then q (t - L) else q t)':
        return 'q'
    m = re.fullmatch(r'ofTern \((\w) (\d|\(\))\)', e)
    if m:
        return 'tern_%s%s' % (m.group(1), m.group(2).strip('()'))
    m = re.fullmatch(r'ofBool \(?(!?\w+)\)?', e)
    if m:
        return m.group(1)
    m = re.fullmatch(r'winK (\w+) \S+ \S+ t', e)
    if m:
        return norm_l(m.group(1))
    m = re.fullmatch(r'K3\.ofBool \(?(\w+)\)?', e)
    if m:
        return m.group(1)
    m = re.fullmatch(r'(\w+) \(t - \d+\)', e)
    if m:
        return m.group(1)
    m = re.fullmatch(r'(\w+) t', e)
    if m:
        return m.group(1)
    m = re.fullmatch(r's\.(\w+)', e)
    if m:
        return m.group(1)
    m = re.fullmatch(r'\.node (\d+)', e)
    if m:
        return 'node' + m.group(1)
    return e


CALL_RE = re.compile(
    r'(?<![\w.])(lutB|lutK|o5B|o6B|o5K|o6K|\.gate|Node\.gate|Gate)\s+'
    r'(\(\s*[\w.]+\s*%\s*2\s*\^\s*32\s*\)|[\w.]+)\s*(?=\[)')
EVAL_RE = re.compile(
    r'\b((?:Init\.)?(\w+))(\.o5|\.o6)?\.(k?eval)\s*\(\s*(bvec|kvec)\s*(?=\[)')
DEF_NAT_RE = re.compile(r'\bdef\s+(\w+)\s*:\s*Nat\s*:=\s*(0x[0-9A-Fa-f_]+)')
DEF_LUT_RE = re.compile(r'\bdef\s+(\w+)\s*:\s*(Lut\s*\d|Lut62)\s*:=\s*⟨\s*(0x[0-9A-Fa-f_]+)#(\d+)\s*⟩')
INLINE_RE = re.compile(r'(initTbl|Nat\.testBit)\s+(0x[0-9A-Fa-f_]+)')


def parse_lean(dirs):
    consts, uses = [], []
    for root_dir in dirs:
        for root, _, files in os.walk(root_dir):
            for fn in sorted(files):
                if not fn.endswith('.lean'):
                    continue
                path = os.path.join(root, fn)
                rel = os.path.relpath(path, os.path.dirname(root_dir.rstrip('/')))
                raw = open(path).read()
                src = strip_lean_comments(raw)
                lines_at = lambda off: src.count('\n', 0, off) + 1
                local = {}
                for m in DEF_NAT_RE.finditer(src):
                    v = lean_int(m.group(2))
                    local[m.group(1)] = (v, None)
                    consts.append(dict(file=rel, line=lines_at(m.start()), name=m.group(1),
                                       value=v, width=None, kind='Nat'))
                for m in DEF_LUT_RE.finditer(src):
                    v = lean_int(m.group(3))
                    local[m.group(1)] = (v, m.group(2).replace(' ', ''))
                    consts.append(dict(file=rel, line=lines_at(m.start()), name=m.group(1),
                                       value=v, width=int(m.group(4)), kind=m.group(2).replace(' ', '')))
                for m in INLINE_RE.finditer(src):
                    v = lean_int(m.group(2))
                    consts.append(dict(file=rel, line=lines_at(m.start()), name='<inline %s>' % m.group(1),
                                       value=v, width=None, kind='inline'))
                for m in CALL_RE.finditer(src):
                    fnname, initname = m.group(1), m.group(2)
                    low32 = '%' in initname
                    iname = re.sub(r'[()\s]|%.*', '', initname)
                    content, _ = bracket(src, m.end())
                    pins = [norm_l(p) for p in split_top(content)]
                    out = {'o5B': 'O5', 'o5K': 'O5', 'o6B': 'O6', 'o6K': 'O6'}.get(fnname, 'O')
                    if low32:
                        out = 'O5'
                    uses.append(dict(file=rel, line=lines_at(m.start()), fn=fnname, init=iname,
                                     out=out, pins=pins, raw=' '.join(content.split())))
                for m in EVAL_RE.finditer(src):
                    content, _ = bracket(src, m.end())
                    out = {'.o5': 'O5', '.o6': 'O6'}.get(m.group(3) or '', 'O')
                    uses.append(dict(file=rel, line=lines_at(m.start()), fn=m.group(4),
                                     init=m.group(2), out=out,
                                     pins=[norm_l(p) for p in split_top(content)],
                                     raw=' '.join(content.split())))
                for u in uses:
                    if u['file'] == rel and 'value' not in u:
                        key = u['init'].split('.')[-1]
                        if key in local:
                            u['value'] = local[key][0]
    # resolve cross-file references (ArbKleene.C2_INIT etc.)
    byname = {}
    for c in consts:
        byname.setdefault(c['name'], set()).add(c['value'])
    for u in uses:
        if 'value' not in u:
            key = u['init'].split('.')[-1]
            vs = byname.get(key)
            u['value'] = next(iter(vs)) if vs and len(vs) == 1 else None
    return consts, uses

# --------------------------------------------------------------------------
# truth tables
# --------------------------------------------------------------------------

def lut(init, bits):
    a = sum((1 << i) for i, b in enumerate(bits) if b)
    return (init >> a) & 1


def o5(init, bits):
    return lut(init & 0xFFFFFFFF, bits[:5])


def rtl_fn(inst, init, outpin):
    """Function of the instance as a callable over a dict of net values."""
    ins = inst['ins']
    def f(env):
        bits = [p if isinstance(p, int) else env[p] for p in ins]
        if inst['prim'] == 'LUT6_2' and outpin == 'O5':
            return o5(init, bits)
        return lut(init, bits)
    return f


def nets_of(inst):
    seen = []
    for p in inst['ins']:
        if not isinstance(p, int) and p not in seen:
            seen.append(p)
    return seen


def depends_on(inst, init, outpin, pos):
    """Does the output depend on input position pos, other RTL constants fixed?"""
    n = inst['nin']
    for bits in itertools.product([0, 1], repeat=n):
        if any(isinstance(inst['ins'][i], int) and bits[i] != inst['ins'][i]
               for i in range(n) if i != pos):
            continue
        b2 = list(bits); b2[pos] ^= 1
        f = (lambda b: o5(init, b)) if (inst['prim'] == 'LUT6_2' and outpin == 'O5') \
            else (lambda b: lut(init, b))
        if f(list(bits)) != f(b2):
            return True
    return False

# --------------------------------------------------------------------------
# Hand transcription of claims (independent of the Lean source text)
# --------------------------------------------------------------------------

maj = lambda a, b, c: int((a and b) or (a and c) or (b and c))
mux = lambda s, x0, x1: x1 if s else x0     # s ? x1 : x0
C3 = lambda a, b, c, q: int((a and b and c) or (q and (a or b or c)))
C4 = lambda a, b, c, d, q: int((a and b and c and d) or (q and (a or b or c or d)))

# (module, instance, outpin) -> list of (source, description, fn(env)->bit)
CLAIMS = {
    ('bd_c2', 'u', 'O'): [
        ('RTL hdr', 'q = ~rst . C(a,b)', lambda e: int(not e['rst'] and maj(e['a'], e['b'], e['q']))),
        ('Lean', 'Init.bd_c2_eval / CElemFn c2: !r && maj a b q',
         lambda e: int(not e['rst'] and maj(e['a'], e['b'], e['q'])))],
    ('bd_c2_set', 'u', 'O'): [
        ('RTL hdr', 'q = rst + C(a,b)', lambda e: int(e['rst'] or maj(e['a'], e['b'], e['q']))),
        ('Lean', 'r || maj a b q', lambda e: int(e['rst'] or maj(e['a'], e['b'], e['q'])))],
    ('bd_c2n', 'u', 'O'): [
        ('RTL hdr', 'q = ~rst . C(a,~b); SR: set a.~b, reset ~a.b, hold on tie',
         lambda e: 0 if e['rst'] else (1 if (e['a'] and not e['b']) else (0 if (not e['a'] and e['b']) else e['q']))),
        ('Lean', '!r && maj a (!b) q', lambda e: int(not e['rst'] and maj(e['a'], 1 - e['b'], e['q'])))],
    ('bd_c2n_set', 'u', 'O'): [
        ('RTL hdr', 'q = rst + C(a,~b)', lambda e: int(e['rst'] or maj(e['a'], 1 - e['b'], e['q']))),
        ('Lean', 'r || maj a (!b) q', lambda e: int(e['rst'] or maj(e['a'], 1 - e['b'], e['q'])))],
    ('bd_c3', 'u', 'O'): [
        ('RTL hdr', 'q = ~rst . C(a,b,c)', lambda e: int(not e['rst'] and C3(e['a'], e['b'], e['c'], e['q']))),
        ('Lean', '!r && (abc || q(a+b+c))', lambda e: int(not e['rst'] and C3(e['a'], e['b'], e['c'], e['q'])))],
    ('bd_c4', 'u', 'O'): [
        ('RTL hdr', 'q = ~rst . C(a,b,c,d)', lambda e: int(not e['rst'] and C4(e['a'], e['b'], e['c'], e['d'], e['q']))),
        ('Lean', '!r && (abcd || q(a+b+c+d))', lambda e: int(not e['rst'] and C4(e['a'], e['b'], e['c'], e['d'], e['q'])))],
    ('bd_c2_norst', 'u', 'O'): [
        ('RTL hdr', 'C(a,b)', lambda e: maj(e['a'], e['b'], e['q'])),
        ('Lean', 'maj a b q', lambda e: maj(e['a'], e['b'], e['q']))],
    ('bd_c3_norst', 'u', 'O'): [
        ('RTL hdr', 'C(a,b,c)', lambda e: C3(e['a'], e['b'], e['c'], e['q'])),
        ('Lean', 'abc || q(a+b+c)', lambda e: C3(e['a'], e['b'], e['c'], e['q']))],
    ('bd_arbcell', 'ugrant', 'O5'): [
        ('RTL hdr', 'g1 = r1.q', lambda e: int(e['r1'] and e['q'])),
        ('Lean', 'r1 && q', lambda e: int(e['r1'] and e['q']))],
    ('bd_arbcell', 'ugrant', 'O6'): [
        ('RTL hdr', 'g2 = r2.~q', lambda e: int(e['r2'] and not e['q'])),
        ('Lean', 'r2 && !q', lambda e: int(e['r2'] and not e['q']))],
    ('bd_arbiter', 'ugrant', 'O5'): [
        ('RTL hdr', 'g1 = r1.q', lambda e: int(e['r1'] and e['q'])),
        ('Lean', 'r1 && q', lambda e: int(e['r1'] and e['q']))],
    ('bd_arbiter', 'ugrant', 'O6'): [
        ('RTL hdr', 'g2 = r2.~q', lambda e: int(e['r2'] and not e['q'])),
        ('Lean', 'r2 && !q', lambda e: int(e['r2'] and not e['q']))],
    ('bd_arbiter', 'ustate', 'O6'): [
        ('RTL hdr (inline)', 'q = rst + C(r1,~r2), additionally frozen while A0 high',
         lambda e: int(e['rst'] or (e['q'] if e['A0'] else maj(e['r1'], 1 - e['r2'], e['q'])))),
        ('Lean', 'rst || (if a0 then q else maj r1 (!r2) q)',
         lambda e: int(e['rst'] or (e['q'] if e['A0'] else maj(e['r1'], 1 - e['r2'], e['q']))))],
    ('bd_arbiter', 'ustate', 'O5'): [
        ('RTL hdr', 'R0 = r1.q + r2.~q', lambda e: int((e['r1'] and e['q']) or (e['r2'] and not e['q']))),
        ('Lean', '(r1 && q) || (r2 && !q)', lambda e: int((e['r1'] and e['q']) or (e['r2'] and not e['q'])))],
    ('bd_latch', 'u', 'O5'): [
        ('RTL hdr', 'q[i] = en ? d[i] : q[i]', lambda e: mux(e['en'], e['q[i]'], e['d[i]'])),
        ('Lean', 'if en then di else qi', lambda e: mux(e['en'], e['q[i]'], e['d[i]']))],
    ('bd_latch', 'u', 'O6'): [
        ('RTL hdr', 'q[i+1] = en ? d[i+1] : q[i+1]', lambda e: mux(e['en'], e['q[i+1]'], e['d[i+1]'])),
        ('Lean', 'if en then dj else qj', lambda e: mux(e['en'], e['q[i+1]'], e['d[i+1]']))],
    ('bd_latch', 'u', 'O'): [
        ('RTL hdr', 'q = en ? d : q', lambda e: mux(e['en'], e['q[W-1]'], e['d[W-1]'])),
        ('Lean', 'if en then d else q', lambda e: mux(e['en'], e['q[W-1]'], e['d[W-1]']))],
    ('bd_latch_rst', 'u', 'O'): [   # checked per INIT alternative below
    ],
    ('bd_delay', 'u', 'O'): [],
    ('bd_link_dctl', 'ub', 'O'): [
        ('RTL hdr', 'b: set req_in.ld.~ack_out, reset ack_out.~ld, rst clears',
         lambda e: 0 if e['rst'] else (1 if (e['req_in'] and e['ld'] and not e['ack_out'])
                                       else (0 if (e['ack_out'] and not e['ld']) else e['b']))),
        ('Lean', '(req && ld && !ack || b && !(ack && !ld)) [rst=0]',
         lambda e: int(e['req_in'] and e['ld'] and not e['ack_out'] or e['b'] and not (e['ack_out'] and not e['ld'])),
         lambda e: e['rst'] == 0)],
    ('bd_link_dctl', 'ua', 'O'): [
        ('RTL hdr', 'a: set req_in.b.ld, reset ~req_in.~ld',
         lambda e: 0 if e['rst'] else (1 if (e['req_in'] and e['b'] and e['ld'])
                                       else (0 if (not e['req_in'] and not e['ld']) else e['a']))),
        ('Lean', '(req && b && ld || a && !(!req && !ld)) [rst=0]',
         lambda e: int(e['req_in'] and e['b'] and e['ld'] or e['a'] and not (not e['req_in'] and not e['ld'])),
         lambda e: e['rst'] == 0)],
    ('bd_link_dctl', 'uld', 'O'): [
        ('RTL hdr', 'ld: set lt.s.~a, reset a',
         lambda e: 0 if e['rst'] else (0 if e['a'] else (1 if (e['lt'] and e['s']) else e['ld']))),
        ('Lean', '(lt && !a || ld && !a) [s=1, rst=0]',
         lambda e: int(e['lt'] and not e['a'] or e['ld'] and not e['a']),
         lambda e: e['rst'] == 0 and e['s'] == 1)],
    ('bd_link_dctl', 'ult', 'O'): [
        ('RTL hdr', 'lt = ~b.~a.(~ack_out)  (gate = ack_out if BROAD else 0)',
         lambda e: int(not e['b'] and not e['a'] and not e['gate'])),
        ('Lean', '!b && !a && !ack', lambda e: int(not e['b'] and not e['a'] and not e['gate']))],
    # cells with no Lean counterpart: header check only
    ('bd_steer', 'u', 'O5'): [('RTL hdr', 'req0 = req.~s', lambda e: int(e['req'] and not e['s']))],
    ('bd_steer', 'u', 'O6'): [('RTL hdr', 'req1 = req.s', lambda e: int(e['req'] and e['s']))],
    ('bd_steer', 'uack', 'O'): [('RTL hdr', 'ack = ack0 + ack1', lambda e: int(e['ack0'] or e['ack1']))],
    ('bd_bd2dr', 'u', 'O5'): [('RTL hdr', 'f = req.~d', lambda e: int(e['req'] and not e['d']))],
    ('bd_bd2dr', 'u', 'O6'): [('RTL hdr', 't = req.d', lambda e: int(e['req'] and e['d']))],
    ('bd_dr2bd', 'u', 'O5'): [('RTL hdr', 'd = majority(t, ~f, d)', lambda e: maj(e['t'], 1 - e['f'], e['d']))],
    ('bd_dr2bd', 'u', 'O6'): [('RTL hdr', 'either = t + f', lambda e: int(e['t'] or e['f']))],
    ('bd_dr2bd', 'uor', 'O'): [('RTL hdr', 'either = t + f', lambda e: int(e['t'] or e['f']))],
    ('bd_src', 'u', 'O'): [('RTL hdr', 'req = ~ack', lambda e: int(not e['ack']))],
    ('bd_merge', 'uor', 'O'): [('RTL hdr', 'either = x_req + y_req', lambda e: int(e['x_req'] or e['y_req']))],
    ('bd_merge', 'usel', 'O'): [('RTL hdr', 'sel = x_req + x_ack', lambda e: int(e['x_req'] or e['x_ack']))],
    ('bd_mux', 'uor', 'O'): [('RTL hdr', 'either = j0 + j1', lambda e: int(e['j0'] or e['j1']))],
    ('bd_mux', 'uj0', 'O'): [('RTL hdr',
                              'j0 = ~rst . C(x_req, ctl_req.~s)',
                              lambda e: int(not e['rst'] and maj(e['x_req'], int(e['ctl_req'] and not e['s']), e['j0'])))],
    ('bd_mux', 'uj1', 'O'): [('RTL hdr',
                              'j1 = ~rst . C(y_req, ctl_req.s)',
                              lambda e: int(not e['rst'] and maj(e['y_req'], int(e['ctl_req'] and e['s']), e['j1'])))],
    ('bd_mlink_ctl', 'ux', 'O'): [('RTL hdr', 'en0 = rst | ~(done ^ ack)',
                                   lambda e: int(e['rst'] or not (e['done'] ^ e['ack'])))],
    ('bd_mlink_ctl', 'uz', 'O'): [('RTL hdr', 'en = s & (rst | ~(done ^ ack))',
                                   lambda e: int(e['s'] and (e['rst'] or not (e['done'] ^ e['ack']))))],
    ('bd_flink_ctl', 'uck', 'O'): [('RTL hdr', 'ck = ~rst & (done ^ ack)',
                                    lambda e: int(not e['rst'] and (e['done'] ^ e['ack'])))],
    ('bd_flink_ctl', 'uq', 'O'): [('RTL hdr', 'done = ck ? done : req_in',
                                   lambda e: mux(e['ck'], e['req_in'], e['done']))],
    ('bd_mem', 'ubuf', 'O'): [('RTL hdr', 'ram_clk = strobe (buffer)', lambda e: e['strobe'])],
    ('bd_datamux', 'u', 'O5'): [('RTL hdr', 'z[i] = s ? b[i] : a[i]', lambda e: mux(e['s'], e['a[i]'], e['b[i]']))],
    ('bd_datamux', 'u', 'O6'): [('RTL hdr', 'z[i+1] = s ? b[i+1] : a[i+1]', lambda e: mux(e['s'], e['a[i+1]'], e['b[i+1]']))],
    ('bd_datamux', 'u', 'O'): [('RTL hdr', 'z = s ? b : a', lambda e: mux(e['s'], e['a[W-1]'], e['b[W-1]']))],
}


def check_claims(insts):
    rows = []
    for inst in insts:
        nets = nets_of(inst)
        outs = list(inst['out'].keys())
        for outpin in outs:
            key = (inst['module'], inst['name'], outpin)
            for init in inst['inits']:
                claims = list(CLAIMS.get(key, []))
                # parameterised families
                if inst['module'] == 'bd_latch_rst':
                    rv = 1 if init == 0xFFB8FFB8FFB8FFB8 else 0
                    claims = [('RTL hdr', 'q = rst ? %d : (en ? d : q)  (RESET_VALUE bit=%d)' % (rv, rv),
                               (lambda rv: lambda e: rv if e['rst'] else mux(e['en'], e['q[i]'], e['d[i]']))(rv)),
                              ('Lean', 'latch_rst%d_eval' % rv,
                               (lambda rv: lambda e: rv if e['rst'] else mux(e['en'], e['q[i]'], e['d[i]']))(rv))]
                if inst['module'] in ('bd_delay', 'bd_delay_gated'):
                    if inst['prim'] == 'LUT1':
                        claims = [('RTL hdr', 'buffer', lambda e: e['s[i]'])]
                    else:
                        side = 'gate' if inst['module'] == 'bd_delay_gated' else 'a'
                        if init == 0x8:
                            claims = [('RTL hdr', 'AND with tap (FASTFALL)', (lambda sd: lambda e: int(e['s[i]'] and e[sd]))(side))]
                        else:
                            claims = [('RTL hdr', 'OR with tap (FASTRISE)', (lambda sd: lambda e: int(e['s[i]'] or e[sd]))(side))]
                f = rtl_fn(inst, init, outpin)
                for cl in claims:
                    src, desc, g = cl[:3]
                    pre = cl[3] if len(cl) > 3 else (lambda e: True)
                    if g is None:
                        continue
                    bad, nrows = [], 0
                    for vals in itertools.product([0, 1], repeat=len(nets)):
                        env = dict(zip(nets, vals))
                        if not pre(env):
                            continue
                        nrows += 1
                        if f(env) != g(env):
                            bad.append(env)
                    rows.append(dict(module=inst['module'], inst=inst['name'], out=outpin,
                                     init='%X' % init, source=src, claim=desc,
                                     ok=not bad, n=nrows,
                                     counterexample=bad[0] if bad else None))
                if not claims:
                    rows.append(dict(module=inst['module'], inst=inst['name'], out=outpin,
                                     init='%X' % init, source='-', claim='(no claim transcribed)',
                                     ok=None, n=0, counterexample=None))
    return rows

# --------------------------------------------------------------------------
# Lean <-> RTL matching
# --------------------------------------------------------------------------

# Lean variable name -> RTL net names it may legitimately stand for (roles).
ALIAS = {
    'req': {'req_in', 'a'}, 'cnext': {'c_next', 'b'}, 'ack': {'ack_out', 'gate'},
    'r': {'a', 'req_in', 'prev'}, 'a': {'a', 'prev', 'A0'}, 'b': {'b', 'next'},
    'rst': {'rst'}, 'r1': {'r1', 'a'}, 'r2': {'r2', 'b'}, 'q': {'q', 'c', 'A1', 'A2', 'q[W-1]'},
    'a0': {'A0'}, 'g1': {'g1', 'a'}, 'g2': {'g2', 'a'}, 'a1': {'A1', 'q'}, 'a2': {'A2', 'q'},
    'g': {'a', 'g1', 'g2'}, 'fb': {'q', 'A1', 'A2'},
    'd': {'d[W-1]', 'd[i]', 'd', 'a'}, 'en': {'en'}, 'di': {'d[i]'}, 'dj': {'d[i+1]'},
    'qi': {'q[i]'}, 'qj': {'q[i+1]'}, 'd0': {'d[i]'}, 'd1': {'d[i+1]'}, 'q0': {'q[i]'},
    'q1': {'q[i+1]'}, 'd2': {'d[i]', 'd[i+1]'}, 'q2': {'q[i]', 'q[i+1]'}, 'e': {'en'},
    'p': {'q[i]'}, 'p1': {'q[i+1]'}, 'v': None,
    'qp': {'q'}, 'qfb': {'q'}, 'u': None, 'w': None, 'c': {'c'}, 'ld': {'ld'}, 'lt': {'lt'},
    'k': {'s[i]'}, 'x': {'s[i]'}, 's1': {'s[i]'}, 'ffA': {'a', 's[i]'}, 'fgA': {'a', 's[i]'},
    'ffS1': {'s[i]'}, 'ffS2': {'s[i]'}, 'fgS1': {'s[i]'}, 'fgS2': {'s[i]'},
    'caD': {'d[W-1]'}, 'caEn': {'en'}, 'caQ': {'q[W-1]'},
    'cbD': {'d[W-1]'}, 'cbEn': {'en'}, 'cbQ': {'q[W-1]'},
    'bq': {'q'}, 'b1': {'g1'}, 'ba0': {'A0'}, 'ba1': {'A1'},
    'node0': {'r1', 'a'}, 'node1': {'r2', 'b'}, 'node2': {'A0', 'rst'}, 'node3': {'A0', 'q'},
    'node4': {'rst'}, 'node5': {'q'}, 'node6': {'g1'}, 'node7': {'g2'},
    'node9': {'A1'}, 'node10': {'A2'},
    'X': None,                      # Kleene X injected as a scenario value
    's[0]': {'a', 's[i]'},           # bd_delay: assign s[0] = a; g0 is stage i=0
    'gate': {'gate'}, 'ai': {'a[i]'}, 'bi': {'b[i]'}, 'aj': {'a[i+1]'}, 'bj': {'b[i+1]'},
    's': {'s[i]', 's'},
    'tern_u0': {'a'}, 'tern_u1': {'b'}, 'tern_t': {'q'}, 'tern_u2': {'rst'},
}
ALIAS['r'] = {'a', 'req_in', 'prev', 'rst'}
ALIAS['q'] = ALIAS['q'] | {'q[i]'}
ALIAS['a'] = ALIAS['a'] | {'a[W-1]', 's[i]'}
ALIAS['b'] = ALIAS['b'] | {'b[W-1]', 'a'}   # bd_delay side tap (Bundling ff_bin) is I1 = a

# Per-site overrides: (file basename, line) -> {lean name: allowed RTL nets} or 'FREE'
# (all variable names at that site are proof-local scenario variables; only the
# constants and the pin positions are checked).  Each is justified in the report.
CONTEXT = {
    ('ArbA0Fork.lean', 83): {'g': {'a'}, 'a': {'b'}, 'fb': {'q'}},        # cel g a fb = C(g, A0) ack
    ('ArbHeldTimed.lean', 62): {'g': {'a'}, 'a': {'b'}, 'fb': {'q'}},
    ('ArbHandover.lean', 569): {'g1': {'a'}, 'a0': {'b'}, 'a1': {'q'}},   # bd_c2 ua1 (.a(g1),.b(A0),.q(A1))
    ('ArbHandover.lean', 570): {'g2': {'a'}, 'a0': {'b'}, 'a2': {'q'}},
    ('ArbKleene.lean', 197): {'b1 && bq': {'a'}, 'ba0': {'b'}, 'ba1': {'q'}},  # g1 = r1.q composed in
    ('HandshakeMuller.lean', 50): {'r': {'a'}, 'a': {'b'}},               # celN r a q: a=req_in, b=ack_out
    # TernarySound arbNet: inputs 0 r1, 1 r2, 2 A0@ustate, 3 A0@acks, 4 rst; 5 q, 6 g1, 7 g2, 8 R0, 9 A1, 10 A2
    ('TernarySound.lean', 696): {'node6': {'a'}, 'node3': {'b'}, 'node9': {'q'}, 'node4': {'rst'}},
    ('TernarySound.lean', 697): {'node7': {'a'}, 'node3': {'b'}, 'node10': {'q'}, 'node4': {'rst'}},
    # TernaryPhases cNet: inputs 0 a, 1 b, 2 rst; gate 3 q
    ('TernaryPhases.lean', 816): {'node0': {'a'}, 'node1': {'b'}, 'node2': {'rst'}, 'node3': {'q'}},
    ('TernaryPhases.lean', 822): {'node0': {'a'}, 'node1': {'b'}, 'node2': {'rst'}, 'node3': {'q'}},
    ('ArbBinary.lean', 128): 'FREE', ('Latch.lean', 116): 'FREE', ('Latch.lean', 122): 'FREE',
    ('Latch.lean', 128): 'FREE', ('Latch.lean', 129): 'FREE', ('Latch.lean', 142): 'FREE',
    ('Latch.lean', 143): 'FREE', ('Lut.lean', 531): 'FREE', ('Lut.lean', 536): 'FREE',
}

# Lean INIT names that model a parameterised/specialised RTL instance on purpose.
INTENDED = {
    # name -> (module, instance) the Lean comments say it transcribes
    'INIT_C2N': ('bd_c2n', 'u'), 'INIT_c2n': ('bd_c2n', 'u'), 'bd_c2n': ('bd_c2n', 'u'),
    'INIT_c2': ('bd_c2', 'u'), 'INIT_C2': ('bd_c2', 'u'), 'C2_INIT': ('bd_c2', 'u'), 'C2': ('bd_c2', 'u'),
    'INIT_C2_RST': ('bd_c2', 'u'), 'bd_c2': ('bd_c2', 'u'),
    'INIT_c2_set': ('bd_c2_set', 'u'), 'bd_c2_set': ('bd_c2_set', 'u'),
    'INIT_c2n_set': ('bd_c2n_set', 'u'), 'INIT_C2N_SET': ('bd_c2n_set', 'u'), 'CS_INIT': ('bd_c2n_set', 'u'),
    'C2N_SET': ('bd_c2n_set', 'u'), 'bd_c2n_set': ('bd_c2n_set', 'u'), 'ARBCELL_INIT': ('bd_c2n_set', 'u'),
    'INIT_c3': ('bd_c3', 'u'), 'INIT_C3': ('bd_c3', 'u'), 'bd_c3': ('bd_c3', 'u'),
    'INIT_c4': ('bd_c4', 'u'), 'INIT_C4': ('bd_c4', 'u'), 'bd_c4': ('bd_c4', 'u'),
    'INIT_c2_norst': ('bd_c2_norst', 'u'), 'bd_c2_norst': ('bd_c2_norst', 'u'),
    'INIT_c3_norst': ('bd_c3_norst', 'u'), 'bd_c3_norst': ('bd_c3_norst', 'u'),
    'ST_INIT': ('bd_arbiter', 'ustate'), 'INIT_HELD': ('bd_arbiter', 'ustate'), 'ARB_ST': ('bd_arbiter', 'ustate'),
    'arb_state': ('bd_arbiter', 'ustate'), 'ARBITER_INIT': ('bd_arbiter', 'ustate'),
    'INIT_UNHELD': (None, None),
    'GR_INIT': ('bd_arbiter', 'ugrant'), 'INIT_GRANTS': ('bd_arbiter', 'ugrant'), 'GRANT': ('bd_arbiter', 'ugrant'),
    'arb_grant': ('bd_arbiter', 'ugrant'),
    'INIT_LAT': ('bd_latch', 'u'), 'ODD': ('bd_latch', 'u'), 'latch_odd': ('bd_latch', 'u'),
    'INIT_PAIR': ('bd_latch', 'u'), 'PAIR': ('bd_latch', 'u'), 'latch_pair': ('bd_latch', 'u'),
    'RST0': ('bd_latch_rst', 'u'), 'RST1': ('bd_latch_rst', 'u'),
    'latch_rst0': ('bd_latch_rst', 'u'), 'latch_rst1': ('bd_latch_rst', 'u'),
    'INIT_DB': ('bd_link_dctl', 'ub'), 'INIT_DA': ('bd_link_dctl', 'ua'),
    'INIT_DLD': ('bd_link_dctl', 'uld'), 'INIT_DLT': ('bd_link_dctl', 'ult'),
    'BUF': ('bd_delay', 'u'), 'delay_buf': ('bd_delay', 'u'),
    'FF_SIDE': ('bd_delay', 'u'), 'delay_and': ('bd_delay', 'u'),
    'FR_SIDE': ('bd_delay', 'u'), 'delay_or': ('bd_delay', 'u'),
    'datamux_pair': ('bd_datamux', 'u'), 'datamux_odd': ('bd_datamux', 'u'),
    'xor2': (None, None),
}
NON_INIT = {'mask1', 'mask2', 'mask3', 'dmask1', 'dmask0', 'MASK', 'init0', 'toyReq', 'toySetup'}


def candidates(insts, value, width_hint=None):
    out = []
    for inst in insts:
        for v in inst['inits']:
            if v == value:
                out.append((inst, v, 'exact'))
            elif width_hint and value == v & ((1 << width_hint) - 1):
                out.append((inst, v, 'low%d' % width_hint))
    return out


def compare_pins(inst, init, outpin, lean_pins, ctx=None):
    """Return (verdict, per-position notes)."""
    notes, verdict = [], 'EQUAL'
    rtl = inst['ins']
    n = len(rtl) if not (inst['prim'] == 'LUT6_2' and outpin == 'O5') else 5
    lp = list(lean_pins)
    if len(lp) < n:
        if inst['prim'] == 'LUT6_2' and outpin == 'O5':
            pass
        notes.append('Lean lists %d pins, RTL %d' % (len(lp), n))
        if len(lp) < n:
            verdict = 'MISMATCH'
    for i in range(min(n, len(lp))):
        L, R = lp[i], rtl[i]
        if isinstance(L, int) and isinstance(R, int):
            if L != R:
                notes.append('I%d: Lean %d vs RTL %d' % (i, L, R)); verdict = 'MISMATCH'
        elif isinstance(L, int):
            notes.append('I%d: Lean ties %s=%d (spec.)' % (i, R, L))
            if verdict == 'EQUAL':
                verdict = 'EQUAL+SPEC'
        elif isinstance(R, int):
            if depends_on(inst, init, outpin, i):
                notes.append('I%d: Lean var %r on RTL const %d, output DEPENDS on it' % (i, L, R))
                verdict = 'MISMATCH'
            else:
                notes.append('I%d: Lean var %r on RTL const %d (output independent: OK)' % (i, L, R))
        else:
            al = ALIAS.get(L, 'missing')
            if ctx == 'FREE':
                al = None
            elif ctx and L in ctx:
                al = ctx[L]
            if L == R or (al and al != 'missing' and R in al):
                pass
            elif al is None:
                notes.append('I%d: Lean %r (free/scenario var) on RTL %s' % (i, L, R))
            else:
                notes.append('I%d: Lean %r vs RTL %s: REVIEW' % (i, L, R))
                if verdict in ('EQUAL', 'EQUAL+SPEC'):
                    verdict = 'REVIEW'
    return verdict, notes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rtl', default='/home/user/wt-research/cells/rtl')
    ap.add_argument('--rtl2', default='/home/user/wt-formal/cells/rtl')
    ap.add_argument('--lean', nargs='+', default=['/home/user/wt-formal/formal/lean/Formal',
                                                  '/home/user/wt-formal/formal/lean/Wip'])
    ap.add_argument('--json', default=None)
    a = ap.parse_args()

    insts = parse_rtl(a.rtl)
    insts2 = parse_rtl(a.rtl2)
    k1 = [(i['module'], i['name'], tuple(i['inits']), tuple(map(str, i['ins'])), tuple(sorted(i['out'].items())))
          for i in insts]
    k2 = [(i['module'], i['name'], tuple(i['inits']), tuple(map(str, i['ins'])), tuple(sorted(i['out'].items())))
          for i in insts2]
    print('== RTL LUT instances (%s): %d ; other branch (%s): %d ; identical LUT sets: %s'
          % (a.rtl, len(insts), a.rtl2, len(insts2), k1 == k2))
    for i in insts:
        print('  %-14s %-11s %-7s %-6s INIT=%-40s I=%s  out=%s' % (
            i['file'] + ':' + str(i['line']), i['module'], i['name'], i['prim'],
            '|'.join('%X' % v for v in i['inits']), i['ins'], i['out']))

    consts, uses = parse_lean(a.lean)
    print('\n== Lean INIT-like constants: %d' % len(consts))
    const_rows = []
    for c in consts:
        if c['name'] in NON_INIT:
            print('  %-40s %-14s (not a LUT INIT: proof mask/scalar, skipped)' % (c['file'] + ':' + str(c['line']), c['name']))
            continue
        width = 16 if c['kind'] == 'inline' else None
        cands = candidates(insts, c['value'], width)
        intended = INTENDED.get(c['name'])
        if c['kind'] == 'inline' and c['value'] == 0x00E8:
            intended = ('bd_c2', 'u')
        hit = [x for x in cands if intended and (x[0]['module'], x[0]['name']) == intended]
        verdict = ('EQUAL' if hit and hit[0][2] == 'exact' else
                   ('EQUAL (sub-table %s)' % hit[0][2] if hit else
                    ('NO RTL (intended: none)' if intended == (None, None) else
                     ('MISMATCH' if intended else 'UNMAPPED'))))
        mods = sorted({'%s.%s' % (x[0]['module'], x[0]['name']) for x in cands})
        const_rows.append(dict(c, intended=intended, verdict=verdict, rtl_same_value=mods))
        print('  %-40s %-14s 0x%016X intended=%s -> %s ; RTL with same value: %s' % (
            c['file'] + ':' + str(c['line']), c['name'], c['value'],
            '%s.%s' % intended if intended else '?', verdict, ', '.join(mods) or '-'))

    print('\n== Lean use sites with explicit pin lists: %d' % len(uses))
    use_rows = []
    for u in uses:
        if u['init'] in ('init', 'st', 'L') or u['value'] is None:
            print('  %-40s %-6s %-12s generic INIT parameter (%s) [%s]' % (
                u['file'] + ':' + str(u['line']), u['fn'], u['init'], u['raw'][:60], 'skipped'))
            continue
        intended = INTENDED.get(u['init'].split('.')[-1])
        if intended == (None, None) or intended is None:
            print('  %-40s %-6s %-12s no RTL counterpart intended (%s)' % (
                u['file'] + ':' + str(u['line']), u['fn'], u['init'], u['raw'][:60]))
            continue
        cand = [i for i in insts if (i['module'], i['name']) == intended and u['value'] in i['inits']]
        if not cand:
            print('  %-40s %-6s %-12s VALUE NOT IN INTENDED RTL INSTANCE %s.%s' % (
                u['file'] + ':' + str(u['line']), u['fn'], u['init'], *intended))
            use_rows.append(dict(u, rtl=None, verdict='MISMATCH', notes=['INIT value not in RTL']))
            continue
        # among intended instances pick the one with matching output kind
        best = None
        for inst in cand:
            outpin = u['out']
            if inst['prim'] != 'LUT6_2' and outpin in ('O5', 'O6'):
                if inst['prim'] == 'LUT6' and outpin == 'O6':
                    outpin = 'O'
                else:
                    continue
            if inst['prim'] == 'LUT6_2' and outpin == 'O':
                outpin = 'O6'
            if inst['prim'] != 'LUT6_2' and len(u['pins']) != inst['nin']:
                continue
            v, notes = compare_pins(inst, u['value'], outpin, u['pins'],
                                    CONTEXT.get((os.path.basename(u['file']), u['line'])))
            if best is None or (v.startswith('EQUAL') and not best[1].startswith('EQUAL')):
                best = (inst, v, notes, outpin)
        if best is None:
            print('  %-40s %-6s %-12s no RTL instance of %s.%s with this arity/output' % (
                u['file'] + ':' + str(u['line']), u['fn'], u['init'], *intended))
            use_rows.append(dict(u, rtl=None, verdict='MISMATCH', notes=['arity/output']))
            continue
        inst, v, notes, outpin = best
        rtl_out = inst['out'].get(outpin)
        use_rows.append(dict(u, rtl='%s:%s %s.%s' % (inst['file'], inst['line'], inst['module'], inst['name']),
                             outpin=outpin, rtl_out=rtl_out, verdict=v, notes=notes))
        print('  %-40s %-4s %-10s -> %s:%s %s.%s %s(%s) pins=%s : %s %s' % (
            u['file'] + ':' + str(u['line']), u['fn'], u['init'], inst['file'], inst['line'],
            inst['module'], inst['name'], outpin, rtl_out, u['pins'], v, '; '.join(notes)))

    print('\n== RTL LUT instances with no Lean counterpart (by intended mapping)')
    covered = {INTENDED[c['name']] for c in const_rows if c['name'] in INTENDED}
    covered.add(('bd_c2', 'u'))
    # submodule reuse: bd_arbcell.ugrant has the same INIT/pins as bd_arbiter.ugrant
    for i in insts:
        key = (i['module'], i['name'])
        tag = 'covered' if key in covered else ('covered via identical bd_arbiter.ugrant'
                                                if key == ('bd_arbcell', 'ugrant') else 'NO LEAN')
        if tag == 'NO LEAN':
            print('  %s:%s %s.%s %s INIT=%s' % (i['file'], i['line'], i['module'], i['name'], i['prim'],
                                               '|'.join('%X' % v for v in i['inits'])))

    print('\n== Truth-table checks of RTL INITs vs RTL header and Lean-claimed equations')
    rows = check_claims(insts)
    for r in rows:
        print('  %-13s %-7s %-3s INIT=%-17s %-9s %-55s %s' % (
            r['module'], r['inst'], r['out'], r['init'], r['source'], r['claim'][:55],
            {True: 'OK (%d rows)' % r['n'], False: 'FAIL e.g. %s' % r['counterexample'], None: '-'}[r['ok']]))

    print('\n== Independent derivation of LUT6_2 constants from their stated equations')
    def derive62(f6, f5):
        v = 0
        for idx in range(64):
            bits = [(idx >> k) & 1 for k in range(6)]
            if bits[5]:
                v |= f6(*bits[:5]) << idx
            else:
                v |= f5(*bits[:5]) << idx
        return v
    held = derive62(lambda r1, r2, q, rst, a0: int(rst or (q if a0 else maj(r1, 1 - r2, q))),
                    lambda r1, r2, q, rst, a0: int((r1 and q) or (r2 and not q)))
    unheld = derive62(lambda r1, r2, q, rst, a0: int(rst or maj(r1, 1 - r2, q)),
                      lambda r1, r2, q, rst, a0: int((r1 and q) or (r2 and not q)))
    grant = derive62(lambda r1, r2, q, x, y: int(r2 and not q), lambda r1, r2, q, x, y: int(r1 and q))
    pair = derive62(lambda di, en, qi, dj, qj: dj if en else qj, lambda di, en, qi, dj, qj: di if en else qi)
    dmux = derive62(lambda s, ai, bi, aj, bj: bj if s else aj, lambda s, ai, bi, aj, bj: bi if s else ai)
    for nm, v, ref in (('held state (q=rst+(A0?q:C(r1,~r2)), R0)', held, 0xFFF0FFB2ACACACAC),
                       ('unheld state (q=rst+C(r1,~r2), R0) = Lean INIT_UNHELD', unheld, 0xFFB2FFB2ACACACAC),
                       ('grants', grant, 0x0C0C0C0CA0A0A0A0), ('latch pair', pair, 0xFF33CC00B8B8B8B8),
                       ('datamux pair', dmux, 0xFFAA5500E4E4E4E4)):
        print('  %-55s derived 0x%016X  constant 0x%016X  %s' % (nm, v, ref, 'EQUAL' if v == ref else 'DIFFERENT'))

    if a.json:
        with open(a.json, 'w') as fh:
            json.dump(dict(rtl=insts, rtl_branches_identical=(k1 == k2), lean_consts=const_rows,
                           lean_uses=use_rows, claims=rows), fh, indent=1, default=str)


if __name__ == '__main__':
    main()
