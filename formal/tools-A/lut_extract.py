#!/usr/bin/env python3
"""lut_extract.py -- extract every LUT primitive instance from cells/rtl/*.v
and emit formal/lean/Formal/Core/LutCells.lean (namespace Formal.Core.LutCells).

The Lean terms are generated from the Verilog text, never transcribed by hand.
For every instance we record: enclosing module, instance name, source file:line,
primitive (LUT1..LUT6, LUT6_2), INIT, the I0..Ik-1 pin connections and the
output connections.  A pin connection is classified as
  * c0 / c1          tied constant (1'b0 / 1'b1)
  * fb O|O5|O6       the instance's OWN output (the same net expression as one
                     of its output ports): the cell's feedback
  * sig "<expr>"     anything else (a cell input, another LUT's output, ...)
An INIT given by a localparam of the form  NAME = cond ? LIT : LIT  is emitted
as two variants (suffix _t / _f), so parametrised cells are covered for both
parameter values.

Usage:  python3 formal/tools-A/lut_extract.py [repo_root]
            writes formal/lean/Formal/Core/LutCells.lean, summary on stderr
        python3 formal/tools-A/lut_extract.py --audit [repo_root]
            independent cross-check of Formal.Core.LutAudit.audit: for every
            output, counts (sHF, sHZ, dHF, dHZ) of multi-input changes with the
            feedback pins held, by brute-force vertex enumeration (Nowick-Dill
            dynamic definition, Eichelberger static); writes nothing.
"""
import os, re, sys

AUDIT = '--audit' in sys.argv
ARGS = [a for a in sys.argv[1:] if a != '--audit']
ROOT = ARGS[0] if ARGS else os.path.join(os.path.dirname(__file__), '..', '..')
ROOT = os.path.abspath(ROOT)
RTL = os.path.join(ROOT, 'cells', 'rtl')
OUT = os.path.join(ROOT, 'formal', 'lean', 'Formal', 'Core', 'LutCells.lean')

INST_RE = re.compile(r'\b(LUT[1-6](?:_2)?)\s*#\(\s*\.INIT\(\s*([^)]*?)\s*\)\s*\)\s*(\w+)\s*\((.*?)\)\s*;', re.S)
PORT_RE = re.compile(r'\.(\w+)\s*\(\s*([^()]*?)\s*\)')
MOD_RE = re.compile(r'^\s*module\s+(\w+)', re.M)
LP_RE = re.compile(r'localparam\s*(?:\[[^\]]*\])?\s*(\w+)\s*=\s*([^;]*?)\?\s*([0-9]+\'h[0-9A-Fa-f_]+)\s*:\s*([0-9]+\'h[0-9A-Fa-f_]+)\s*;', re.S)

def strip_comments(s):
    # keep line structure (replace comment chars by spaces) so offsets map to lines
    out = re.sub(r'//[^\n]*', lambda m: ' ' * len(m.group(0)), s)
    return re.sub(r'/\*.*?\*/', lambda m: re.sub(r'[^\n]', ' ', m.group(0)), out, flags=re.S)

def lit(v):
    m = re.fullmatch(r"([0-9]+)'h([0-9A-Fa-f_]+)", v.strip())
    if not m: return None
    return int(m.group(2).replace('_', ''), 16), int(m.group(1))

def lean_ident(s):
    return re.sub(r'[^A-Za-z0-9_]', '_', s)

def extract():
    res = []
    for fn in sorted(os.listdir(RTL)):
        if not fn.endswith('.v'): continue
        path = os.path.join(RTL, fn)
        raw = open(path).read()
        txt = strip_comments(raw)
        mods = [(m.start(), m.group(1)) for m in MOD_RE.finditer(txt)]
        lps = {m.group(1): (m.group(2).strip(), lit(m.group(3)), lit(m.group(4)))
               for m in LP_RE.finditer(txt)}
        for m in INST_RE.finditer(txt):
            prim, init_s, inst, body = m.group(1), m.group(2), m.group(3), m.group(4)
            line = txt.count('\n', 0, m.start()) + 1
            module = [n for (p, n) in mods if p <= m.start()][-1]
            ports = dict((p, e.strip()) for p, e in PORT_RE.findall(body))
            k = int(prim[3])
            outs = [o for o in ('O', 'O5', 'O6') if o in ports]
            variants = []
            L = lit(init_s)
            if L is not None:
                variants.append(('', L[0], None))
            elif init_s in lps:
                cond, lt, lf = lps[init_s]
                variants.append(('_t', lt[0], '%s = %s (true branch: %s)' % (init_s, cond, hex(lt[0]))))
                variants.append(('_f', lf[0], '%s = %s (false branch: %s)' % (init_s, cond, hex(lf[0]))))
            else:
                raise SystemExit('cannot resolve INIT %r at %s:%d' % (init_s, fn, line))
            pins = []
            for i in range(k):
                e = ports.get('I%d' % i)
                if e is None: raise SystemExit('missing I%d at %s:%d' % (i, fn, line))
                if e == "1'b0": pins.append(('c0', None))
                elif e == "1'b1": pins.append(('c1', None))
                else:
                    fb = [o for o in outs if ports[o] == e]
                    pins.append(('fb', fb[0]) if fb else ('sig', e))
            for suf, init, note in variants:
                assert init < (1 << (1 << k))
                res.append(dict(file='cells/rtl/' + fn, line=line, module=module, inst=inst,
                                prim=prim, k=k, init=init, pins=pins,
                                outs=[(o, ports[o]) for o in outs], suf=suf, note=note))
    return res

def lean_pin(p):
    t, v = p
    if t == 'c0': return '.c0'
    if t == 'c1': return '.c1'
    if t == 'fb': return '(.fb .%s)' % v
    return '(.sig "%s")' % v

def emit(res):
    L = []
    L.append('/-!\n# Formal.Core.LutCells -- every LUT instance of cells/rtl/*.v\n')
    L.append('GENERATED by `formal/tools-A/lut_extract.py` from the Verilog. Do not edit by hand:')
    L.append('rerun `python3 formal/tools-A/lut_extract.py`. Definitions only, nothing to prove.\n')
    L.append('Pins are listed I0 first (UNISIM naming; I0 = A1 is INIT address bit 0, I5 = A6')
    L.append('is the root of the mux tree). `fb o` marks a pin wired to the instance\'s OWN')
    L.append('output `o` (the cell\'s feedback); `c0`/`c1` tied constants; `sig` anything else.\n-/\n')
    L.append('namespace Formal.Core.LutCells\n')
    L.append('inductive OutSel where\n  | O\n  | O5\n  | O6\n  deriving DecidableEq, Repr\n')
    L.append('inductive Pin where\n  | c0\n  | c1\n  | fb (o : OutSel)\n  | sig (net : String)\n  deriving DecidableEq, Repr\n')
    L.append('structure LutInst where\n  module : String\n  inst : String\n  src : String\n  prim : String\n'
             '  k : Nat\n  init : Nat\n  pins : List Pin\n  outs : List (OutSel × String)\n  deriving Repr\n')
    names = []
    base = [lean_ident('%s_%s' % (r['module'], r['inst'])) for r in res]
    for r, b in zip(res, base):
        # an instance name reused in two generate branches gets its line number
        nm = b + ('_L%d' % r['line'] if sum(1 for (x, y) in zip(res, base)
                                            if y == b and x['line'] != r['line']) else '') + r['suf']
        assert nm not in names, nm
        names.append(nm)
        r['lean'] = nm
        doc = '%s:%d  %s %s.%s' % (r['file'], r['line'], r['prim'], r['module'], r['inst'])
        if r['note']: doc += '  [variant ' + r['note'] + ']'
        L.append('/-- %s -/' % doc)
        L.append('def %s : LutInst where' % nm)
        L.append('  module := "%s"\n  inst := "%s"\n  src := "%s:%d"\n  prim := "%s"\n  k := %d'
                 % (r['module'], r['inst'], r['file'], r['line'], r['prim'], r['k']))
        L.append('  init := 0x%X' % r['init'])
        L.append('  pins := [%s]' % ', '.join(lean_pin(p) for p in r['pins']))
        L.append('  outs := [%s]\n' % ', '.join('(.%s, "%s")' % (o, e) for o, e in r['outs']))
    L.append('/-- Every extracted instance, in file order. -/')
    L.append('def all : List LutInst :=\n  [%s]\n' % ',\n   '.join(names))
    L.append('end Formal.Core.LutCells')
    return '\n'.join(L) + '\n'

def audit(res):
    import itertools
    def cube(old, new):
        ch = [i for i in range(len(old)) if old[i] != new[i]]
        for bits in itertools.product([0, 1], repeat=len(ch)):
            v = list(old)
            for i, b in zip(ch, bits): v[i] = b
            yield tuple(v)
    def classify(f, old, new):
        if f(old) == f(new):
            return 'sHF' if all(f(v) == f(old) for v in cube(old, new)) else 'sHZ'
        for C in cube(old, new):
            if f(C) == f(new) and any(f(D) != f(new) for D in cube(C, new)): return 'dHZ'
        return 'dHF'
    for r in res:
        fr = [i for i, (t, _) in enumerate(r['pins']) if t in ('sig', 'fb')]
        fb = [j for j, i in enumerate(fr) if r['pins'][i][0] == 'fb']
        for o, _ in r['outs']:
            def f(v, r=r, o=o):
                it = iter(v); full = []
                for t, _ in r['pins']:
                    full.append(0 if t == 'c0' else 1 if t == 'c1' else next(it))
                idx = sum(b << i for i, b in enumerate(full))
                if o == 'O5': idx &= 31
                return (r['init'] >> idx) & 1
            m = len(fr); cnt = dict(sHF=0, sHZ=0, dHF=0, dHZ=0)
            for old in itertools.product([0, 1], repeat=m):
                for new in itertools.product([0, 1], repeat=m):
                    if any(old[j] != new[j] for j in fb): continue
                    if sum(a != b for a, b in zip(old, new)) < 2: continue
                    cnt[classify(f, old, new)] += 1
            print(r['lean'], o, m, cnt['sHF'], cnt['sHZ'], cnt['dHF'], cnt['dHZ'])

if __name__ == '__main__':
    res = extract()
    src = emit(res)
    if AUDIT:
        audit(res); sys.exit(0)
    with open(OUT, 'w') as f: f.write(src)
    for r in res:
        print('%-26s %-20s %-6s INIT=%-18s pins=%s outs=%s' % (
            '%s:%d' % (r['file'][10:], r['line']), r['lean'], r['prim'], hex(r['init']),
            ' '.join(lean_pin(p) for p in r['pins']), r['outs']), file=sys.stderr)
    print('%d instances -> %s' % (len(res), OUT), file=sys.stderr)
