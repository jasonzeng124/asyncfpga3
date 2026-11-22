#!/usr/bin/env python3
"""Auditor's own extractor: token-level graph from bdc's emitted Verilog (top module) and from the Lean `rules`.
Compares them by channel name. Usage: vextract.py KERNEL.v LEANFILE"""
import re, sys
V = open(sys.argv[1]).read(); LF = open(sys.argv[2]).read()
top = V[V.index('module bdc_xorshift'):]
mods = {}
for m in re.finditer(r'module (bdc_fused_\w+) .*?endmodule', V, re.S):
    mods[m.group(1)] = m.group(0)

def ch(sig):   # n_foo__0_req -> foo#0 ; n4__0 -> 4#0
    s = re.sub(r'_(req|ack|data|freq|fack)$', '', sig)
    if not s.startswith('n'): return '@'+s
    s = s[1:]
    if s.startswith('_'): s = s[1:]
    s = re.sub(r'__(\d+)', r'#\1', s)
    return s
alias = {}   # identity buffers / wires: from -> to  (token level)
rules = []
# instances: type #(...) name ( ... );
for m in re.finditer(r'\n\s*(bd_\w+|bdc_\w+)\s*(?:#\((?:[^()]|\([^()]*\))*\))?\s*(\w+)\s*\((.*?)\);', top, re.S):
    typ, name, body = m.groups()
    def port(p):
        mm = re.search(r'\.' + p + r'\(([^)]*)\)', body)
        return mm.group(1).strip() if mm else None
    def lst(p):
        return [x.strip() for x in port(p).strip('{}').split(',')]
    if typ in ('bd_link', 'bd_pipe'):
        a, b = port('req_in'), port('req_out')
        alias[a] = b
    elif typ == 'bd_fork':
        rules.append(['fork', port('req'), list(reversed(lst('req_out'))), name])
    elif typ == 'bd_join':
        rules.append(['join', lst('req_in'), port('req'), name])
    elif typ == 'bd_steer':
        rules.append(['steer', port('req'), port('s'), port('req1'), port('req0'), name])
    elif typ == 'bd_mux':
        rules.append(['mux', port('ctl_req'), [port('x_req'), port('y_req')], port('z_req'), name])
    elif typ.startswith('bdc_amerge'):
        rules.append(['amerge', [port('in0_req'), port('in1_req')], port('z_req'), port('index'), name])
    elif typ == 'bd_snk':
        rules.append(['sink', port('req'), name])
    elif typ.startswith('bdc_fused'):
        ins = []
        k = 0
        while port(f'e{k}_req'):
            ins.append(port(f'e{k}_req')); k += 1
        body_m = mods[typ]
        dp = re.findall(r'^\s*wire [^=]*?(\w+) = (.*);$', body_m[body_m.index('The datapath'):], re.M)
        rules.append(['comp', ins, port('z_req'), dp, name])
    else:
        rules.append(['?', typ, name])
# assigns: req aliases (constants/extui/args)
assigns = dict(re.findall(r'assign (\w+) = ([^;]+);', top))
# Resolve helper names
def res(sig):
    seen = 0
    while True:
        if sig in alias: sig = alias[sig]; continue
        break
    return sig
# join+steer -> branch
out = []
joins = {r[2]: r for r in rules if r[0] == 'join'}
for r in rules:
    if r[0] == 'steer':
        j = joins[r[1]]
        cond = r[2].split('[')[0].replace('_data', '_req')
        data = [x for x in j[1] if x != cond]
        assert len(data) == 1 and cond in j[1], (r, j)
        out.append(('branch', ch(res(cond)), ch(res(data[0])), ch(res(r[3])), ch(res(r[4])), r[5]))
    elif r[0] == 'fork':
        out.append(('fork', ch(res(r[1])), tuple(ch(res(x)) for x in r[2]), r[3]))
    elif r[0] == 'mux':
        out.append(('mux', ch(res(r[1])), tuple(ch(res(x)) for x in r[2]), ch(res(r[3])), r[4]))
    elif r[0] == 'sink':
        out.append(('sink', ch(res(r[1])), r[2]))
    elif r[0] == 'comp':
        out.append(('comp', tuple(ch(res(x)) for x in r[1]), ch(res(r[2])), r[3], r[4]))
    elif r[0] == 'amerge':
        out.append(('amerge', tuple(ch(res(x)) for x in r[1]), r[2], r[3], r[4]))
    elif r[0] != 'join':
        out.append(tuple(r))
# assign-defined units: constant (nX_data = literal, nX_req = trigger_req), extui
for k, v in assigns.items():
    if k.endswith('_req') and k.startswith('n') and v.startswith('n') and v.endswith('_req'):
        d = k[:-4] + '_data'
        out.append(('assignop', ch(res(v)), ch(res(k)), assigns.get(d), k))
for o in out: print(o)

# ---------------- comparison against the Lean `rules` ----------------
import random
names = eval(re.search(r'def chanNames : List String := (\[.*?\])\n', LF).group(1))
rtxt = re.search(r'def rules : List Rule := \[\n(.*?)\n\]', LF, re.S).group(1)
def tok(s):
    return re.findall(r'\(|\)|\[|\]|,|\.?[A-Za-z_][\w]*|\d+', s)
def parseE(ts, i):
    # returns (expr, i)
    if ts[i] == '(':
        e, i = parseE(ts, i + 1); assert ts[i] == ')'; return e, i + 1
    t = ts[i]
    if t == '.var': return ('var', int(ts[i+1])), i + 2
    if t == '.lit': return ('lit', int(ts[i+1])), i + 2
    if t == '.bin':
        if ts[i+1] == '(':   # (.cmpi .sgt)
            op = ('cmpi', ts[i+3][1:]); i = i + 5
        else:
            op = ts[i+1][1:]; i = i + 2
        w = int(ts[i]); a, i = parseE(ts, i + 1); b, i = parseE(ts, i); return ('bin', op, w, a, b), i
    if t == '.un':
        op = ts[i+1][1:]; w = int(ts[i+2]); a, i = parseE(ts, i + 3); return ('un', op, w, a), i
    raise SystemExit(f'parse {ts[i:i+5]}')
def evE(e, env):
    M = (1 << 32) - 1
    k = e[0]
    if k == 'var': return env[e[1]]
    if k == 'lit': return e[1]
    if k == 'un':
        assert e[1] == 'extui'; return evE(e[3], env) & ((1 << e[2]) - 1)
    op, w, a, b = e[1], e[2], evE(e[3], env), evE(e[4], env)
    m = (1 << w) - 1; a &= m; b &= m
    sg = lambda x: x - (1 << w) if x >> (w - 1) else x
    if op == 'xori': return a ^ b
    if op == 'addi': return (a + b) & m
    if op == 'shli': return (a << b) & m if b < w else 0
    if op == 'shrui': return a >> b if b < w else 0
    if op == ('cmpi', 'sgt'): return int(sg(a) > sg(b))
    if op == ('cmpi', 'slt'): return int(sg(a) < sg(b))
    raise SystemExit(op)
L = []
for line in rtxt.split('\n'):
    code = line.split('--')[0].strip().rstrip(',')
    ts = tok(code)
    kind = ts[0]
    if kind == '.fork':
        a = int(ts[1]); outs = [int(x) for x in ts[3:] if x.isdigit()]
        L.append(('fork', names[a], tuple(names[o] for o in outs)))
    elif kind == '.branch':
        c, d, t, f = map(int, ts[1:5]); L.append(('branch', names[c], names[d], names[t], names[f]))
    elif kind == '.mux':
        j = ts.index(']'); s = int(ts[1]); ins = [int(x) for x in ts[3:j] if x.isdigit()]
        L.append(('mux', names[s], tuple(names[x] for x in ins), names[int(ts[j+1])]))
    elif kind == '.sink':
        L.append(('sink', names[int(ts[1])]))
    elif kind == '.cm':
        a, r, ix, k = map(int, ts[1:5]); L.append(('cm', names[a], names[r], names[ix], k))
    elif kind == '.comp':
        j = ts.index(']'); ins = [int(x) for x in ts[2:j] if x.isdigit()]; oc = int(ts[j+1])
        e, _ = parseE(ts, j + 2)
        L.append(('comp', tuple(names[x] for x in ins), names[oc], e))
    else:
        raise SystemExit(kind)

# Verilog side normalized
def vexpr(dp, nin):
    """python function env->value for a fused datapath list"""
    def f(env):
        vals = {f'e{k}_data': env[k] for k in range(nin)}
        last = None
        for nm, ex in dp:
            ex2 = ex.replace("{1'b1, 31'b0}", str(1 << 31))
            ex2 = re.sub(r"(\d+)'h([0-9a-fA-F]+)", lambda m: str(int(m.group(2), 16)), ex2)
            ex2 = re.sub(r"(\d+)'b([01]+)", lambda m: str(int(m.group(2), 2)), ex2)
            ex2 = ex2.replace('~', 'NOT ')
            ex2 = re.sub(r'\b(\w+)\b', lambda m: f"vals['{m.group(1)}']" if m.group(1) in vals else m.group(1), ex2)
            ex2 = ex2.replace('NOT ', '1 ^ ')
            v = eval(ex2, {'vals': vals})
            v = int(v) & 0xffffffff
            vals[nm] = v; last = nm
        # z_data assigned from w_*; take the w_ / last real value
        return vals.get('z_data', vals[last]) if 'z_data' not in vals else vals[[n for n, _ in dp if n == 'z_data'][0]]
    return f
def vexpr_out(dp, nin):
    g = vexpr(dp, nin)
    def h(env):
        return g(env)
    return h
# z_data = w_nX where w_nX is a LUT1 of cmp_z: patch: treat w_nX as cmp_z
VV = []
for o in out:
    if o[0] == 'comp':
        dp = [(n, e) for n, e in o[3] if n != 'z_data']
        if dp[-1][0].startswith('cmp_z'):
            dp.append(('RESULT', dp[-1][0]))
        else:
            dp.append(('RESULT', dp[-1][0]))
        VV.append(('comp', o[1], o[2], dp))
    elif o[0] == 'assignop':
        VV.append(('assignop',) + o[1:4])
    elif o[0] == 'amerge':
        pass
    elif o[0] == 'fork' and o[1].startswith('@ucontrol_merge'):
        pass
    else:
        VV.append(o[:-1])
# control merges: amerge inputs + its fork outputs (result, index)
am = [o for o in out if o[0] == 'amerge']
cmf = {o[1][1:]: o[2] for o in out if o[0] == 'fork' and o[1].startswith('@ucontrol_merge')}
for o in am:
    res_, idx_ = cmf[o[4]]
    for k, a in enumerate(o[1]):
        VV.append(('cm', a, res_, idx_, k))

def run_dp(dp, env):
    vals = {f'e{k}_data': v for k, v in enumerate(env)}
    for nm, ex in dp:
        if nm == 'RESULT': return vals[ex]
        ex2 = ex.replace("{1'b1, 31'b0}", str(1 << 31))
        ex2 = re.sub(r"(\d+)'h([0-9a-fA-F]+)", lambda m: str(int(m.group(2), 16)), ex2)
        isnot = ex2.startswith('~')
        ex2 = ex2.lstrip('~')
        ex2 = re.sub(r'\b([a-z]\w*)\b', lambda m: f"vals['{m.group(1)}']", ex2)
        v = eval(ex2, {'vals': vals})
        v = int(v) & 0xffffffff
        if isnot: v = 1 ^ (v & 1)
        vals[nm] = v
# match
Lset = list(L); unmatched_v = []
rnd = random.Random(181)
edge = [0, 1, 2, 0x7fffffff, 0x80000000, 0xffffffff, 0xfffffffe, 0x80000001, 13, 17]
for v in VV:
    hit = None
    for l in Lset:
        if v[0] in ('fork', 'branch', 'mux', 'sink', 'cm') and v == l: hit = l; break
        if v[0] == 'comp' and l[0] == 'comp' and l[1] == v[1] and l[2] == v[2]:
            ok = True
            tests = [[a, b] for a in edge for b in edge] + [[rnd.getrandbits(32), rnd.getrandbits(32)] for _ in range(3000)]
            for env in tests:
                if run_dp(v[3], env[:len(v[1])]) != evE(l[3], env):
                    ok = False; print('  EXPR MISMATCH', v[2], env, run_dp(v[3], env[:len(v[1])]), evE(l[3], env)); break
            if ok: hit = l; break
        if v[0] == 'assignop' and l[0] == 'comp' and l[1] == (v[1],) and l[2] == v[2]:
            vs = v[3]
            if vs.startswith('{31'):
                ok = l[3] == ('un', 'extui', 1, ('var', 0))
            else:
                ok = l[3] == ('lit', int(vs.split("'h")[1], 16))
            if ok: hit = l; break
    if hit: Lset.remove(hit)
    else: unmatched_v.append(v)
print(f'Lean rules: {len(L)} ; Verilog units: {len(VV)} ; matched: {len(VV) - len(unmatched_v)}')
print('Verilog units with no Lean rule:', unmatched_v)
print('Lean rules with no Verilog unit:', Lset)
print('identity buffers (bd_link/bd_pipe) collapsed:', len(alias))
