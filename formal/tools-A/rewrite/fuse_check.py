#!/usr/bin/env python3
"""fuse_check.py A.mlir B.mlir [--env-a K=V,...] [--env-b K=V,...] [--bdc BDCDIR] [--keep DIR]
-- are two handshake graphs the same up to operator fusion? Proved in Lean, or refused.

For a fusion pass (bdc's region fusion, research's ringfuse): the same MLIR imported with two sets of bdc knobs
(`--env-a BDC_OP_FUSION=0,BDC_FORK_FUSION=0` against the default), or an MLIR and its fused rewrite.
  1. dfimport of A and of B (bdc's own parser and fusion plan; --bdc reads bdc from BDCDIR).
  2. Untrusted planner: each import is taken to its maximal-fusion normal form by a script of local steps
     (Formal.Rewrite.Steps.Script): absorb every comp into its only (comp) reader; dedupe a comp reading two copies of
     one forked value; remove one-output forks feeding a comp (wire); then every comp's inputs are put in the order in
     which its expression first reads them (reorder), and the dead sinks are dropped.
  3. rules_iso.py finds the renumbering between the two normal forms.
  4. One Lean file: both scripts accepted by `runScript` (decide +kernel), `renCheck` of the normal forms, and
     pass_forward / pass_backward from `runScript_sound`: from tokens on the inputs only, every complete run of A has a
     complete run of B with the same result tokens, and vice versa. `#print axioms`: propext, Classical.choice,
     Quot.sound only.
Exit 0: PROVED. 2: refused (normal forms differ, or Lean rejected). 3: A and B import to the same rules.
NOT covered: dfimport (MLIR -> rules) is trusted Python; nothing below the token level.
"""
import json, os, re, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
LEAN = os.path.join(ROOT, 'formal', 'lean')
sys.path.insert(0, HERE)
import plain_pass as PP   # noqa: E402
import eq2_check as Q     # noqa: E402

def dedupE(ins, a, b, F):
    er = list(ins); er.remove(b)
    return Q.subst(F, [('var', Q.pos(er, a if c == b else c)) for c in ins])

def swA(a, x, c): return x if c == a else c

class FPlan(Q.Plan):
    def do(self, st):
        k = st[0]; rs = self.rs
        if k == 'dedupe':
            _, lf, lc, a, b = st; rf, rc = rs[lf], rs[lc]
            os_ = list(rf[2]); os_.remove(b); ins = list(rc[1]); er = list(ins); er.remove(b)
            rs[lf] = ('fork', rf[1], os_); rs[lc] = ('comp', er, rc[2], dedupE(ins, a, b, rc[3]))
            self.pre += [a, b]; self.chg += [b]; self.steps.append(st)
        elif k == 'wire':
            _, lf, lc = st; rf, rc = rs[lf], rs[lc]; x, a = rf[1], rf[2][0]
            rs[lf] = ('sink', a); rs[lc] = ('comp', [swA(a, x, c) for c in rc[1]], rc[2], rc[3])
            self.sinks.append(lf); self.pre += [a]; self.chg += [x, a]; self.steps.append(st)
        else:
            Q.Plan.do(self, st)

def first_vars(e, acc):
    k = e[0]
    if k == 'var':
        if e[1] not in acc: acc.append(e[1])
    elif k == 'un': first_vars(e[3], acc)
    elif k == 'bin': first_vars(e[3], acc); first_vars(e[4], acc)
    elif k == 'sel': first_vars(e[1], acc); first_vars(e[2], acc); first_vars(e[3], acc)
    return acc

def normal_form(rs):
    p = FPlan(rs); R = p.rs
    changed = True
    while changed:
        changed = False
        # absorb: a comp whose output only one comp reads
        for lp, r in enumerate(R):
            if r[0] != 'comp' or not r[1]: continue
            o = r[2]; W = Q.writers(R, o); Rd = Q.readers(R, o)
            if W != [lp] or len(Rd) != 1 or Rd[0] == lp or R[Rd[0]][0] != 'comp': continue
            lq = Rd[0]; ins = list(R[lq][1])
            if ins.count(o) != 1 or set(r[1]) & set(ins) or R[lq][2] in r[1] + [o]: continue
            ins2 = [c for c in ins if c != o] + [o]
            if ins2 != ins: p.do(('reorder', lq, ins2))
            p.do(('absorb', lp, lq)); changed = True; break
        if changed: continue
        # dedupe: a comp reading two outputs of one fork
        for lc, r in enumerate(R):
            if r[0] != 'comp': continue
            byfork = {}
            for c in r[1]:
                W = Q.writers(R, c)
                if len(W) == 1 and R[W[0]][0] == 'fork' and Q.readers(R, c) == [lc]: byfork.setdefault(W[0], []).append(c)
            hit = next(((lf, cs) for lf, cs in byfork.items() if len(cs) >= 2), None)
            if hit:
                lf, cs = hit; p.do(('dedupe', lf, lc, cs[0], cs[1])); changed = True; break
        if changed: continue
        # wire: a one-output fork feeding a comp
        for lf, r in enumerate(R):
            if r[0] != 'fork' or len(r[2]) != 1: continue
            a = r[2][0]; x = r[1]; Rd = Q.readers(R, a)
            if len(Rd) != 1 or R[Rd[0]][0] != 'comp' or x in R[Rd[0]][1] or Q.readers(R, x) != [lf]: continue
            p.do(('wire', lf, Rd[0])); changed = True; break
    # canonical input order: first read in the expression
    for l, r in enumerate(R):
        if r[0] != 'comp' or len(r[1]) < 2: continue
        order = first_vars(r[3], [])
        ins = list(r[1]); ins2 = [ins[i] for i in order if i < len(ins)]
        ins2 += [c for c in ins if c not in ins2]
        if ins2 != ins: p.do(('reorder', l, ins2))
    p.drops()
    return p

def refuse(why):
    print('fuse_check: REFUSED -- ' + why); return 2

def parse_env(s):
    return dict(kv.split('=', 1) for kv in s.split(',') if kv) if s else {}

def imp(mlir, out, ns, env):
    keep = {k: os.environ.get(k) for k in env}
    os.environ.update(env)
    try:
        return PP.dfimport(mlir, out, ns)
    finally:
        for k, v in keep.items():
            if v is None: os.environ.pop(k, None)
            else: os.environ[k] = v

def main():
    args = sys.argv[1:]; keep = None; ea = eb = ''
    for flag in ('--keep', '--bdc', '--env-a', '--env-b'):
        if flag in args:
            i = args.index(flag); v = args[i + 1]; del args[i:i + 2]
            if flag == '--keep': keep = v
            elif flag == '--bdc': PP.BDCDIR = v
            elif flag == '--env-a': ea = v
            else: eb = v
    if len(args) != 2: print(__doc__); return 1
    tmp = keep or tempfile.mkdtemp(prefix='fuse_check_'); os.makedirs(tmp, exist_ok=True)
    rc = run(args[0], args[1], parse_env(ea), parse_env(eb), tmp)
    if rc == 0: print(f'fuse_check: PROVED -- {args[1]} [{eb}] is equal to {args[0]} [{ea}] '
                      f'(Lean: {tmp}/Eq2CheckRun.lean; axioms propext, Classical.choice, Quot.sound)')
    return rc

def run(fa, fb, ea, eb, tmp):
    Ra, Na, oa, naa = imp(fa, os.path.join(tmp, 'A.lean'), 'FuA', ea)
    Rb, Nb, ob, nab = imp(fb, os.path.join(tmp, 'B.lean'), 'FuB', eb)
    if Ra == Rb: print('fuse_check: A and B import to the same rules'); return 3
    if naa != nab: return refuse('different numbers of inputs')
    if oa is None or ob is None: return refuse('no data output channel (chOut)')
    pa, pb = normal_form(Ra), normal_form(Rb)
    n1, n2 = os.path.join(tmp, 'nf1.lean'), os.path.join(tmp, 'nf2.lean')
    open(n1, 'w').write('def rules : List Rule := ' + PP.ser_rules(pa.rs) + '\n')
    open(n2, 'w').write('def rules : List Rule := ' + PP.ser_rules(pb.rs) + '\n')
    mp = os.path.join(tmp, 'maps.json')
    ri = subprocess.run([sys.executable, os.path.join(HERE, 'rules_iso.py'), n1, n2, mp], capture_output=True, text=True)
    if ri.returncode != 0: return refuse('normal forms differ: ' + ri.stdout[-300:])
    m = json.load(open(mp))
    ch = {int(a): b for a, b in m['chan'].items()}; ru = {int(a): b for a, b in m['rule'].items()}
    K = max(list(ch) + list(ch.values())) + 1
    freeA = [c for c in range(K) if c not in ch]; freeB = [c for c in range(K) if c not in set(ch.values())]
    for a, b in zip(freeA, freeB): ch[a] = b
    P = [ch[c] for c in range(K)]; Pi = [0] * K
    for a, b in ch.items(): Pi[b] = a
    R = len(ru); T = [ru[l] for l in range(R)]; Ti = [0] * R
    for a, b in ru.items(): Ti[b] = a
    s1 = '[' + ', '.join(Q.ser_step(s) for s in pa.steps) + ']'
    s2 = '[' + ', '.join(Q.ser_step(s) for s in pb.steps) + ']'
    lean = Q.TEMPLATE.format(inp=f'{os.path.abspath(fa)} [{ea}]', out=f'{os.path.abspath(fb)} [{eb}]',
                             rin=PP.ser_rules(Ra), rout=PP.ser_rules(Rb), s1=s1, s2=s2, P=P, Pi=Pi, T=T, Ti=Ti,
                             NA=naa, oi=oa, oo=ob, **Q.lits(pa, pb)).replace('eq2_check.py', 'fuse_check.py')
    lf = os.path.join(tmp, 'Eq2CheckRun.lean'); open(lf, 'w').write(lean)
    env = dict(os.environ); env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')
    b = subprocess.run(['lake', 'build', 'Formal.Rewrite.Steps.ScriptSound', 'Formal.Rewrite.Rename'], cwd=LEAN,
                       env=env, capture_output=True, text=True)
    if b.returncode != 0: return refuse('lake build failed: ' + b.stdout[-400:])
    c = subprocess.run(['lake', 'env', 'lean', lf], cwd=LEAN, env=env, capture_output=True, text=True)
    txt = c.stdout + c.stderr
    open(os.path.join(tmp, 'lean.log'), 'w').write(txt)
    ax = re.findall(r"depends on axioms: \[([^\]]*)\]", txt)
    ok = (c.returncode == 0 and 'error' not in txt and 'sorry' not in txt and len(ax) == 2 and
          all(sorted(a.replace(' ', '').split(',')) == ['Classical.choice', 'Quot.sound', 'propext'] for a in ax))
    if not ok: return refuse(f'Lean rejected (rc {c.returncode}); see {tmp}/lean.log')
    return 0

if __name__ == '__main__':
    sys.exit(main())
