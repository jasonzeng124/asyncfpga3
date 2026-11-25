#!/usr/bin/env python3
"""eq2_pass.py IN.mlir OUT.mlir [--bdc BDCDIR] [--keep DIR] -- the loop-test move (test on the update -> test on the
value), matched by STRUCTURE and applied only when Lean proves it.

The pass, for any kernel (no names, no hashes):
  1. Match (handshake MLIR): a compare `cmpi eq, F#j, K` where F is a 2-output fork of a value Y (the loop's update),
     K is the constant 1 (directly or through a fork of the constant), F's other output is used once, and every
     data input of Y's computation (through arithmetic ops) is an output of ONE fork N (the loop value n).
  2. Rewrite (the same edit as research's pre_eq2.py, located structurally): N gets one more output; a new constant 2
     (fired by a new source) is compared with it; F is deleted (its other reader reads Y); the freed constant-1 input
     is sunk.
  3. Check: `eq2_check.py IN OUT` (dfimport + scripts of proved local steps + Lean). Its identity library decides
     which compares may move: today `step(n) == 1` with the collatz step at any width >= 3 becomes `n == 2`.
Exit 0: OUT written AND proved equal to IN. 2: matched but refused (OUT = copy of IN). 3: no match (OUT = IN).
"""
import os, re, shutil, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))

ARITH = {'trunci', 'extui', 'extsi', 'andi', 'ori', 'xori', 'addi', 'subi', 'muli', 'shli', 'shrsi', 'shrui',
         'cmpi', 'select'}
DEF = re.compile(r'^    (%[\w.]+)(?::(\d+))? = (\w+)\b(.*)$')

def parse(src):
    lines = src.split('\n'); defs = {}
    for i, l in enumerate(lines):
        m = DEF.match(l)
        if not m: continue
        v, n, op, rest = m.groups()
        args = re.findall(r'%[\w.]+(?:#\d+)?', rest.split('{')[0])
        defs[v] = (i, op, args, int(n) if n else 1, l)
    return lines, defs

def uses(lines, tok, skip=None):
    pat = re.compile(re.escape(tok) + r'(?![\w#])')
    return [i for i, l in enumerate(lines) if i != skip and pat.search(l.split('{')[0] if '{' in l else l)
            and not (DEF.match(l) and DEF.match(l).group(1) == tok)]

def base(tok): return tok.split('#')[0]

def is_const(defs, tok, val=None):
    """tok is a constant (optionally of value val), directly or through forks of a constant."""
    d = defs.get(base(tok))
    if d is None: return False
    if d[1] == 'fork': return is_const(defs, d[2][0], val)
    if d[1] != 'constant': return False
    return val is None or re.search(r'value = %d : i\d+' % val, d[4]) is not None

def leaves(defs, tok, acc):
    """Data leaves of tok's arithmetic DAG: (fork value, index) pairs; constants are skipped."""
    if is_const(defs, tok): return True
    b = base(tok); d = defs.get(b)
    if d is None: return False
    if d[1] == 'fork':
        acc.add((b, tok)); return True
    if d[1] in ARITH: return all(leaves(defs, a, acc) for a in d[2])
    return False

def match(src):
    lines, defs = parse(src)
    for v, (i, op, args, n, l) in defs.items():
        if op != 'cmpi' or not re.search(r'= cmpi eq,', l) or len(args) != 2: continue
        ty = re.search(r': <(i\d+)>\s*$', l)
        if not ty: continue
        ty = ty.group(1)
        for a, k in (args, args[::-1]):
            if '#' not in a or not is_const(defs, k, 1): continue
            F = base(a); dF = defs.get(F)
            if not dF or dF[1] != 'fork' or dF[3] != 2: continue
            j = int(a.split('#')[1]); other = F + '#' + str(1 - j); Y = dF[2][0]
            if len(uses(lines, a, dF[0])) != 1 or len(uses(lines, other, dF[0])) != 1: continue
            acc = set()
            if not leaves(defs, Y, acc) or not acc: continue
            forks = {b for b, _ in acc}
            if len(forks) != 1: continue
            N = forks.pop(); dN = defs[N]
            if is_const(defs, N): continue
            return dict(lines=lines, cmp=(v, i, l, a, k), F=dF, Fv=F, other=other, Y=Y, N=N, dN=dN, ty=ty)
    return None

def fresh(src, stem):
    s = stem; i = 0
    while ('%' + s) in src or ('"%s"' % s) in src: i += 1; s = '%s_%d' % (stem, i)
    return s

def rewrite(src, M):
    lines = list(M['lines']); ty = M['ty']
    N, (iN, _, argsN, nN, lN) = M['N'], M['dN']
    vs, vc = fresh(src, 'eq2s'), fresh(src, 'eq2c')
    ns, nc, nk = fresh(src, 'sourceeq2'), fresh(src, 'constanteq2'), fresh(src, 'sinkeq2')
    lines[iN] = lN.replace('%s:%d = fork [%d]' % (N, nN, nN), '%s:%d = fork [%d]' % (N, nN + 1, nN + 1), 1)
    lines[iN] += ('\n    %%%s = source {handshake.bb = 1 : ui32, handshake.name = "%s"} : <>' % (vs, ns) +
                  '\n    %%%s = constant %%%s {handshake.bb = 1 : ui32, handshake.name = "%s", value = 2 : %s} : <>, <%s>'
                  % (vc, vs, nc, ty, ty))
    v, i, l, a, k = M['cmp']
    head, tail = l.split('{', 1)
    head = re.sub(r'cmpi eq, .*$', 'cmpi eq, %s#%d, %%%s ' % (N, nN, vc), head)
    lines[i] = head + '{' + tail
    iF = M['F'][0]
    lines[iF] = None
    pat = re.compile(re.escape(M['other']) + r'(?![\w#])')
    lines = [pat.sub(M['Y'], x) if x is not None else None for x in lines]
    out = '\n'.join(x for x in lines if x is not None)
    out = out.replace('    end {', '    sink %s {handshake.name = "%s"} : <%s>\n    end {' % (k, nk, ty), 1)
    return out

def main():
    args = sys.argv[1:]; extra = []
    for flag in ('--bdc', '--keep'):
        if flag in args: i = args.index(flag); extra += args[i:i + 2]; del args[i:i + 2]
    if len(args) != 2: print(__doc__); return 1
    inp, out = args
    src = open(inp).read()
    M = match(src)
    if M is None:
        shutil.copy(inp, out); print('eq2_pass: no match (OUT = IN)'); return 3
    cand = rewrite(src, M)
    tmp = tempfile.mkdtemp(prefix='eq2_pass_'); cf = os.path.join(tmp, 'cand.mlir'); open(cf, 'w').write(cand)
    r = subprocess.run([sys.executable, os.path.join(HERE, 'eq2_check.py'), inp, cf] + extra, capture_output=True,
                       text=True)
    print((r.stdout + r.stderr).strip().split('\n')[-1])
    if r.returncode == 0:
        shutil.copy(cf, out); print(f'eq2_pass: PROVED -- {out} written'); return 0
    shutil.copy(inp, out); print('eq2_pass: refused (OUT = IN)'); return 2

if __name__ == '__main__':
    sys.exit(main())
