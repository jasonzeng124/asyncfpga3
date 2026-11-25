#!/usr/bin/env python3
"""ring_dec_route.py IN.mlir OUT.mlir [--only CMPNAME]   (shard A, 2026-11-20; UNTRUSTED edit, proof per kernel)
The plain loop-test move of ring_dec.py --plain, generalised to a bound that reaches the test through routing:
the test `cmpi P, F#a, B` with P in {slt, ult} (any width), F a 2-way fork of `addi I, 1` (1 a constant), and
B either a constant c read only by the test (it becomes c - 1; refused at the wrap point) or
B a value of the BOUND CLASS: the closure of channels that carry the same token as B through routing only
(fork outputs, br, cond_br data outputs, mux / merge outputs whose every data input is in the class or an entry).
Side conditions (anything else is refused):
  - every reader of a class channel is a routing node of the class, a sink, the test itself, or a cond_br's data input
    whose outputs are in the class or sunk -- the bound is never computed on, so carrying n - 1 cannot be observed
    except at the test;
  - the class is entered only through mux data inputs from outside it (the loop entries).
Edit: each entry e becomes `addi e, -1` (the class carries n - 1); the test reads I (forked before the increment):
`cmpi P, I, B`. NOT proved here: the result must be proved equal to the C per kernel (ringfuse_autoproof.sh /
exitcond_gate.sh style: translation validation); without that proof it must not be used.
Exit 0 rewrote (one test per run), 3 nothing matched. Prints what it refused and why."""
import re, sys
def main():
    a = sys.argv[1:]; only = None
    if '--only' in a: i = a.index('--only'); only = a[i + 1]; del a[i:i + 2]
    L = open(a[0]).read().split('\n')
    def defl(v):
        base = v.split('#')[0]
        for n, l in enumerate(L):
            if l is None: continue
            lhs = l.split('=')[0] if '=' in l else ''
            if re.search(re.escape(base) + r'(?::\d+)?(?![\w])', lhs): return n
        return None
    def readers(v):   # line numbers reading v as an operand
        out = []
        for n, l in enumerate(L):
            if l is None or '=' not in l and not l.strip().startswith(('sink', 'end')): 
                if l is None: continue
            rhs = l.split('=', 1)[1] if '=' in l and not l.strip().startswith(('sink', 'end')) else l
            rhs = rhs.split('{')[0] if '{' in rhs else rhs.split('[bb')[0]
            if re.search(re.escape(v) + r'(?![\w#])', rhs): out.append(n)
        return out
    def outs(n):      # result value names of line n (fork outputs expanded)
        l = L[n].strip(); lhs = l.split('=')[0].strip()
        m = re.match(r'(%\w+):(\d+)$', lhs)
        if m: return [f'{m.group(1)}#{i}' for i in range(int(m.group(2)))]
        return [x.strip() for x in lhs.split(',')]
    W = r'<i(\d+)>'
    for n0, l in enumerate(list(L)):
        m = re.match(r'^(\s*)(%\w+) = cmpi (slt|ult), (%\w+#\d+), (%\w+(?:#\d+)?) \{(.*)\} : <i(\d+)>$', l or '')
        if not m: continue
        ind, c, P, A_, B, attrs, w = m.groups()
        cname = re.search(r'handshake.name = "([^"]+)"', attrs).group(1)
        if only and cname != only: continue
        why = None
        sf = A_.split('#')[0]; nsf = defl(sf)
        ms = nsf is not None and re.match(r'^\s*' + re.escape(sf) + r':2 = fork \[2\] (%\w+(?:#\d+)?) ', L[nsf])
        if not ms: why = 'test lhs is not a 2-way fork'
        else:
            s = ms.group(1); ns = defl(s)
            ma = ns is not None and re.match(r'^\s*' + re.escape(s) + r' = addi (%\w+(?:#\d+)?), (%\w+) \{.*\} : <i' + w + r'>$', L[ns])
            if not ma: why = 'fork input is not an addi of the test width'
            else:
                I, one = ma.groups(); n1 = defl(one)
                mo = n1 is not None and re.match(r'^\s*' + re.escape(one) + r' = constant (%\w+(?:#\d+)?) \{.*value = 1 : i' + w + r'\}', L[n1])
                if not mo: why = 'step is not a constant 1'
        nB = defl(B); mk = nB is not None and re.match(r'^\s*' + re.escape(B) + r' = constant (%\w+(?:#\d+)?) \{(.*)value = (-?\d+) : i' + w + r'\}', L[nB])
        if why is None and mk and len(readers(B)) == 1:   # a constant bound read only by the test: c -> c - 1
            cval = int(mk.group(3)); ww = int(w); u = cval % (1 << ww)
            nv = (u - 1) % (1 << ww); nv = nv if nv < (1 << (ww - 1)) else nv - (1 << ww)   # MLIR prints signed
            if (P == 'ult' and u == 0) or (P == 'slt' and cval == -(1 << (ww - 1))): why = 'constant bound at the wrap point'
            else:
                L[nB] = L[nB].replace(f'value = {cval} : i{w}', f'value = {nv} : i{w}', 1)
                sf_other = sf + '#' + ('0' if A_.endswith('#1') else '1')
                for r in readers(sf_other):
                    L[r] = re.sub(re.escape(sf_other) + r'(?![\w#])', s, L[r], count=1)
                bba = re.search(r'handshake.bb = (\d+)', L[ns]).group(1); t = 'rr'
                L[ns] = (f'{ind}%{t}f:2 = fork [2] {I} {{handshake.bb = {bba} : ui32, handshake.name = "fork{t}f"}} : <i{w}>\n' +
                         L[ns].replace(f'= addi {I}, ', f'= addi %{t}f#0, ', 1))
                L[n0] = f'{ind}{c} = cmpi {P}, %{t}f#1, {B} {{{attrs}}} : <i{w}>'
                L[nsf] = None
                open(a[1], 'w').write('\n'.join(x for x in L if x is not None))
                print(f'rewrote {cname}: test before the increment ({P} i{w}); constant bound {cval} -> {nv}')
                return 0
        if why is None:   # the bound class, by closure backward and forward through routing
            cls, entries, todo, seen = set(), [], [B], set()
            while todo and why is None:
                v = todo.pop()
                if v in seen: continue
                seen.add(v); cls.add(v)
                nd = defl(v); dl = L[nd].strip() if nd is not None else ''
                # backward: what defines v
                if re.match(r'%[\w:]+ = fork ', dl) or re.match(r'%\w+ = br ', dl):
                    src = re.search(r'= (?:fork \[\d+\]|br) (%\w+(?:#\d+)?)', dl).group(1); todo.append(src)
                elif re.match(r'%\w+, %\w+ = cond_br ', dl):
                    todo.append(re.search(r'cond_br %\w+(?:#\d+)?, (%\w+(?:#\d+)?)', dl).group(1))
                elif re.match(r'%\w+ = mux ', dl):
                    for d in re.search(r'\[([^\]]*)\]', dl.split('mux', 1)[1]).group(1).split(','):
                        todo.append(d.strip())
                elif re.match(r'%\w+ = merge ', dl):
                    for d in dl.split('merge', 1)[1].split('{')[0].split(','):
                        todo.append(d.strip())
                else:
                    entries.append(v); cls.discard(v); continue   # an outside value: a candidate entry
                # forward: every reader must be routing, a sink, or the test
                for r in readers(v):
                    rl = L[r].strip()
                    if r == n0: continue
                    if rl.startswith('sink '): continue
                    if re.match(r'%[\w:]+ = fork ', rl) or re.match(r'%\w+ = br ', rl):
                        todo.extend(outs(r)); continue
                    mc = re.match(r'(%\w+), (%\w+) = cond_br (%\w+(?:#\d+)?), (%\w+(?:#\d+)?)', rl)
                    if mc and mc.group(4) == v: todo.extend([mc.group(1), mc.group(2)]); continue
                    mm = re.match(r'(%\w+) = mux (%\w+(?:#\d+)?) \[', rl)
                    if mm and mm.group(2) != v: todo.append(mm.group(1)); continue
                    mg = re.match(r'(%\w+) = merge ', rl)
                    if mg: todo.append(mg.group(1)); continue
                    why = f'bound class value {v} is read by a computing op: {rl[:60]}'
            if why is None:
                # entries: values defined outside the class that feed a class mux / routing
                ent = [e for e in entries if e not in cls]
                ent = sorted(set(ent))
                if not ent: why = 'no entry into the bound class'
                elif any(e.startswith('%arg') for e in ent) and False: pass
        if why is not None:
            print(f'refused {cname}: {why}'); continue
        # each entry must be a mux data input of the class (loop entry); find those uses
        uses = []   # (line, value): where to decrement; only on edges whose consumer is wholly in the class
        todo2 = list(ent)
        while todo2:
            e = todo2.pop()
            for r in readers(e):
                rl = L[r]
                if r == n0 or rl.strip().startswith('sink '): continue
                o = outs(r) if '=' in rl else []
                if o and all(x in cls for x in o): uses.append((r, e))
                elif o and any(x in cls for x in o) and re.match(r'\s*%[\w:]+ = fork ', rl):
                    todo2.extend(x for x in o if x in cls)   # a mixed fork: decrement on its class outputs only
                elif o and any(x in cls for x in o):
                    mc = re.match(r'\s*(%\w+), (%\w+) = cond_br (%\w+(?:#\d+)?), (%\w+(?:#\d+)?)', rl)
                    if mc and mc.group(4) == e: uses.append((r, e))   # a guard's data input: its other output is sunk
        if not uses: print(f'refused {cname}: entries {ent} do not feed the class'); continue
        t = 'rr'; k = 0
        for r, e in uses:
            bb = re.search(r'handshake.bb = (\d+)', L[r]).group(1); ind2 = re.match(r'(\s*)', L[r]).group(1)
            A = lambda nm: '{handshake.bb = %s : ui32, handshake.name = "%s"}' % (bb, nm)
            nm = f'%{t}{k}'; k += 1
            pre = (f'{ind2}{nm}s = source {A("source"+nm[1:])} : <>\n'
                   f'{ind2}{nm}c = constant {nm}s {{handshake.bb = {bb} : ui32, handshake.name = "constant{nm[1:]}", value = -1 : i{w}}} : <>, <i{w}>\n'
                   f'{ind2}{nm}d = addi {e}, {nm}c {A("addi"+nm[1:])} : <i{w}>\n')
            L[r] = pre + re.sub(re.escape(e) + r'(?![\w#])', nm + 'd', L[r], count=1)
        # the test reads I: fork I before the increment
        sf_other = sf + '#' + ('0' if A_.endswith('#1') else '1')
        for r in readers(sf_other):
            L[r] = re.sub(re.escape(sf_other) + r'(?![\w#])', s, L[r], count=1)
        bba = re.search(r'handshake.bb = (\d+)', L[ns]).group(1)
        L[ns] = (f'{ind}%{t}f:2 = fork [2] {I} {{handshake.bb = {bba} : ui32, handshake.name = "fork{t}f"}} : <i{w}>\n' +
                 L[ns].replace(f'= addi {I}, ', f'= addi %{t}f#0, ', 1))
        L[n0] = f'{ind}{c} = cmpi {P}, %{t}f#1, {B} {{{attrs}}} : <i{w}>'
        L[nsf] = None
        open(a[1], 'w').write('\n'.join(x for x in L if x is not None))
        print(f'rewrote {cname}: test before the increment ({P} i{w}); bound class of {len(cls)} channels, entries {[e for _, e in uses]}')
        return 0
    open(a[1], 'w').write('\n'.join(x for x in L if x is not None)); return 3
sys.exit(main())
