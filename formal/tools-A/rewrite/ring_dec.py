#!/usr/bin/env python3
"""ring_dec.py IN.mlir OUT.mlir [--only CMPNAME] [--plain]

--plain: the test is plain `slt(i, m)` with no correction (exact only under the loop's entry invariant). Covered by
`Formal.Rewrite.PlainPass` for every graph whose certificate passes its `check`; run it through `plain_pass.py`, which
applies it only when Lean proves it for that MLIR.
 -- the loop test `slt(i + 1, n)` with n on a ring, rewritten so that
the test does not wait for the increment (shard A, 2026-11-18).

Pattern (every match is checked, anything else is refused):
    %r = mux %sel [NE, %nb]          (2 inputs, entry first)      %rf:2 = fork [2] %r
    %nb, %nx = cond_br %cnd, %rf#j   with `sink %nx`              the other fork output %rf#k is read by the test
    %s = addi I, %one                (%one = constant %src, value 1, %src a `source`)
    %sf:2 = fork [2] %s              one output read by the test, the other by anything
    %c = cmpi slt, %sf#.., %rf#k     (all i32)
Rewrite (proved: formal/lean/Formal/Rewrite/{RingMap,IncCmp2,SplitComp,IncCmpArith}.lean):
    the ring carries m = n - 1:  %d = addi NE, -1 (a new source/constant) and the mux reads %d;
    the test reads I:            %f:2 = fork I ; %s = addi %f#0, %one ; (%sf removed, its other reader reads %s)
    %c = (slt(i, m) xor (i == INT_MAX)) xor (m == INT_MAX)   on forks of %f#1 and %rf#k.
Output is byte-identical to the input if nothing matches. Prints what it did and what it refused.
"""
import re, sys

def main():
    args = sys.argv[1:]
    only = None
    plain = '--plain' in args
    if plain: args.remove('--plain')
    if '--only' in args:
        i = args.index('--only'); only = args[i + 1]; del args[i:i + 2]
    src = open(args[0]).read()
    lines = src.split('\n')
    def find_def(v):
        base = v.split('#')[0]
        pat = re.compile(r'^\s*' + re.escape(base) + r'(?::\d+)?\s*=|^\s*%\w+\s*,\s*' + re.escape(base) + r'\s*=|^\s*' + re.escape(base) + r'\s*,')
        for n, l in enumerate(lines):
            if pat.search(l): return n
        return None
    def uses(v):
        return [n for n, l in enumerate(lines) if re.search(re.escape(v) + r'(?![\w#])', l.split('{')[0]) and find_def(v) != n]
    def name_of(n): return re.search(r'handshake.name = "([^"]+)"', lines[n]).group(1)
    done = 0; k = 0
    for n0, l in enumerate(list(lines)):
        m = re.match(r'^(\s*)(%\w+) = cmpi slt, (%\w+#\d+), (%\w+#\d+) \{(.*)\} : <i32>$', l)
        if not m: continue
        ind, c, a, b, attrs = m.groups()
        cname = re.search(r'handshake.name = "([^"]+)"', attrs).group(1)
        if only and cname != only: continue
        why = None
        # a = %sf#x, fork [2] of %s = addi I, %one
        sf = a.split('#')[0]; nsf = find_def(sf)
        ms = nsf is not None and re.match(r'^\s*' + re.escape(sf) + r':2 = fork \[2\] (%\w+) ', lines[nsf])
        if not ms: why = 'test lhs is not a 2-way fork'
        else:
            s = ms.group(1); ns = find_def(s)
            ma = ns is not None and re.match(r'^\s*' + re.escape(s) + r' = addi (%\w+(?:#\d+)?), (%\w+) \{.*\} : <i32>$', lines[ns])
            if not ma: why = 'fork input is not an i32 addi'
            else:
                I, one = ma.groups(); n1 = find_def(one)
                mo = n1 is not None and re.match(r'^\s*' + re.escape(one) + r' = constant (%\w+) \{.*value = 1 : i32\}', lines[n1])
                if not mo: why = 'addi step is not a source constant 1'
                else:
                    srcv = mo.group(1); nsrc = find_def(srcv)
                    if nsrc is None or ' = source ' not in lines[nsrc]: why = 'constant 1 not fired by a source'
        if why is None:
            # b = %rf#k, fork [2] of mux output
            rf = b.split('#')[0]; nrf = find_def(rf)
            mr = nrf is not None and re.match(r'^\s*' + re.escape(rf) + r':2 = fork \[2\] (%\w+) ', lines[nrf])
            if not mr: why = 'test rhs is not a 2-way fork'
            else:
                r = mr.group(1); nr = find_def(r)
                mm = nr is not None and re.match(r'^(\s*)' + re.escape(r) + r' = mux (%\w+#?\d*) \[(%\w+(?:#\d+)?), (%\w+(?:#\d+)?)\] (\{.*\}) : <i1>, \[<i32>, <i32>\] to <i32>$', lines[nr])
                if not mm: why = 'ring value is not a 2-input i32 mux'
                else:
                    sel, NE, nb = mm.group(2), mm.group(3), mm.group(4)
                    other = rf + '#' + ('0' if b.endswith('#1') else '1')
                    ub = uses(other)
                    mb = len(ub) == 1 and re.match(r'^\s*(%\w+), (%\w+) = cond_br (%\w+(?:#\d+)?), ' + re.escape(other) + r' ', lines[ub[0]])
                    if not mb or mb.group(1) != nb: why = 'ring fork other output is not the cond_br feeding the mux back edge'
                    else:
                        nx = mb.group(2); ux = uses(nx)
                        if len(ux) != 1 or not lines[ux[0]].strip().startswith('sink ' + nx + ' '): why = 'ring exit is not sunk'
                        elif len(uses(b)) != 1: why = 'ring value read by more than the test'
        if why is not None:
            print(f"refused {cname}: {why}"); continue
        bb = re.search(r'handshake.bb = (\d+)', lines[n0]).group(1)
        bbne = re.search(r'handshake.bb = (\d+)', lines[nr]).group(1)
        t = f'rd{k}'; k += 1
        A = lambda nm, b_=bb: '{handshake.bb = %s : ui32, handshake.name = "%s"}' % (b_, nm)
        sf_other = sf + '#' + ('0' if a.endswith('#1') else '1')
        # edits, from the bottom up so line numbers stay valid
        if plain:
            lines[n0] = f'{ind}{c} = cmpi slt, %{t}f#1, {b} {{{attrs}}} : <i32>'
        else:
          lines[n0] = (f'{ind}%{t}i:2 = fork [2] %{t}f#1 {A("fork"+t+"i")} : <i32>\n'
                     f'{ind}%{t}m:2 = fork [2] {b} {A("fork"+t+"m")} : <i32>\n'
                     f'{ind}%{t}lt = cmpi slt, %{t}i#0, %{t}m#0 {{{attrs}}} : <i32>\n'
                     f'{ind}%{t}s1 = source {A("source"+t+"a")} : <>\n'
                     f'{ind}%{t}k1 = constant %{t}s1 {{handshake.bb = {bb} : ui32, handshake.name = "constant{t}a", value = 2147483647 : i32}} : <>, <i32>\n'
                     f'{ind}%{t}s2 = source {A("source"+t+"b")} : <>\n'
                     f'{ind}%{t}k2 = constant %{t}s2 {{handshake.bb = {bb} : ui32, handshake.name = "constant{t}b", value = 2147483647 : i32}} : <>, <i32>\n'
                     f'{ind}%{t}ei = cmpi eq, %{t}i#1, %{t}k1 {A("cmpi"+t+"i")} : <i32>\n'
                     f'{ind}%{t}em = cmpi eq, %{t}m#1, %{t}k2 {A("cmpi"+t+"m")} : <i32>\n'
                     f'{ind}%{t}x = xori %{t}lt, %{t}ei {A("xori"+t+"a")} : <i1>\n'
                     f'{ind}{c} = xori %{t}x, %{t}em {A("xori"+t+"b")} : <i1>')
        for u in uses(sf_other):
            lines[u] = re.sub(re.escape(sf_other) + r'(?![\w#])', s, lines[u], count=1)
        lines[nsf] = None
        bba = re.search(r'handshake.bb = (\d+)', lines[ns]).group(1)
        lines[ns] = (f'{ind}%{t}f:2 = fork [2] {I} {A("fork"+t+"f", bba)} : <i32>\n' +
                     lines[ns].replace(f'= addi {I}, ', f'= addi %{t}f#0, ', 1))
        lines[nr] = (f'{ind}%{t}ds = source {A("source"+t+"d", bbne)} : <>\n'
                     f'{ind}%{t}dc = constant %{t}ds {{handshake.bb = {bbne} : ui32, handshake.name = "constant{t}d", value = -1 : i32}} : <>, <i32>\n'
                     f'{ind}%{t}dd = addi {NE}, %{t}dc {A("addi"+t+"d", bbne)} : <i32>\n' +
                     lines[nr].replace(f'[{NE}, {nb}]', f'[%{t}dd, {nb}]', 1))
        lines[:] = [x for x in lines if x is not None]
        print(f"rewrote {cname}: test before the increment (ring n -> n-1, {'PLAIN' if plain else 'corrected'} slt)")
        done += 1
        break  # one rewrite per run: line numbers moved; run again for the next one
    open(args[1], 'w').write('\n'.join(lines))
    return 0

sys.exit(main())
