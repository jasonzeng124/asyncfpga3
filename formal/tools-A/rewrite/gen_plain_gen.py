#!/usr/bin/env python3
"""gen_plain_gen.py NAME RS2_EVAL.txt [--cert] -- the graph-only plain-test proof (CountloopPlainGen) for another ring kernel.

NAME: the Ring module name (Horner, Quadrec, Varshift, Xorshift). RS2_EVAL.txt: Lean `#eval Formal.Rewrite.Ring.NAME.rs2`.
Writes formal/lean/Formal/Rewrite/Plain/<NAME>PlainGen.lean; with --cert, prints the PlainPass.Cert instead.

What the script finds (untrusted; every fact it relies on is re-checked in Lean by `decide +kernel` or by the
PairOK / RuleSafe obligations, so a wrong guess makes the Lean fail, not a wrong theorem):
- the TEST pair from patTest's parameters (fork e -> [d0, x], inc d0 -> d, test [x, k] -> c, fork of c, the branch on d);
- the GUARD pair: the branch whose true output is the ring's `ne` channel, back to the fork and the `sgt` compare;
- the channel classes by backward closure from what `agree` needs (x and k never INT_MAX) and what gDec needs
  (ne never INT_MIN): class 1 = NotMax, class 2 = NotMin, everything else unconstrained. Producers allowed: forks,
  muxes and non-pair branches (copy the class), width-1 extui (class 1), gDec (class 2 -> 1), the pair branches' true
  sides (their compares). Anything else on the closure is a failure, reported.
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
src = open(os.path.join(HERE, 'rules_iso.py')).read().replace('sys.exit(main())', '')
G = {}; exec(src, G); load = G['load']

def ins_outs(r):
    k = r[0]
    if k == 'comp': return list(r[1]), [r[2]]
    if k == 'fork': return [r[1]], list(r[2])
    if k == 'branch': return [r[1], r[2]], [r[3], r[4]]
    if k == 'mux': return [r[1]] + list(r[2]), [r[3]]
    if k == 'cm': return [r[1]], [r[2], r[3]]
    if k == 'sink': return [r[1]], []

def main():
    name, ev = sys.argv[1:3]
    rs = load(ev)
    ring = open(os.path.join(ROOT, f'formal/lean/Formal/Rewrite/Ring/{name}.lean')).read()
    pr = [int(x) for x in re.search(r'patRing : RingMap\.Pat rules rs1 ([\d ]+) fSlt', ring).group(1).split()]
    pt = [int(x) for x in re.search(r'patTest : Pat2 rs1 rs2 ([\d ]+) fInc', ring).group(1).split()]
    # RingMap.Pat ... lM lF lB lS lC lD sel ne ne' r r0 k nb nx cnd y c w
    ne, nep, rr, r0, kk, nb = pr[7], pr[8], pr[9], pr[10], pr[11], pr[12]
    # Pat2 lA lF lC e s s0 y c k e0 e1
    tA, tF, tC, te, ts, ts0, ty, tc, tk, te0, te1 = pt
    prod = {}
    for l, r in enumerate(rs):
        for o in ins_outs(r)[1]: prod[o] = l
    # test pair: fork tA: e -> [e0, e1]; comp tF [e0] s0; comp tC [e1, k] c; fork of c; branch on s0
    assert rs[tA] == ('fork', te, [te0, te1]), rs[tA]
    assert rs[tF][0] == 'comp' and rs[tF][1] == [te0] and rs[tF][2] == ts0
    assert rs[tC][0] == 'comp' and rs[tC][1] == [te1, tk] and rs[tC][2] == tc
    lKt = [l for l, r in enumerate(rs) if r[0] == 'fork' and r[1] == tc]; assert len(lKt) == 1; lKt = lKt[0]
    lBt = [l for l, r in enumerate(rs) if r[0] == 'branch' and r[2] == ts0]; assert len(lBt) == 1; lBt = lBt[0]
    test = dict(lF=tA, lA=tF, lC=tC, lK=lKt, lB=lBt, e=te, d0=te0, d=ts0, x=te1, c=tc, cb=rs[lBt][1], k=tk,
                t=rs[lBt][3], f=rs[lBt][4], os=rs[lKt][2], hasA='true', fA='fInc', F='fSltXor')
    # guard pair: branch with true output ne
    lBg = [l for l, r in enumerate(rs) if r[0] == 'branch' and r[3] == ne]; assert len(lBg) == 1; lBg = lBg[0]
    cbg, dg = rs[lBg][1], rs[lBg][2]
    lKg = [l for l, r in enumerate(rs) if r[0] == 'fork' and cbg in r[2]]; assert len(lKg) == 1; lKg = lKg[0]
    cg = rs[lKg][1]; lCg = prod[cg]; rc = rs[lCg]
    assert rc[0] == 'comp' and len(rc[1]) == 2, rc
    assert rc[3] == ('bin', ('cmpi', ('sgt',)), 32, ('var', 0), ('var', 1)), rc
    xg, kg = rc[1]
    lFg = [l for l, r in enumerate(rs) if r[0] == 'fork' and r[2] == [dg, xg]]; assert len(lFg) == 1; lFg = lFg[0]
    guard = dict(lF=lFg, lA=0, lC=lCg, lK=lKg, lB=lBg, e=rs[lFg][1], d0=dg, d=dg, x=xg, c=cg, cb=cbg, k=kg,
                 t=ne, f=rs[lBg][4], os=rs[lKg][2], hasA='false', fA='E.var 0',
                 F='E.bin (BOp.cmpi Pred.sgt) 32 (E.var 0) (E.var 1)')
    # class closure
    cls = {}; work = [(te1, 1), (tk, 1), (ne, 2)]; special = {}
    while work:
        ch, c = work.pop()
        if ch in cls:
            if cls[ch] != c: sys.exit(f'class conflict on {ch}')
            continue
        cls[ch] = c
        if ch in (0, 1, 2): sys.exit(f'argument channel {ch} needs class {c}')
        l = prod[ch]; r = rs[l]
        if l == lBt:
            if not (ch == test['t'] and c == 1): sys.exit(f'test branch output {ch} class {c}')
            continue
        if l == lBg:
            if not (ch == ne and c == 2): sys.exit(f'guard branch output {ch} class {c}')
            continue
        if r[0] == 'fork': work.append((r[1], c))
        elif r[0] == 'mux': work += [(d, c) for d in r[2]]
        elif r[0] == 'branch': work.append((r[2], c))
        elif r[0] == 'comp' and c == 1 and r[3] == ('un', ('extui',), 1, ('var', 0)) and len(r[1]) == 1:
            special[l] = 'extui'
        elif r[0] == 'comp' and c == 1 and r[3] == ('bin', ('addi',), 32, ('var', 0), ('lit', 4294967295)) \
                and r[1] == [ne]:
            special[l] = 'dec'; work.append((ne, 2))
        else: sys.exit(f'channel {ch} class {c}: producer {l} {r} not allowed')
    c1 = sorted(k for k, v in cls.items() if v == 1); c2 = sorted(k for k, v in cls.items() if v == 2)
    assert c2 == [ne], c2
    assert sorted(special.values()) == ['dec', 'extui'], special
    lExt = [l for l, v in special.items() if v == 'extui'][0]; lDec = [l for l, v in special.items() if v == 'dec'][0]
    extIn, extOut = rs[lExt][1][0], rs[lExt][2]

    if len(sys.argv) > 3 and sys.argv[3] == '--cert':
        f = dict(M=pr[0], F=pr[1], B=pr[2], S=pr[3], C=pr[4], sel=pr[6], ne=ne, **{"ne'": nep}, r=rr, r0=r0, k=kk,
                 nb=nb, nx=pr[13], cnd=pr[14], y=pr[15], c=pr[16], iw=pr[17], lb=tA, ld=tF, e=te, s=ts, s0=ts0,
                 e0=te0, e1=te1, gF=lFg, gC=lCg, gK=lKg, gB=lBg, ge=guard['e'], gd=dg, gx=xg, gc=cg, gcb=cbg, gk=kg,
                 gt=ne, gf=guard['f'], gos=guard['os'], tK=lKt, tB=lBt, tcb=test['cb'], tt=test['t'], tf=test['f'],
                 tos=test['os'], c1=c1, c2=c2)
        assert pr[15] == ty and pr[16] == tc and pr[11] == tk and pr[4] == tC
        print(f'def c{name} : Cert where')
        for a, b in f.items(): print(f'  {a} := {b}')
        return
    tpl = open(os.path.join(ROOT, 'formal/lean/Formal/Rewrite/Plain/CountloopPlainGen.lean')).read()
    s = tpl
    def sub(a, b, cnt=1):
        nonlocal s
        if s.count(a) != cnt: sys.exit(f'template: {a!r} occurs {s.count(a)} times, expected {cnt}')
        s = s.replace(a, b)
    low = name.lower()
    sub('import Formal.Rewrite.CountloopRewrite', f'import Formal.Rewrite.Ring.{name}')
    sub('Plain.CountloopPlainGen', f'Plain.{name}PlainGen', 3)
    sub('Formal.Rewrite.IncCmp Formal.Rewrite.CountloopRewrite', f'Formal.Rewrite.IncCmp Formal.Rewrite.Ring.{name}')
    sub('Formal.Rewrite.ChanInv Formal.Rewrite.CountloopHw', f'Formal.Rewrite.ChanInv Formal.Rewrite.Ring.{name}Hw')
    sub('the PLAIN loop test on countloop, from the graph alone (shard A, 2026-11-18)',
        f'the PLAIN loop test on {low}, from the graph alone (shard A, 2026-11-18; GENERATED by '
        f'formal/tools-A/rewrite/gen_plain_gen.py from CountloopPlainGen)')
    sub("(unlike `CountloopSame`, which goes through the C)", '(as `CountloopPlainGen` does for countloop)')
    sub("research's countloop fixture", f"research's {low} fixture")
    sub('(`rs2` of CountloopRewrite with', f'(`rs2` of Ring.{name} with')
    sub('**Not covered:** token level only; the tie of `rs2p` to `out/countloop_plain.mlir` is the rules_iso check (43 rules,\nisomorphic), not yet through `Rename` in Lean.',
        f'**Not covered:** token level only; the tie of `rs2p` to `out/{low}_plain.mlir` is `{name}PlainTie` (Rename).')
    sub('rs2.set 28 (.comp [69, 45] 53 fSlt)', f'rs2.set {tC} (.comp [{te1}, {tk}] {tc} fSlt)')
    sub('ch ∈ [19, 20, 21, 29, 30, 31, 32, 68, 69, 67, 43, 44, 45, 42] then 1 else if ch = 24 then 2',
        f'ch ∈ {c1} then 1 else if ch = {ne} then 2')
    sub('rs2p.length = 43', f'rs2p.length = {len(rs)}')
    def pair(p):
        return '\n'.join(f'  {k} := {p[k]}' for k in
            ['lF', 'lA', 'lC', 'lK', 'lB', 'e', 'd0', 'd', 'x', 'c', 'cb', 'k', 't', 'f', 'os', 'hasA', 'fA', 'F'])
    oldG = s[s.index('def pGuard : Pair where\n') + len('def pGuard : Pair where\n'):s.index('\n\ndef pTest')]
    sub(oldG, pair(guard))
    oldT = s[s.index('def pTest : Pair where\n') + len('def pTest : Pair where\n'):s.index('\n\ndef privB')]
    sub(oldT, pair(test))
    sub('change Q 24 v', f'change Q {ne} v')
    sub('change Q 29 (fInc.eval [v])', f'change Q {test["t"]} (fInc.eval [v])')
    sub('by_cases l8 : l = 8\n  · subst l8', f'by_cases l8 : l = {lExt}\n  · subst l8')
    sub('.comp [16] 19 (.un .extui 1 (.var 0))', f'.comp [{extIn}] {extOut} (.un .extui 1 (.var 0))', 2)
    sub('rs2[8]?', f'rs2[{lExt}]?')
    sub('by_cases l42 : l = 42\n  · subst l42', f'by_cases l42 : l = {lDec}\n  · subst l42')
    sub('.comp [24] 67 gDec', f'.comp [{ne}] {nep} gDec', 2)
    sub('rs2[42]?', f'rs2[{lDec}]?')
    sub('l == 8 || l == 42 || l == 12 || l == 30', f'l == {lExt} || l == {lDec} || l == {lBg} || l == {lBt}')
    sub('have h12 : l ≠ 12', f'have h12 : l ≠ {lBg}'); sub('have h30 : l ≠ 30', f'have h30 : l ≠ {lBt}')
    sub('(a b : Nat) (ha : Q 69 a) (hb : Q 45 b)', f'(a b : Nat) (ha : Q {te1} a) (hb : Q {tk} b)')
    sub('rs2[28]? = some (.comp [69, 45] 53 fSltXor)', f'rs2[{tC}]? = some (.comp [{te1}, {tk}] {tc} fSltXor)')
    sub('rs2p[28]? = some (.comp [69, 45] 53 fSlt)', f'rs2p[{tC}]? = some (.comp [{te1}, {tk}] {tc} fSlt)')
    sub('∀ l, l ≠ 28 → rs2p[l]? = rs2[l]?', f'∀ l, l ≠ {tC} → rs2p[l]? = rs2[l]?')
    out = os.path.join(ROOT, f'formal/lean/Formal/Rewrite/Plain/{name}PlainGen.lean')
    open(out, 'w').write(s)
    print(f'{name}: wrote {out}\n  guard {guard}\n  test {test}\n  class1 {c1} class2 {c2} extui@{lExt} dec@{lDec}')

if __name__ == '__main__':
    main()
