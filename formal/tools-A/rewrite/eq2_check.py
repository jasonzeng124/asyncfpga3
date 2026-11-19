#!/usr/bin/env python3
"""eq2_check.py IN.mlir OUT.mlir [--keep DIR] [--bdc BDCDIR] -- is OUT, a loop-test rewrite of IN (the test moved
from the loop's UPDATE to the loop's VALUE, as research's pre_eq2.py does), proved equal to IN?

One command, from a clean checkout of claude/formal (after formal/setup.sh). Translation validation with a general
checker; nothing in it is specific to a kernel's name or file:
  1. dfimport (formal/tools/dfimport/mlir2lean.py: bdc's own parser and fusion plan) of IN and of OUT.
  2. Untrusted planner (this file): a script of local steps for each import (Formal.Rewrite.Steps.Script):
       IN : fold the update's region into one comp (reorder / absorb / forder / forksplit / forkjoin), move the fork
            after the update before it (forkcomm), fold the test's copy of the update into the test (absorb), replace
            the folded test by its library identity (ident; today: the collatz test, any width >= 3), drop dead sinks;
       OUT: split the test's branch off the fork (forder / forksplit), fold the update's region the same way, drop.
     and the renumbering between the two normal forms (rules_iso.py).
  3. One Lean file: `runScript rulesIn s1 = some r1`, `runScript rulesOut s2 = some r2`, `renCheck r1.1 r2.1 P Ti`
     (all by decide +kernel), and pass_forward / pass_backward from `runScript_sound` (any rule list, any accepted
     script): every complete run of IN's graph from tokens on the inputs only has a complete run of OUT's graph from
     the same inputs with the same result tokens, and vice versa. Compiled with `lake env lean`; `#print axioms` must
     show only propext, Classical.choice, Quot.sound.
Exit 0: PROVED. Exit 2: refused (no plan found, or Lean rejected it). Exit 3: IN and OUT import to the same rules.
--bdc BDCDIR: dfimport reads bdc from BDCDIR (e.g. research's tree); the environment (BDC_AUTO, ...) is passed through.
NOT covered: dfimport itself (MLIR -> rules) is trusted Python; nothing below the token level.
"""
import os, re, shutil, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
LEAN = os.path.join(ROOT, 'formal', 'lean')
sys.path.insert(0, HERE)
import gen_plain_gen as G  # noqa: E402
import plain_pass as PP    # noqa: E402

# ---------- mirror of the Lean definitions (only to plan; Lean re-evaluates everything) ----------
def subst(e, sig):
    k = e[0]
    if k == 'var': return sig[e[1]] if e[1] < len(sig) else ('lit', 0)
    if k == 'lit': return e
    if k == 'un': return ('un', e[1], e[2], subst(e[3], sig))
    if k == 'bin': return ('bin', e[1], e[2], subst(e[3], sig), subst(e[4], sig))
    if k == 'sel': return ('sel', subst(e[1], sig), subst(e[2], sig), subst(e[3], sig))
    raise ValueError(e)

def absorbE(nb, na, f, g):
    return subst(g, [('var', i) for i in range(nb)] + [subst(f, [('var', nb + j) for j in range(na)])])

def allZero(cs, g): return subst(g, [('var', 0)] * len(cs))
def pos(l, c): return l.index(c) if c in l else len(l)
def reindex(ins, ins2, F): return subst(F, [('var', pos(ins2, c)) for c in ins])

def colLhs(w):
    return ('bin', ('cmpi', ('eq',)), w,
            ('sel', ('bin', ('cmpi', ('eq',)), 1, ('bin', ('andi',), 1, ('un', ('trunci',), 1, ('var', 0)), ('lit', 1)), ('lit', 0)),
             ('bin', ('shrsi',), w, ('var', 0), ('lit', 1)),
             ('bin', ('addi',), w, ('bin', ('addi',), w, ('var', 0), ('bin', ('shli',), w, ('var', 0), ('lit', 1))), ('lit', 1))),
            ('lit', 1))

def colRhs(w): return ('bin', ('cmpi', ('eq',)), w, ('var', 0), ('lit', 2))

def ins_of(r):
    k = r[0]
    if k == 'comp': return list(r[1])
    if k in ('fork', 'cm', 'sink'): return [r[1]]
    if k == 'branch': return [r[1], r[2]]
    if k == 'mux': return [r[1]] + list(r[2])
    raise ValueError(r)

def outs_of(r):
    k = r[0]
    if k == 'comp': return [r[2]]
    if k == 'fork': return list(r[2])
    if k == 'branch': return [r[3], r[4]]
    if k == 'mux': return [r[3]]
    if k == 'cm': return [r[2], r[3]]
    if k == 'sink': return []
    raise ValueError(r)

def writers(rs, c): return [l for l, r in enumerate(rs) if c in outs_of(r)]
def readers(rs, c): return [l for l, r in enumerate(rs) for x in ins_of(r) if x == c]
def maxch(rs): return max([c for r in rs for c in ins_of(r) + outs_of(r)] + [0])

class Plan:
    def __init__(self, rs): self.rs = list(rs); self.steps = []; self.sinks = []; self.pre = []; self.chg = []

    def do(self, st):
        rs = self.rs; k = st[0]
        if k == 'absorb':
            _, lp, lq = st; rp, rq = rs[lp], rs[lq]
            assert rp[0] == 'comp' and rq[0] == 'comp' and rq[1][-1] == rp[2], st
            bs = rq[1][:-1]; a = rp[1]
            rs[lp] = ('sink', rp[2]); rs[lq] = ('comp', bs + a, rq[2], absorbE(len(bs), len(a), rp[3], rq[3]))
            self.sinks.append(lp); self.pre += [rp[2]]; self.chg += [rp[2]] + list(a)
        elif k == 'forkjoin':
            _, lf, lc = st; rf, rc = rs[lf], rs[lc]
            assert rf[0] == 'fork' and rc[0] == 'comp' and list(rc[1]) == list(rf[2]), st
            rs[lf] = ('comp', [rf[1]], rc[2], allZero(rf[2], rc[3])); rs[lc] = ('sink', rf[2][0])
            self.sinks.append(lc); self.pre += list(rf[2]); self.chg += list(rf[2])
        elif k == 'forksplit':
            _, lf, kk, e = st; rf = rs[lf]
            rs[lf] = ('fork', rf[1], [e] + rf[2][kk:]); rs.append(('fork', e, rf[2][:kk]))
            self.pre += [e]; self.chg += [e]
        elif k == 'forkcomm':
            _, lc, lf, x0, x1 = st; rc, rf = rs[lc], rs[lf]
            assert rc[0] == 'comp' and len(rc[1]) == 1 and rf[0] == 'fork' and rf[1] == rc[2] and len(rf[2]) == 2, st
            rs[lc] = ('fork', rc[1][0], [x0, x1]); rs[lf] = ('comp', [x0], rf[2][0], rc[3])
            rs.append(('comp', [x1], rf[2][1], rc[3]))
            self.pre += [rf[1], x0, x1]; self.chg += [rf[1], x0, x1]
        elif k == 'reorder':
            _, l, ins2 = st; r = rs[l]; rs[l] = ('comp', list(ins2), r[2], reindex(r[1], ins2, r[3]))
        elif k == 'forder':
            _, l, os2 = st; r = rs[l]; rs[l] = ('fork', r[1], list(os2))
        elif k == 'ident':
            _, l, w = st; r = rs[l]; assert r[3] == colLhs(w), st; rs[l] = ('comp', r[1], r[2], colRhs(w))
        elif k == 'drop':
            _, l = st; assert rs[l][0] == 'sink'; self.pre += [rs[l][1]]; del rs[l]
        self.steps.append(st)

    def collapse(self, L):
        """Fold the single-input tree region ending at comp L into one comp; return its label."""
        while True:
            r = self.rs[L]; ins = list(r[1]); done = True
            for i in ins:
                W = writers(self.rs, i)
                if (len(W) == 1 and W[0] != L and self.rs[W[0]][0] == 'comp' and len(self.rs[W[0]][1]) >= 1
                        and readers(self.rs, i) == [L]):
                    ins2 = [c for c in ins if c != i] + [i]
                    if ins2 != ins: self.do(('reorder', L, ins2))
                    self.do(('absorb', W[0], L)); done = False; break
            if done: break
        r = self.rs[L]; ins = list(r[1])
        W = {w for i in ins for w in writers(self.rs, i)}
        assert len(W) == 1, 'region inputs not from one fork'
        X = W.pop(); rf = self.rs[X]
        assert rf[0] == 'fork' and set(ins) <= set(rf[2]) and all(readers(self.rs, i) == [L] for i in ins), 'not a fork region'
        os_ = list(rf[2])
        if set(os_) == set(ins):
            if ins != os_: self.do(('reorder', L, os_))
            self.do(('forkjoin', X, L)); return X
        rest = [c for c in os_ if c not in ins]
        if os_ != ins + rest: self.do(('forder', X, ins + rest))
        e = maxch(self.rs) + 1; E = len(self.rs)
        self.do(('forksplit', X, len(ins), e))
        self.do(('forkjoin', E, L)); return E

    def drops(self):
        for l in sorted(set(self.sinks), reverse=True): self.do(('drop', l))

def plan_in(rs):
    """IN: the test reads a fork of the update."""
    for F, rf in enumerate(rs):
        if rf[0] != 'fork' or len(rf[2]) != 2: continue
        Ws = writers(rs, rf[1])
        if len(Ws) != 1 or rs[Ws[0]][0] != 'comp': continue
        for t in rf[2]:
            R = readers(rs, t)
            if len(R) != 1 or rs[R[0]][0] != 'comp' or rs[R[0]][1] != [t]: continue
            T = R[0]; H = rs[T][3]
            if not (H[0] == 'bin' and H[1] == ('cmpi', ('eq',)) and H[3] == ('var', 0) and H[4] == ('lit', 1)): continue
            w = H[2]
            try:
                p = Plan(rs); Lc = p.collapse(Ws[0])
                x0 = maxch(p.rs) + 1; x1 = x0 + 1; n0 = len(p.rs)
                p.do(('forkcomm', Lc, F, x0, x1))
                p.do(('absorb', n0 if t == rf[2][1] else F, T))
                if p.rs[T][3] != colLhs(w): continue
                p.do(('ident', T, w)); p.drops()
                return p
            except AssertionError:
                continue
    return None

def plan_out(rs):
    """OUT: the test reads a fork output of the loop value directly."""
    for T, rt in enumerate(rs):
        if rt[0] != 'comp' or len(rt[1]) != 1: continue
        w = rt[3][2] if rt[3][0] == 'bin' else None
        if w is None or rt[3] != colRhs(w): continue
        t = rt[1][0]; Wt = writers(rs, t)
        if len(Wt) != 1 or rs[Wt[0]][0] != 'fork': continue
        X = Wt[0]; os_ = list(rs[X][2])
        if readers(rs, t) != [T] or len(os_) < 3: continue
        region = [c for c in os_ if c != t]
        # candidate region roots: comps fed (transitively, through single-reader comps) by the region's channels
        cands = []
        frontier = list(region); seen = set()
        while frontier:
            c = frontier.pop()
            for l in readers(rs, c):
                if l in seen or rs[l][0] != 'comp': continue
                seen.add(l); cands.append(l); frontier.append(rs[l][2])
        for L in cands:
            try:
                p = Plan(rs)
                if os_ != region + [t]: p.do(('forder', X, region + [t]))
                e = maxch(p.rs) + 1; E = len(p.rs)
                p.do(('forksplit', X, len(region), e))
                Lc = p.collapse(L)
                if Lc != E: continue
                p.drops()
                return p
            except AssertionError:
                continue
    return None

def ser_step(st):
    k = st[0]; a = st[1:]
    def s(x): return '[' + ', '.join(map(str, x)) + ']' if isinstance(x, list) else str(x)
    return '.' + k + ' ' + ' '.join(s(x) for x in a)

def lits(p1, p2):
    return dict(nf1=PP.ser_rules(p1.rs), nf2=PP.ser_rules(p2.rs), pre1=p1.pre, chg1=p1.chg, pre2=p2.pre, chg2=p2.chg)

def refuse(why):
    print('eq2_check: REFUSED -- ' + why); return 2

def main():
    args = sys.argv[1:]; keep = None
    if '--keep' in args: i = args.index('--keep'); keep = args[i + 1]; del args[i:i + 2]
    if '--bdc' in args: i = args.index('--bdc'); PP.BDCDIR = args[i + 1]; del args[i:i + 2]
    if len(args) != 2: print(__doc__); return 1
    inp, out = args
    tmp = keep or tempfile.mkdtemp(prefix='eq2_check_'); os.makedirs(tmp, exist_ok=True)
    rc = run(inp, out, tmp)
    if rc == 0: print(f'eq2_check: PROVED -- {out} is equal to {inp} (Lean: {tmp}/Eq2CheckRun.lean; axioms propext, '
                      'Classical.choice, Quot.sound)')
    return rc

def run(inp, out, tmp):
    fi, fo = os.path.join(tmp, 'In.lean'), os.path.join(tmp, 'Out.lean')
    Ri, Ni, oi, nai = PP.dfimport(inp, fi, 'Eq2In')
    Ro, No, oo, nao = PP.dfimport(out, fo, 'Eq2Out')
    if Ri == Ro: print('eq2_check: IN and OUT import to the same rules'); return 3
    if nai != nao: return refuse('IN and OUT have different numbers of inputs')
    if oi is None or oo is None: return refuse('no data output channel (chOut) in the import')
    p1 = plan_in(Ri)
    if p1 is None: return refuse('no plan for IN (no test on a forked update whose folded form is a library identity)')
    p2 = plan_out(Ro)
    if p2 is None: return refuse('no plan for OUT')
    n1, n2 = os.path.join(tmp, 'nf1.lean'), os.path.join(tmp, 'nf2.lean')
    open(n1, 'w').write('def rules : List Rule := ' + PP.ser_rules(p1.rs) + '\n')
    open(n2, 'w').write('def rules : List Rule := ' + PP.ser_rules(p2.rs) + '\n')
    mp = os.path.join(tmp, 'maps.json')
    ri = subprocess.run([sys.executable, os.path.join(HERE, 'rules_iso.py'), n1, n2, mp], capture_output=True, text=True)
    if ri.returncode != 0: return refuse('the two normal forms are not the same graph: ' + ri.stdout[-300:])
    import json
    m = json.load(open(mp))
    ch = {int(a): b for a, b in m['chan'].items()}; ru = {int(a): b for a, b in m['rule'].items()}
    K = max(list(ch) + list(ch.values())) + 1
    freeA = [c for c in range(K) if c not in ch]; freeB = [c for c in range(K) if c not in set(ch.values())]
    for a, b in zip(freeA, freeB): ch[a] = b
    P = [ch[c] for c in range(K)]; Pi = [0] * K
    for a, b in ch.items(): Pi[b] = a
    R = len(ru); T = [ru[l] for l in range(R)]; Ti = [0] * R
    for a, b in ru.items(): Ti[b] = a
    na = nai
    s1 = '[' + ', '.join(ser_step(s) for s in p1.steps) + ']'
    s2 = '[' + ', '.join(ser_step(s) for s in p2.steps) + ']'
    lean = TEMPLATE.format(inp=os.path.abspath(inp), out=os.path.abspath(out), rin=PP.ser_rules(Ri),
                           rout=PP.ser_rules(Ro), s1=s1, s2=s2, P=P, Pi=Pi, T=T, Ti=Ti, NA=na, oi=oi, oo=oo,
                           **lits(p1, p2))
    lf = os.path.join(tmp, 'Eq2CheckRun.lean'); open(lf, 'w').write(lean)
    env = dict(os.environ); env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')
    b = subprocess.run(['lake', 'build', 'Formal.Rewrite.Steps.ScriptSound', 'Formal.Rewrite.Rename'], cwd=LEAN,
                       env=env, capture_output=True, text=True)
    if b.returncode != 0: return refuse('lake build of Steps.ScriptSound failed: ' + b.stdout[-400:])
    c = subprocess.run(['lake', 'env', 'lean', lf], cwd=LEAN, env=env, capture_output=True, text=True)
    txt = c.stdout + c.stderr
    open(os.path.join(tmp, 'lean.log'), 'w').write(txt)
    ax = re.findall(r"depends on axioms: \[([^\]]*)\]", txt)
    ok = (c.returncode == 0 and 'error' not in txt and 'sorry' not in txt and len(ax) == 2 and
          all(sorted(a.replace(' ', '').split(',')) == ['Classical.choice', 'Quot.sound', 'propext'] for a in ax))
    if not ok: return refuse(f'Lean rejected (rc {c.returncode}); see {tmp}/lean.log')
    return 0

TEMPLATE = '''import Formal.Rewrite.Steps.ScriptSound
import Formal.Rewrite.Rename

/-! GENERATED by formal/tools-A/rewrite/eq2_check.py.
IN:  {inp}
OUT: {out}
`rulesIn` / `rulesOut` are dfimport's imports of IN / OUT. -/

namespace Eq2CheckRun
open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp Formal.Rewrite.Steps

def rulesIn : List Rule := {rin}

def rulesOut : List Rule := {rout}

def s1 : List Step := {s1}
def s2 : List Step := {s2}

def nf1 : List Rule := {nf1}
def nf2 : List Rule := {nf2}
def r1 : Res := (nf1, {pre1}, {chg1})
def r2 : Res := (nf2, {pre2}, {chg2})
theorem h1 : runScript rulesIn s1 = some r1 := by decide +kernel
theorem h2 : runScript rulesOut s2 = some r2 := by decide +kernel

def P : List Nat := {P}
def Pi : List Nat := {Pi}
def T : List Nat := {T}
def Ti : List Nat := {Ti}
theorem hP : fpCheck P Pi = true := by decide +kernel
theorem hPi : fpCheck Pi P = true := by decide +kernel
theorem hT : fpCheck T Ti = true := by decide +kernel
theorem hTi : fpCheck Ti T = true := by decide +kernel
theorem hRen : renCheck r1.1 r2.1 P Ti = true := by decide +kernel

theorem pre1_int : ∀ c ∈ r1.2.1, {NA} ≤ c := by decide +kernel
theorem pre2_int : ∀ c ∈ r2.2.1, {NA} ≤ c := by decide +kernel
theorem out1 : {oi} ∉ r1.2.2 := by decide +kernel
theorem out2 : {oo} ∉ r2.2.2 := by decide +kernel
theorem out_maps : fp P {oi} = {oo} := by decide +kernel

theorem fix_in (Q : List Nat) (hQ : (List.range Q.length).all (fun c => if c < {NA} then Q.getD c c == c
    else decide ({NA} ≤ Q.getD c c)) = true) : ∀ c, (c < {NA} → fp Q c = c) ∧ ({NA} ≤ c → {NA} ≤ fp Q c) := by
  intro c
  unfold fp
  by_cases hc : c < Q.length
  · rw [if_pos hc]
    have := List.all_eq_true.mp hQ c (List.mem_range.mpr hc)
    by_cases h2 : c < {NA}
    · simp only [h2, ite_true, beq_iff_eq] at this; exact ⟨fun _ => this, fun h => absurd h (by omega)⟩
    · simp only [h2, ite_false, decide_eq_true_eq] at this; exact ⟨fun h => absurd h h2, fun _ => this⟩
  · rw [if_neg hc]; exact ⟨fun _ => rfl, fun h => h⟩

theorem fixP : ∀ c, (c < {NA} → fp P c = c) ∧ ({NA} ≤ c → {NA} ≤ fp P c) := fix_in P (by decide +kernel)
theorem fixPi : ∀ c, (c < {NA} → fp Pi c = c) ∧ ({NA} ≤ c → {NA} ≤ fp Pi c) := fix_in Pi (by decide +kernel)

theorem ren_input {{Q : List Nat}} (hQ : ∀ c, (c < {NA} → fp Q c = c) ∧ ({NA} ≤ c → {NA} ≤ fp Q c))
    {{σ0 : Store Nat Nat}} (h0 : ∀ ch, {NA} ≤ ch → σ0 ch = []) : renS (fp Q) σ0 = σ0 := by
  funext c
  simp only [renS]
  by_cases h : c < {NA}
  · rw [(hQ c).1 h]
  · rw [h0 _ ((hQ c).2 (by omega)), h0 c (by omega)]

theorem pass_forward {{σ0 t : Store Nat Nat}} {{n : Nat}} (h0 : ∀ ch, {NA} ≤ ch → σ0 ch = [])
    (hr : Run (step (graph rulesIn)) σ0 n t) (ht : Terminal (step (graph rulesIn)) t) :
    ∃ t' m, Run (step (graph rulesOut)) σ0 m t' ∧ Terminal (step (graph rulesOut)) t' ∧
      (∀ ch, ch ∉ r1.2.2 → fp P ch ∉ r2.2.2 → t' (fp P ch) = t ch) ∧ t' {oo} = t {oi} := by
  obtain ⟨t1, m1, run1, term1, a1⟩ := (runScript_sound h1).fwd (fun c hc => h0 c (pre1_int c hc)) hr ht
  have run2 := run_ren (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp T) (fp Ti) (fp_inv T Ti hT)
    (renCheck_ok hRen) run1
  have term2 := terminal_ren (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp T) (fp Ti) (fp_inv Ti T hTi)
    (renCheck_ok hRen) term1
  rw [ren_input fixPi h0] at run2
  obtain ⟨t3, m3, run3, term3, a3⟩ := (runScript_sound h2).symm.fwd (fun c hc => h0 c (pre2_int c hc)) run2 term2
  have key : ∀ ch, ch ∉ r1.2.2 → fp P ch ∉ r2.2.2 → t3 (fp P ch) = t ch := by
    intro ch h1' h2'
    rw [a3 _ h2']; simp only [renS, fp_inv P Pi hP]; exact a1 ch h1'
  refine ⟨t3, m3, run3, term3, key, ?_⟩
  rw [← out_maps]; exact key _ out1 (by rw [out_maps]; exact out2)

theorem pass_backward {{σ0 t' : Store Nat Nat}} {{n : Nat}} (h0 : ∀ ch, {NA} ≤ ch → σ0 ch = [])
    (hr : Run (step (graph rulesOut)) σ0 n t') (ht : Terminal (step (graph rulesOut)) t') :
    ∃ t m, Run (step (graph rulesIn)) σ0 m t ∧ Terminal (step (graph rulesIn)) t ∧
      (∀ ch, ch ∉ r1.2.2 → fp P ch ∉ r2.2.2 → t ch = t' (fp P ch)) ∧ t {oi} = t' {oo} := by
  obtain ⟨t2, m2, run2, term2, a2⟩ := (runScript_sound h2).fwd (fun c hc => h0 c (pre2_int c hc)) hr ht
  have run1 := run_ren_back (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp Ti) (renCheck_ok hRen) run2
  have term1 := terminal_ren_back (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp T) (fp Ti)
    (fp_inv T Ti hT) (renCheck_ok hRen) term2
  rw [ren_input fixP h0] at run1
  obtain ⟨t0, m0, run0, term0, a0⟩ := (runScript_sound h1).bwd (fun c hc => h0 c (pre1_int c hc)) run1 term1
  have key : ∀ ch, ch ∉ r1.2.2 → fp P ch ∉ r2.2.2 → t0 ch = t' (fp P ch) := by
    intro ch h1' h2'
    rw [a0 ch h1']; simp only [renS]; exact a2 _ h2'
  refine ⟨t0, m0, run0, term0, key, ?_⟩
  rw [← out_maps]; exact key _ out1 (by rw [out_maps]; exact out2)

end Eq2CheckRun

#print axioms Eq2CheckRun.pass_forward
#print axioms Eq2CheckRun.pass_backward
'''

if __name__ == '__main__':
    sys.exit(main())
