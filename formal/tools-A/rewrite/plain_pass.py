#!/usr/bin/env python3
"""plain_pass.py IN.mlir OUT.mlir [--keep DIR] -- the plain loop-test rewrite (pre_dec), applied only when Lean proves it.

One command, from a clean checkout of claude/formal (after formal/setup.sh):
  1. `ring_dec.py --plain IN OUT`: the rewrite (the ring carries n - 1, the loop test `slt(i + 1, n)` becomes
     `slt(i, n - 1)` on the counter before its increment). No match: OUT = IN, exit 3.
  2. dfimport (formal/tools/dfimport/mlir2lean.py, bdc's own parser and fusion plan) of IN and of OUT.
  3. Untrusted search (Python): the pattern's labels and channels, the PlainPass certificate (gen_plain_gen.analyse),
     and the renumbering between `rs2p` and OUT's import (rules_iso.py).
  4. One Lean file stating, about the two imports:
        check rulesIn cert = true                         (decide +kernel; Formal.Rewrite.PlainPass)
        renCheck (rs2p rulesIn cert) rulesOut P Ti = true (decide +kernel; Formal.Rewrite.Rename)
        pass_forward / pass_backward: every complete run of IN's graph from tokens on the arguments only is matched by a
        complete run of OUT's graph (channels renamed by fp P) with the same tokens outside the changed channels,
        and vice versa.
     compiled with `lake env lean`; `#print axioms` must show only propext, Classical.choice, Quot.sound.
Exit 0: OUT is written AND proved equal to IN (token level, Kahn semantics of dfimport's graph). Exit 2: refused
(certificate not found or Lean rejected it): OUT is reset to a copy of IN. Exit 3: nothing matched (OUT = IN).
NOT covered: dfimport itself (MLIR -> rules) is trusted Python; nothing below the token level.
"""
import json, os, re, shutil, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
LEAN = os.path.join(ROOT, 'formal', 'lean')
sys.path.insert(0, HERE)
import gen_plain_gen as G  # noqa: E402

SLT = ('bin', ('cmpi', ('slt',)), 32, ('var', 0), ('var', 1))
INC = ('bin', ('addi',), 32, ('var', 0), ('lit', 1))
DEC = ('bin', ('addi',), 32, ('var', 0), ('lit', 4294967295))
SLTINC = ('bin', ('cmpi', ('slt',)), 32, ('var', 0), ('bin', ('addi',), 32, ('var', 1), ('lit', 1)))
XOR = ('bin', ('xori',), 1, ('bin', ('xori',), 1, SLT, ('bin', ('cmpi', ('eq',)), 32, ('var', 0), ('lit', 2147483647))),
       ('bin', ('cmpi', ('eq',)), 32, ('var', 1), ('lit', 2147483647)))

def ser(x):
    if isinstance(x, int): return str(x)
    if isinstance(x, list): return '[' + ', '.join(ser(a) for a in x) + ']'
    if len(x) == 1: return '.' + x[0]
    return '(.' + x[0] + ' ' + ' '.join(ser(a) for a in x[1:]) + ')'

def ser_rules(rs):
    return '[\n' + ',\n'.join('  ' + ser(r)[1:-1] if ser(r).startswith('(') else '  ' + ser(r) for r in rs) + '\n]'

def dfimport(mlir, out, ns):
    subprocess.check_call([sys.executable, os.path.join(ROOT, 'formal/tools/dfimport/mlir2lean.py'), mlir, '-o', out,
                           '--ns', ns, '--graph-module', ns, '--label', 'plain_pass', '--short', 'plain_pass'],
                          stdout=subprocess.DEVNULL)
    txt = open(out).read()
    N = int(re.search(r'^def N : Nat := (\d+)', txt, re.M).group(1))
    o = re.search(r'^def chOut : Nat := (\d+)', txt, re.M)
    return G.load(out), N, (int(o.group(1)) if o else None)

def find(R, N):
    L = len(R); found = []
    for C, rc in enumerate(R):
        if rc[0] != 'comp' or len(rc[1]) != 2 or rc[3] != SLT: continue
        y, kk = rc[1]; c = rc[2]
        try:
            d = next(i for i, r in enumerate(R) if r[0] == 'fork' and len(r[2]) == 2 and r[2][1] == y)
            s, s0 = R[d][1], R[d][2][0]
            b = next(i for i, r in enumerate(R) if r[0] == 'comp' and r[2] == s and len(r[1]) == 1 and r[3] == INC)
            e = R[b][1][0]
            F = next(i for i, r in enumerate(R) if r[0] == 'fork' and len(r[2]) == 2 and r[2][1] == kk)
            rr, r0 = R[F][1], R[F][2][0]
            M = next(i for i, r in enumerate(R) if r[0] == 'mux' and r[3] == rr and len(r[2]) == 2 and r[4] == 1)
            sel, (ne, nb) = R[M][1], R[M][2]
            B = next(i for i, r in enumerate(R) if r[0] == 'branch' and r[2] == r0 and r[3] == nb)
            cnd, nx = R[B][1], R[B][4]
            S = next(i for i, r in enumerate(R) if r[0] == 'sink' and r[1] == nx)
        except StopIteration:
            continue
        found.append(([M, F, B, S, C, L, sel, ne, N, rr, r0, kk, nb, nx, cnd, y, c, 1],
                      [b, d, C, e, s, s0, y, c, kk, N + 1, N + 2]))
    return found

def rewrite(R, pr, pt):
    M, F, B, S, C, L, sel, ne, nep, rr, r0, kk, nb, nx, cnd, y, c, iw = pr
    b, d, _, e, s, s0, _, _, _, e0, e1 = pt
    rs = list(R)
    rs[M] = ('mux', sel, [nep, nb], rr, iw); rs[C] = ('comp', [y, kk], c, SLTINC); rs.append(('comp', [ne], nep, DEC))
    rs[b] = ('fork', e, [e0, e1]); rs[d] = ('comp', [e0], s0, INC); rs[C] = ('comp', [e1, kk], c, XOR)
    rs2 = list(rs); rs2p = list(rs); rs2p[C] = ('comp', [e1, kk], c, SLT)
    return rs2, rs2p

def refuse(inp, out, why):
    shutil.copyfile(inp, out); print('plain_pass: REFUSED --', why, '(OUT reset to IN)'); return 2

def main():
    args = sys.argv[1:]; keep = None
    if '--keep' in args:
        i = args.index('--keep'); keep = args[i + 1]; del args[i:i + 2]
    inp, out = args
    r = subprocess.run([sys.executable, os.path.join(HERE, 'ring_dec.py'), inp, out, '--plain'], capture_output=True,
                       text=True)
    print(r.stdout.strip())
    if r.returncode != 0: return refuse(inp, out, 'ring_dec.py failed: ' + r.stderr.strip()[-300:])
    if open(inp).read() == open(out).read():
        print('plain_pass: no match, OUT = IN'); return 3
    tmp = keep or tempfile.mkdtemp(prefix='plain_pass_'); os.makedirs(tmp, exist_ok=True)
    Ri, Ni, oi = dfimport(inp, os.path.join(tmp, 'in.lean'), 'PlainPassIn')
    Ro, No, oo = dfimport(out, os.path.join(tmp, 'out.lean'), 'PlainPassOut')
    m = find(Ri, Ni)
    if len(m) != 1: return refuse(inp, out, f'{len(m)} matches of the pattern in the import of IN (need exactly 1)')
    pr, pt = m[0]
    rs2, rs2p = rewrite(Ri, pr, pt)
    try:
        A = G.analyse(rs2, pr, pt)
    except (G.Refused, AssertionError, StopIteration, KeyError) as x:
        return refuse(inp, out, f'no certificate: {x!r}')
    # renumbering rs2p -> OUT's import (untrusted search; Lean checks it)
    fa = os.path.join(tmp, 'rs2p.txt'); open(fa, 'w').write(ser_rules(rs2p))
    mp = os.path.join(tmp, 'maps.json')
    ri = subprocess.run([sys.executable, os.path.join(HERE, 'rules_iso.py'), fa, os.path.join(tmp, 'out.lean'), mp],
                        capture_output=True, text=True)
    if ri.returncode != 0: return refuse(inp, out, 'OUT\'s import is not rs2p up to renaming: ' + ri.stdout[-300:])
    mj = json.load(open(mp))
    ch = {int(a): b for a, b in mj['chan'].items()}; ru = {int(a): b for a, b in mj['rule'].items()}
    K = max(list(ch) + list(ch.values())) + 1
    freeA = [x for x in range(K) if x not in ch]; freeB = [x for x in range(K) if x not in set(ch.values())]
    for a, b in zip(freeA, freeB): ch[a] = b
    P = [ch[x] for x in range(K)]; Pi = [0] * K
    for a, b in ch.items(): Pi[b] = a
    T = [ru[l] for l in range(len(ru))]; Ti = [0] * len(ru)
    for a, b in ru.items(): Ti[b] = a
    outmap = f'theorem out_maps : fp P {oi} = {oo} := by decide +kernel\n' if oi is not None and oo is not None else ''
    lean = f'''import Formal.Rewrite.PlainPass
import Formal.Rewrite.Rename

/-! GENERATED by formal/tools-A/rewrite/plain_pass.py.
IN:  {os.path.abspath(inp)}
OUT: {os.path.abspath(out)}
`rulesIn` / `rulesOut` are dfimport's imports of IN / OUT. -/

namespace PlainPassRun
open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp Formal.Rewrite.PlainPass

def rulesIn : List Rule := {ser_rules(Ri)}

def rulesOut : List Rule := {ser_rules(Ro)}

{G.cert_lean('X', A['cert'])}
def P : List Nat := {P}
def Pi : List Nat := {Pi}
def T : List Nat := {T}
def Ti : List Nat := {Ti}

theorem hcheck : check rulesIn cX = true := by decide +kernel
theorem hP : fpCheck P Pi = true := by decide +kernel
theorem hPi : fpCheck Pi P = true := by decide +kernel
theorem hT : fpCheck T Ti = true := by decide +kernel
theorem hTi : fpCheck Ti T = true := by decide +kernel
theorem hRen : renCheck (rs2p rulesIn cX) rulesOut P Ti = true := by decide +kernel
theorem args_fixed : fp P 0 = 0 ∧ fp P 1 = 1 ∧ fp P 2 = 2 := by decide +kernel
{outmap}
theorem pass_forward {{σ0 t : Store Nat Nat}} {{n : Nat}} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0 ch = [])
    (hr : Run (step (graph rulesIn)) σ0 n t) (ht : Terminal (step (graph rulesIn)) t) :
    ∃ t' m, Run (step (graph rulesOut)) (renS (fp Pi) σ0) m t' ∧
      Terminal (step (graph rulesOut)) t' ∧ ∀ ch, ch ∉ changed cX → t' (fp P ch) = t ch := by
  obtain ⟨t3, m, r3, ht3, o3⟩ := plain_forward hcheck h0 hr ht
  refine ⟨renS (fp Pi) t3, m, run_ren (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp T) (fp Ti)
    (fp_inv T Ti hT) (renCheck_ok hRen) r3,
    terminal_ren (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp T) (fp Ti) (fp_inv Ti T hTi)
      (renCheck_ok hRen) ht3, ?_⟩
  intro ch hc; simp only [renS, fp_inv P Pi hP]; exact o3 ch hc

theorem pass_backward {{σ0' t' : Store Nat Nat}} {{n : Nat}} (h0 : ∀ ch, ch ≠ 0 → ch ≠ 1 → ch ≠ 2 → σ0' (fp P ch) = [])
    (hr : Run (step (graph rulesOut)) σ0' n t') (ht : Terminal (step (graph rulesOut)) t') :
    ∃ t m, Run (step (graph rulesIn)) (renS (fp P) σ0') m t ∧ Terminal (step (graph rulesIn)) t ∧
      ∀ ch, ch ∉ changed cX → t ch = t' (fp P ch) := by
  have r3 := run_ren_back (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp Ti) (renCheck_ok hRen) hr
  have ht3 := terminal_ren_back (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp T) (fp Ti)
    (fp_inv T Ti hT) (renCheck_ok hRen) ht
  obtain ⟨t, m, r, htt, o⟩ := plain_backward hcheck (fun ch a b c => h0 ch a b c) r3 ht3
  exact ⟨t, m, r, htt, fun ch hc => by rw [o ch hc]; rfl⟩

end PlainPassRun

#print axioms PlainPassRun.pass_forward
#print axioms PlainPassRun.pass_backward
'''
    lf = os.path.join(tmp, 'PlainPassRun.lean'); open(lf, 'w').write(lean)
    env = dict(os.environ); env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')
    b = subprocess.run(['lake', 'build', 'Formal.Rewrite.PlainPass', 'Formal.Rewrite.Rename'], cwd=LEAN, env=env,
                       capture_output=True, text=True)
    if b.returncode != 0: return refuse(inp, out, 'lake build of PlainPass failed: ' + b.stdout[-400:])
    c = subprocess.run(['lake', 'env', 'lean', lf], cwd=LEAN, env=env, capture_output=True, text=True)
    txt = c.stdout + c.stderr
    open(os.path.join(tmp, 'lean.log'), 'w').write(txt)
    ax = re.findall(r"depends on axioms: \[([^\]]*)\]", txt)
    ok = (c.returncode == 0 and 'error' not in txt and 'sorry' not in txt and len(ax) == 2 and
          all(sorted(a.replace(' ', '').split(',')) == ['Classical.choice', 'Quot.sound', 'propext'] for a in ax))
    if not ok: return refuse(inp, out, f'Lean rejected (rc {c.returncode}); see {tmp}/lean.log')
    print(f'plain_pass: PROVED -- {out} is equal to {inp} (Lean: {lf}; axioms propext, Classical.choice, Quot.sound)')
    return 0

if __name__ == '__main__':
    sys.exit(main())
