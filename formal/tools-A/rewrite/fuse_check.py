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


MR_OLD = """            if fu is not None and i in fu.anchor_region:
                reg = fu.anchor_region[i]
"""
MR_NEW = """            if fu is not None and i in fu.anchor_region and getattr(fu.anchor_region[i], "outputs", None):
                # formal A (fuse_check): a multi-result cell (BDC_RING_FUSE), modelled as bdc builds it: ONE cell whose
                # output packs every result (the first in the low bits), a fork, one slice per result
                reg = fu.anchor_region[i]
                parts, W = [], 0
                for v, mi in reg.outputs:
                    w = max(em.width(v), 1); parts.append((v, mi, W, w)); W += w
                pack = None
                for v, mi, lo, w in parts:
                    e = self.region_expr(reg, mi)
                    t = ("bin", "shli", W, e, ("lit", lo)) if lo else e
                    pack = t if pack is None else ("bin", "addi", W, pack, t)
                if os.environ.get("FA_MR_LOG"):   # side record for mr_verilog_check (no effect on the rules)
                    with open(os.environ["FA_MR_LOG"], "a") as _f:
                        _f.write(repr((i, [(lo, w, v, mi) for v, mi, lo, w in parts],
                                       [eternal.get(A(x), "live") if A(x) in eternal else "live"
                                        for x in reg.ext_inputs])) + "\\n")
                z = "__mr_%d" % i
                comp(list(reg.ext_inputs), z, pack, "fused multi-result cell")
                zs = ["__mr_%d_%d" % (i, k) for k in range(len(parts))]
                self.rules.append(("fork", self.ch(z), [self.ch(x) for x in zs], "multi-result fork"))
                for (v, mi, lo, w), zk in zip(parts, zs):
                    ex = ("un", "trunci", w, ("bin", "shrui", W, ("var", 0), ("lit", lo)))
                    self.rules.append(("comp", [self.ch(zk)], self.ch(v), ex, "multi-result slice"))
                continue
            if fu is not None and i in fu.anchor_region:
                reg = fu.anchor_region[i]
"""

WDUMP = """    if os.environ.get("FA_W_LOG"):   # formal A (fuse_check): declared (width, is_control) per channel, from bdc
        import json as _json
        _json.dump({"chan": [list(g.em.ch[v]) if v in g.em.ch else None for v in g.chname],
                    "args": [[a.ssa_name, g.chan[g.A(a.ssa_name)]] for a in g.func.args]},
                   open(os.environ["FA_W_LOG"], "w"))
"""

def importer_mr(tmp):
    """A copy of formal/tools/dfimport with multi-result cells modelled (patched at run time; the tool is not edited)."""
    import shutil
    d = os.path.join(tmp, 'imp', 'formal', 'tools', 'dfimport'); os.makedirs(d, exist_ok=True)
    src = os.path.join(ROOT, 'formal/tools/dfimport')
    for f in os.listdir(src):
        if f.endswith('.py'): shutil.copy(os.path.join(src, f), d)
    m = os.path.join(d, 'mlir2lean.py'); t = open(m).read()
    assert t.count(MR_OLD) == 1, 'dfimport changed: the multi-result patch no longer applies'
    t = t.replace(MR_OLD, MR_NEW)
    old2 = "        return self.em.ch[v][1]\n"
    assert t.count(old2) == 1
    t = t.replace(old2, "        return self.em.ch[v][1] if v in self.em.ch else False\n")
    old3 = '    w(f"def N : Nat := {g.N}")\n'
    assert t.count(old3) == 1, 'dfimport changed: the width dump no longer applies'
    t = t.replace(old3, old3 + WDUMP)
    open(m, 'w').write(t)
    link = os.path.join(tmp, 'imp', 'bdc')
    if os.path.islink(link): os.remove(link)
    os.symlink(os.path.abspath(PP.BDCDIR or os.path.join(ROOT, 'bdc')), link)
    return os.path.join(d, 'mlir2lean.py')

PP.importer = importer_mr

def dedupE(ins, a, b, F):
    er = list(ins); er.remove(b)
    return Q.subst(F, [('var', Q.pos(er, a if c == b else c)) for c in ins])

def swA(a, x, c): return x if c == a else c

class FPlan(Q.Plan):
    rf = 0; Wi = None; NA = 0
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
        elif k == 'forkcomm2':
            _, lc, lf, x0, x1, n0, n1 = st; rc, rf = rs[lc], rs[lf]
            assert rc[0] == 'comp' and len(rc[1]) == 2 and rf[0] == 'fork' and rf[1] == rc[2] and len(rf[2]) == 2, st
            (x, n), y, G = rc[1], rc[2], rc[3]; y0, y1 = rf[2]
            rs[lc] = ('fork', x, [x0, x1]); rs[lf] = ('fork', n, [n0, n1])
            rs.append(('comp', [x0, n0], y0, G)); rs.append(('comp', [x1, n1], y1, G))
            self.pre += [y, x0, x1, n0, n1]; self.chg += [x, n, y, x0, x1, n0, n1]; self.steps.append(st)
        elif k == 'unpack':
            _, l = st; r = rs[l]; F2 = unslice_n(8, r[3]); assert F2 != r[3], st
            rs[l] = ('comp', r[1], r[2], F2); self.steps.append(st)
        elif k == 'unjoin':
            _, lx, ln, lc, lk, lb, lu = st; rn, ru_ = rs[ln], rs[lu]
            x1, n1 = rs[lc][1]; c = rs[lc][2]; cc = rs[lb][1]; x2, n2 = ru_[1]; u = ru_[2]
            assert rn[0] == 'fork' and rn[2][0] == n2 and not uses_var(ru_[3], 1), st
            rs[ln] = ('fork', rn[1], rn[2][1:]); rs[lu] = ('comp', [x2], u, ru_[3])
            self.pre += [x1, x2, n1, n2, c, cc, u]; self.chg += [x2, n2, u]; self.steps.append(st)
        elif k == 'permute':
            _, T, Ti = st; old = list(rs); rs[:] = [old[Ti[l]] for l in range(len(old))]
            self.sinks = [T[x] for x in self.sinks]; self.steps.append(st)
        elif k == 'forkmerge':
            _, lf = st; last = rs.pop(); rf = rs[lf]
            assert last[0] == 'fork' and rf[0] == 'fork' and rf[2][0] == last[1], st
            rs[lf] = ('fork', rf[1], list(last[2]) + list(rf[2][1:])); self.pre += [last[1]]; self.chg += [last[1]]
            self.steps.append(st)
        elif k == 'unabsorb':   # Absorb read backward (Lean: applyUA, checked by absorbing back and dropping the sink)
            _, lq, bs, as_, pc, f, g = st; rq = rs[lq]
            assert rq[0] == 'comp' and list(rq[1]) == list(bs) + list(as_) and Q.absorbE(len(bs), len(as_), f, g) == rq[3], st
            rs[lq] = ('comp', list(bs) + [pc], rq[2], g); rs.append(('comp', list(as_), pc, f))
            self.pre += [pc, pc]; self.chg += [pc] + list(as_); self.steps.append(st)
        elif k == 'unpackw':    # Lean: applyUW (slices narrowed with the inputs' widths; every rule checked safe)
            _, l, W = st; r = rs[l]
            assert all(safeB(W, x) for x in rs), st
            F2 = unslice_nw([wOf(W, c) for c in r[1]], 8, r[3]); assert F2 != r[3], st
            rs[l] = ('comp', r[1], r[2], F2); self.steps.append(st)
        elif k == 'undedupe':   # Lean: applyUD (Dedupe read backward: the comp reads one more copy b of a's fork)
            _, lf, lc, a, b, os2, ins2, F2 = st
            assert list(os2) == list(rs[lf][2]) + [b] and list(ins2) == list(rs[lc][1]) + [b], st
            assert Q.subst(F2, [('var', Q.pos(list(rs[lc][1]), a if c == b else c)) for c in ins2]) == rs[lc][3], st
            rs[lf] = ('fork', rs[lf][1], list(os2)); rs[lc] = ('comp', list(ins2), rs[lc][2], F2)
            self.pre += [a, b]; self.chg += [b]; self.steps.append(st)
        elif k == 'back':       # Lean: applyBK (a StepRF script read backward, checked by running it forward)
            _, ed, app, ss = st; old = list(rs)
            for l, r in ed: rs[l] = r
            rs.extend(app)
            sub = FPlan(list(rs))
            for s in ss: sub.do(s)
            assert sub.rs == old, st
            self.pre += sub.pre; self.chg += sub.chg; self.steps.append(st)
        elif k == 'constdata':
            _, lc, i, v, C = st; rc = rs[lc]; n = len(rc[1])
            F2 = Q.subst(rc[3], [('lit', v) if j == i else ('var', j) for j in range(n)])
            rs[lc] = ('comp', rc[1], rc[2], F2); self.pre += list(C); self.steps.append(st)
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

def uses_var(e, i):
    k = e[0]
    if k == 'var': return e[1] == i
    if k == 'lit': return False
    if k == 'un': return uses_var(e[3], i)
    if k == 'bin': return uses_var(e[3], i) or uses_var(e[4], i)
    if k == 'sel': return any(uses_var(x, i) for x in e[1:])
    return False

def const_class(R, ch):
    """(v, C) if ch carries only the constant v: its writers go back through forks to one `comp _ k (lit v)`."""
    seen = set()
    while True:
        if ch in seen: return None
        seen.add(ch); W = Q.writers(R, ch)
        if len(W) != 1: return None
        r = R[W[0]]
        if r[0] == 'fork': ch = r[1]; continue
        if r[0] == 'comp' and r[3][0] == 'lit': root = ch; v = r[3][1]; break
        return None
    C = [root]; frontier = [root]
    while frontier:
        c = frontier.pop()
        for l in Q.readers(R, c):
            if R[l][0] == 'fork':
                for o in R[l][2]:
                    if o not in C: C.append(o); frontier.append(o)
    return v, C

BW_OPS = {'addi', 'subi', 'muli', 'andi', 'ori', 'xori', 'shli'}

def bw(e):
    """Width bound from the top operator (Lean: Formal.Rewrite.Steps.bw)."""
    if e[0] == 'un' and e[1][0] in ('trunci', 'extui'): return e[2]
    if e[0] == 'bin' and e[1][0] in BW_OPS: return e[2]
    if e[0] == 'bin' and e[1][0] == 'cmpi': return 1
    if e[0] == 'bin' and e[1][0] in ('shrui', 'shrsi'): return e[2]
    if e[0] == 'sel':
        a, b = bw(e[2]), bw(e[3])
        return None if a is None or b is None else max(a, b)
    return None

def bwp(e):
    """Lean: Formal.Rewrite.Steps.bwp (bw, plus packed pairs)."""
    if (e[0] == 'bin' and e[1] == ('addi',) and e[4][0] == 'bin' and e[4][1] == ('shli',) and e[4][4][0] == 'lit'):
        W = e[2]; A = e[3]; W2 = e[4][2]; B = e[4][3]; w0 = e[4][4][1]
        a, b = bwp(A), bwp(B)
        if a is None or b is None: return W
        return w0 + b if (W2 == W and a <= w0 and w0 + b <= W) else W
    return bw(e)

def unslice(F):
    """Lean: Formal.Rewrite.Steps.unslice (one narrowing of a slice of a packed pair, or a slice-at-0 identity)."""
    if not (F[0] == 'un' and F[1] == ('trunci',) and F[3][0] == 'bin' and F[3][1] == ('shrui',)
            and F[3][4][0] == 'lit'):
        return None
    w = F[2]; W = F[3][2]; p = F[3][3]; lo = F[3][4][1]
    if p[0] == 'bin' and p[1] == ('addi',) and p[4][0] == 'bin' and p[4][1] == ('shli',) and p[4][4][0] == 'lit':
        W1 = p[2]; A = p[3]; W2 = p[4][2]; B = p[4][3]; w0 = p[4][4][1]
        a, b = bwp(A), bwp(B)
        if a is None or b is None: return None
        if not (W1 == W and W2 == W and a <= w0 and w0 + b <= W): return None
        if lo + w <= w0: return ('un', ('trunci',), w, ('bin', ('shrui',), W, A, ('lit', lo)))
        if w0 <= lo: return ('un', ('trunci',), w, ('bin', ('shrui',), W, B, ('lit', lo - w0)))
        return None
    if lo == 0:
        b = bwp(p)
        if b is not None and b <= w and b <= W: return p
    return None

def unslice_deep(e):
    """Lean: Formal.Rewrite.Steps.unsliceDeep (unslice at every node, outermost first)."""
    t = unslice(e)
    if t is not None: return t
    if e[0] == 'un': return ('un', e[1], e[2], unslice_deep(e[3]))
    if e[0] == 'bin': return ('bin', e[1], e[2], unslice_deep(e[3]), unslice_deep(e[4]))
    if e[0] == 'sel': return ('sel', unslice_deep(e[1]), unslice_deep(e[2]), unslice_deep(e[3]))
    return e

def unslice_n(n, e):
    for _ in range(n): e = unslice_deep(e)
    return e

# ---------- the width assumption (Lean: Formal.Rewrite.Steps.Width) ----------
def wOf(W, c): return W[c] if 0 <= c < len(W) else 0

def bwv(ws, e):
    if e[0] == 'var': w = wOf(ws, e[1]); return None if w == 0 else w
    if e[0] == 'lit': return max(e[1].bit_length(), 1)     # Nat.log2 v + 1
    if e[0] == 'sel':
        a, b = bwv(ws, e[2]), bwv(ws, e[3])
        return None if a is None or b is None else max(a, b)
    return bw(e)

def bwpv(ws, e):
    if (e[0] == 'bin' and e[1] == ('addi',) and e[4][0] == 'bin' and e[4][1] == ('shli',) and e[4][4][0] == 'lit'):
        W = e[2]; A = e[3]; W2 = e[4][2]; B = e[4][3]; w0 = e[4][4][1]
        a, b = bwpv(ws, A), bwpv(ws, B)
        if a is None or b is None: return W
        return w0 + b if (W2 == W and a <= w0 and w0 + b <= W) else W
    return bwv(ws, e)

def unslice_w(ws, F):
    if not (F[0] == 'un' and F[1] == ('trunci',) and F[3][0] == 'bin' and F[3][1] == ('shrui',)
            and F[3][4][0] == 'lit'):
        return None
    w = F[2]; W = F[3][2]; p = F[3][3]; lo = F[3][4][1]
    if p[0] == 'bin' and p[1] == ('addi',) and p[4][0] == 'bin' and p[4][1] == ('shli',) and p[4][4][0] == 'lit':
        W1 = p[2]; A = p[3]; W2 = p[4][2]; B = p[4][3]; w0 = p[4][4][1]
        a, b = bwpv(ws, A), bwpv(ws, B)
        if a is None or b is None: return None
        if not (W1 == W and W2 == W and a <= w0 and w0 + b <= W): return None
        if lo + w <= w0: return ('un', ('trunci',), w, ('bin', ('shrui',), W, A, ('lit', lo)))
        if w0 <= lo: return ('un', ('trunci',), w, ('bin', ('shrui',), W, B, ('lit', lo - w0)))
        return None
    if lo == 0:
        b = bwpv(ws, p)
        if b is not None and b <= w and b <= W: return p
    return None

def unslice_deep_w(ws, e):
    t = unslice_w(ws, e)
    if t is not None: return t
    if e[0] == 'un': return ('un', e[1], e[2], unslice_deep_w(ws, e[3]))
    if e[0] == 'bin': return ('bin', e[1], e[2], unslice_deep_w(ws, e[3]), unslice_deep_w(ws, e[4]))
    if e[0] == 'sel': return ('sel', unslice_deep_w(ws, e[1]), unslice_deep_w(ws, e[2]), unslice_deep_w(ws, e[3]))
    return e

def unslice_nw(ws, n, e):
    for _ in range(n): e = unslice_deep_w(ws, e)
    return e

def wle(W, a, b): return wOf(W, b) == 0 or (wOf(W, a) != 0 and wOf(W, a) <= wOf(W, b))

def safeB(W, r):
    k = r[0]
    if k == 'comp':
        if wOf(W, r[2]) == 0: return True
        b = bwpv([wOf(W, c) for c in r[1]], r[3]); return b is not None and b <= wOf(W, r[2])
    if k == 'fork': return all(wle(W, r[1], o) for o in r[2])
    if k == 'branch': return wle(W, r[2], r[3]) and wle(W, r[2], r[4])
    if k == 'mux': return all(wle(W, d, r[3]) for d in r[2])
    if k == 'cm': return wle(W, r[1], r[2]) and (wOf(W, r[3]) == 0 or r[4] < 2 ** wOf(W, r[3]))
    return True

def infer_W(R, Wi, NA):
    """A width map for the rules R that every rule keeps (safeB), with the input channels at their declared widths
    Wi (0 = none). Forward propagation to a fixpoint (None = nothing yet, 0 = no bound); then any channel whose
    writer fails safeB loses its bound, until every rule passes. Lean re-checks it (applyUW)."""
    N = fresh(R) + 1
    W = [None] * N
    for c in range(min(NA, N)): W[c] = wOf(Wi, c)
    def join(c, w):
        if c < NA: return False
        old = W[c]
        if w is None: return False
        new = w if old is None else (0 if (old == 0 or w == 0) else max(old, w))
        if new > 512: new = 0
        if new != old: W[c] = new; return True
        return False
    def g(c): return W[c] if 0 <= c < N else 0
    changed = True; rounds = 0
    while changed and rounds < 200:
        changed = False; rounds += 1
        for r in R:
            k = r[0]
            if k == 'comp':
                if any(g(c) is None for c in r[1]): continue
                b = bwpv([g(c) for c in r[1]], r[3]); changed |= join(r[2], 0 if b is None else b)
            elif k == 'fork':
                if g(r[1]) is not None:
                    for o in r[2]: changed |= join(o, g(r[1]))
            elif k == 'branch':
                if g(r[2]) is not None: changed |= join(r[3], g(r[2])); changed |= join(r[4], g(r[2]))
            elif k == 'mux':
                for d in r[2]:
                    if g(d) is not None: changed |= join(r[3], g(d))
            elif k == 'cm':
                if g(r[1]) is not None: changed |= join(r[2], g(r[1]))
                changed |= join(r[3], max(r[4].bit_length(), 1))
    W = [0 if w is None else w for w in W]
    while True:
        bad = [r for r in R if not safeB(W, r)]
        if not bad: break
        for r in bad:
            for c in Q.outs_of(r):
                if c >= NA: W[c] = 0
    while W and W[-1] == 0: W.pop()
    return W

def do_unpack(p, l):
    """Narrow the slices in the comp at l: `unpack` when the syntactic widths suffice (as before), else `unpackw`
    with a width map of the current rules (needs the width assumption on the inputs)."""
    r = p.rs[l]; F = r[3]; plain = unslice_n(8, F)
    if p.Wi is None:   # no width map: the unconditional step only (as before the width mode)
        p.do(('unpack', l)); return
    W = infer_W(p.rs, p.Wi, p.NA)
    wide = unslice_nw([wOf(W, c) for c in r[1]], 8, F)
    if wide == plain:
        if plain != F: p.do(('unpack', l))
    else:
        p.do(('unpackw', l, W))

def unpacks(p, S, H, ins):
    """The slice S of the packed word H (over the inputs ins) narrows (with the width map when there is one)."""
    e = Q.subst(S, [H])
    if unslice_n(8, e) != e: return True
    if p.Wi is None: return False
    W = infer_W(p.rs, p.Wi, p.NA)
    return unslice_nw([wOf(W, c) for c in ins], 8, e) != e

def fresh(R):
    return 1 + max([c for r in R for c in (Q.ins_of(r) + Q.outs_of(r))] + [0])

def rf_merge(p, inner, outer, labs):
    """Move the fork at `inner` to the end (permute) and merge it into the fork at `outer` (forkmerge).
    `labs` (dict name -> label) is updated for the relabelling."""
    R = p.rs; n = len(R)
    Ti = [l for l in range(n) if l != inner] + [inner]
    T = [0] * n
    for new_l, old in enumerate(Ti): T[old] = new_l
    p.do(('permute', T, Ti))
    for k, v in labs.items():
        if isinstance(v, list): labs[k] = [T[x] for x in v]
        else: labs[k] = T[v]
    outer = T[outer]
    p.do(('forkmerge', outer))
    return outer

def subterms(e):
    yield e
    if e[0] == 'un': yield from subterms(e[3])
    elif e[0] == 'bin': yield from subterms(e[3]); yield from subterms(e[4])
    elif e[0] == 'sel':
        for x in e[1:]: yield from subterms(x)

def vars_of(e): return {s[1] for s in subterms(e) if s[0] == 'var'}

def replace_t(e, t, by):
    if e == t: return by
    if e[0] == 'un': return ('un', e[1], e[2], replace_t(e[3], t, by))
    if e[0] == 'bin': return ('bin', e[1], e[2], replace_t(e[3], t, by), replace_t(e[4], t, by))
    if e[0] == 'sel': return ('sel',) + tuple(replace_t(x, t, by) for x in e[1:])
    return e

def contains(e, t): return any(s == t for s in subterms(e))

def size(e): return sum(1 for _ in subterms(e))

def rf_factor(H, k, slices):
    """A k-input cell `comp (n :: as) z H` (n first) as `comp as p f` absorbed into `comp [n, p] z g`:
    f is a subterm of H over `as` only, every read of `as` in H lies inside a copy of f, and every slice of the
    packed word still unpacks with f folded (no part is f itself). Largest such f first. None if there is none."""
    seen = []
    for s in subterms(H):
        v = vars_of(s)
        if s[0] != 'var' and v and v <= set(range(1, k)) and s not in seen: seen.append(s)
    for s in sorted(seen, key=size, reverse=True):
        g = replace_t(H, s, ('var', 10 ** 6))
        if not vars_of(g) <= {0, 10 ** 6}: continue
        g = replace_t(g, ('var', 10 ** 6), ('var', 1))
        f = Q.subst(s, [('lit', 0)] + [('var', j) for j in range(k - 1)])
        if Q.absorbE(1, k - 1, f, g) != H: continue
        if all(not contains(unslice_n(8, Q.subst(S, [g])), g) for S in slices): return f, g
    return None

def is_test(R, ch):
    """`ch` is read by a comp whose result only steers branches (a loop test), possibly through comps that absorb."""
    a = Q.readers(R, ch)
    if len(a) != 1 or R[a[0]][0] != 'comp': return False
    b = Q.readers(R, R[a[0]][2])
    if len(b) == 1 and R[b[0]][0] == 'comp': return is_test(R, R[a[0]][2])   # the test's copy, not yet absorbed
    if len(b) != 1 or R[b[0]][0] != 'fork': return False
    return all(len(Q.readers(R, z)) == 1 and R[Q.readers(R, z)[0]][0] == 'branch'
               and R[Q.readers(R, z)[0]][1] == z for z in R[b[0]][2])

def rf_flatten(p, pins):
    """Every fork fed by the fork reading `pin` merges into it (so duplicate reads can dedupe)."""
    R = p.rs
    for pin in pins:
        while True:
            lo = [l for l in Q.readers(R, pin) if R[l][0] == 'fork']
            if len(lo) != 1: break
            lo = lo[0]
            kid = next((ch for ch in R[lo][2]
                        if len(Q.readers(R, ch)) == 1 and R[Q.readers(R, ch)[0]][0] == 'fork'), None)
            if kid is None: break
            os_ = list(R[lo][2])
            if os_[0] != kid: p.do(('forder', lo, [kid] + [x for x in os_ if x != kid]))
            rf_merge(p, Q.readers(R, kid)[0], lo, {})

def rf_order(p, pins):
    """Canonical order, as on the other side: the updates' copies first, the test's last."""
    R = p.rs
    for pin in pins:
        lo = [l for l in Q.readers(R, pin) if R[l][0] == 'fork']
        if len(lo) != 1: continue
        os_ = list(R[lo[0]][2]); want = [c for c in os_ if not is_test(R, c)] + [c for c in os_ if is_test(R, c)]
        if want != os_: p.do(('forder', lo[0], want))

def rf_prefactor(p, lc, sls, branch_data):
    """A three-input packed cell with two slices: the inputs the update parts read (`as`, two of them) are folded
    into one fresh channel by `unabsorb`, so that the cell reads `[n, pc]` and the two-input steps apply.
    Returns (label of `comp as pc f`, pc, as) or None (nothing done)."""
    R = p.rs; r = R[lc]; ins = list(r[1]); H = r[3]
    if len(sls) != 2: return None
    parts = [unslice_n(8, Q.subst(R[s][3], [H])) for s in sls]
    ups = [k for k in range(2) if branch_data(R[sls[k]][2]) is not None]
    if not ups: return None
    U = set().union(*(vars_of(parts[k]) for k in ups))
    bs = [ins[i] for i in range(3) if i not in U]; as_ = [ins[i] for i in range(3) if i in U]
    if len(bs) != 1 or len(as_) != 2: return None
    ins2 = bs + as_; H2 = Q.reindex(ins, ins2, H)
    fg = rf_factor(H2, 3, [R[s][3] for s in sls])
    if fg is None: return None
    if ins2 != ins: p.do(('reorder', lc, ins2))
    pc = fresh(R)
    p.do(('unabsorb', lc, bs, as_, pc, fg[0], fg[1]))
    return [(pc, as_)]

def rf_gate(p, lc, sls, branch_data):
    """A three-input packed cell with three slices (iterative_division): two data inputs a, b and one wait k (no part
    reads it); one test reads a and b, one update reads only a, one only b. The cell reads one more copy k2 of k
    (undedupe), then [k, a] and [k2, b] are each folded into a fresh channel that carries a, gated by k (unabsorb,
    f = var 1), so the cell reads [x, y] and the two-input steps apply. Returns [(x, [k, a]), (y, [k2, b])] or None."""
    R = p.rs; r = R[lc]; ins = list(r[1]); H = r[3]
    if len(sls) != 3 or p.Wi is None: return None
    W = infer_W(R, p.Wi, p.NA); ws = [wOf(W, c) for c in ins]
    parts = [unslice_nw(ws, 8, Q.subst(R[s][3], [H])) for s in sls]
    if any(contains(e, H) for e in parts): return None
    ups = [k for k in range(3) if branch_data(R[sls[k]][2]) is not None]
    if len(ups) != 2: return None
    D = sorted(set().union(*(vars_of(e) for e in parts))); K = [i for i in range(3) if i not in D]
    if len(D) != 2 or len(K) != 1: return None
    if sorted(tuple(sorted(vars_of(parts[k]))) for k in ups) != [(D[0],), (D[1],)]: return None
    kch = ins[K[0]]; Wk = Q.writers(R, kch)
    if len(Wk) != 1 or R[Wk[0]][0] != 'fork' or Q.readers(R, kch) != [lc]: return None
    lfk = Wk[0]; k2 = fresh(R)
    p.do(('undedupe', lfk, lc, kch, k2, list(R[lfk][2]) + [k2], ins + [k2], H))
    def gate(data, wait):
        cur = list(R[lc][1]); bs = [c for c in cur if c not in (data, wait)]; as_ = [wait, data]
        ins2 = bs + as_; H2 = Q.reindex(cur, ins2, R[lc][3]); nb = len(bs)
        g = Q.subst(H2, [('var', i) for i in range(nb)] + [('lit', 0), ('var', nb)])
        f = ('var', 1)
        if Q.absorbE(nb, 2, f, g) != H2: return None
        if ins2 != cur: p.do(('reorder', lc, ins2))
        pc = fresh(R); p.do(('unabsorb', lc, bs, as_, pc, f, g)); return pc
    x = gate(ins[D[0]], kch)
    y = gate(ins[D[1]], k2) if x is not None else None
    if y is None: raise AssertionError('rf_gate: fold failed after undedupe')
    if R[lc][1] != [x, y]: p.do(('reorder', lc, [x, y]))
    return [(x, [kch, ins[D[0]]]), (y, [k2, ins[D[1]]])]

def comps_first(p, lfk):
    """Order the fork at `lfk`: outputs read by comps first, then the others (both stable)."""
    R = p.rs; os_ = list(R[lfk][2])
    isc = lambda o: any(R[l][0] == 'comp' for l in Q.readers(R, o))
    want = [o for o in os_ if isc(o)] + [o for o in os_ if not isc(o)]
    if want != os_: p.do(('forder', lfk, want))

def ext_shape(R, lc, sls, branch_data):
    """The shape of a packed cell with an external test (iterative_sqrt's `comp [mid, n, lo, hi]`): two slices, the
    output of each forked into [the data of a branch, a copy read by one test comp T], the same T for both. Returns
    (T's label, [(slice output's fork label, data copy, test copy)] per slice) or None."""
    if len(sls) != 2: return None
    T = None; per = []
    for s in sls:
        rd = Q.readers(R, R[s][2])
        if len(rd) != 1 or R[rd[0]][0] != 'fork' or len(R[rd[0]][2]) != 2: return None
        lfo = rd[0]; d = t_ = None
        for o in R[lfo][2]:
            a = Q.readers(R, o)
            if len(a) != 1: return None
            if branch_data(o) is not None: d = o
            elif R[a[0]][0] == 'comp': t_ = o; T = a[0] if T is None else (T if T == a[0] else -1)
        if d is None or t_ is None: return None
        per.append((lfo, d, t_))
    if T is None or T < 0 or len(R[T][1]) != 2: return None
    tf = Q.readers(R, R[T][2])
    if len(tf) != 1 or R[tf[0]][0] != 'fork': return None
    return T, per

def rf_ext(p, lc, lf, sls, branch_data):
    """A k-input packed cell (k >= 3) with an external test (`ext_shape`). Its expression `pack(A, B)` is split into
    `comp [X, Y] pack(v0, v1)` with `X = comp as_A A`, `Y = comp as_B B` (an input both parts read gets a second copy:
    `back` inserts a one-output fork when it has none, then `undedupe`; then two `unabsorb`s). Then: forkcomm2 and
    absorb/unpack the slices (each becomes a copy of X or Y), forkcomm2 each slice before its fork, the test absorbs
    its copies (flatten, dedupe: it reads one copy of X and one of Y), and each data copy stops waiting for the other
    part (unjoin; JoinExt). Returns True if done (False: nothing changed)."""
    R = p.rs; r = R[lc]; ins = list(r[1]); H = r[3]
    if len(ins) < 3 or p.Wi is None: return False
    sh = ext_shape(R, lc, sls, branch_data)
    if sh is None: return False
    if not (H[0] == 'bin' and H[1] == ('addi',) and H[4][0] == 'bin' and H[4][1] == ('shli',) and H[4][4][0] == 'lit'):
        return False
    WW = H[2]; A = H[3]; B = H[4][3]; w0 = H[4][4][1]
    vA, vB = vars_of(A), vars_of(B)
    if not vA or not vB or (vA | vB) != set(range(len(ins))): return False
    # the slices must unpack to A and B (one each) on the cell's own inputs (Lean checks them again on X and Y)
    W = infer_W(R, p.Wi, p.NA); ws = [wOf(W, c) for c in ins]
    got = [unslice_nw(ws, 8, Q.subst(R[s][3], [H])) for s in sls]
    if sorted(map(repr, got)) != sorted(map(repr, [A, B])): return False
    shared = sorted(vA & vB)
    for i in shared:   # every shared input must come from a fork the cell alone reads from (or have no other reader)
        ch = ins[i]; Wc = Q.writers(R, ch)
        if Q.readers(R, ch) != [lc]: return False
        if not (len(Wc) == 1 and R[Wc[0]][0] == 'fork'):
            if ch < p.NA: return False
    # 1. a second copy of each shared input, read by B
    Bv = B
    for i in shared:
        ch = R[lc][1][i]; Wc = Q.writers(R, ch)
        if not (len(Wc) == 1 and R[Wc[0]][0] == 'fork'):
            a = fresh(R); L = len(R); rc = R[lc]
            p.do(('back', [(lc, ('comp', [a if c == ch else c for c in rc[1]], rc[2], rc[3]))], [('fork', ch, [a])],
                  [('wire', L, lc), ('drop', L)]))
            ch = a; Wc = [L]
        lfk = Wc[0]; b = fresh(R); cur = list(R[lc][1]); nb = len(cur)
        Bv = Q.subst(Bv, [('var', nb) if j == i else ('var', j) for j in range(nb)])
        F2 = ('bin', ('addi',), WW, A, ('bin', ('shli',), WW, Bv, ('lit', w0)))
        p.do(('undedupe', lfk, lc, ch, b, list(R[lfk][2]) + [b], cur + [b], F2))
        comps_first(p, lfk)
    # 2. Y = comp as_B B, X = comp as_A A, the cell reads [X, Y]
    cur = list(R[lc][1]); F = R[lc][3]
    aA = [cur[i] for i in sorted(vars_of(F[3]))]; aB = [cur[i] for i in sorted(vars_of(F[4][3]))]
    if set(aA) & set(aB) or set(aA) | set(aB) != set(cur): return False   # (cannot happen after step 1)
    ins2 = aA + aB
    if ins2 != cur: p.do(('reorder', lc, ins2))
    H2 = R[lc][3]; nb, na = len(aA), len(aB)
    fB = Q.subst(H2[4][3], [('lit', 0)] * nb + [('var', j) for j in range(na)])
    g = ('bin', ('addi',), WW, H2[3], ('bin', ('shli',), WW, ('var', nb), ('lit', w0)))
    pY = fresh(R); p.do(('unabsorb', lc, aA, aB, pY, fB, g))
    p.do(('reorder', lc, [pY] + aA))
    H3 = R[lc][3]
    fA = Q.subst(H3[3], [('lit', 0)] + [('var', j) for j in range(nb)])
    g2 = ('bin', ('addi',), WW, ('var', 1), ('bin', ('shli',), WW, ('var', 0), ('lit', w0)))
    pX = fresh(R); p.do(('unabsorb', lc, [pY], aA, pX, fA, g2))
    p.do(('reorder', lc, [pX, pY]))
    # 3. forkcomm2 of the packed cell; each slice absorbs its copy and unpacks to v0 / v1
    for s in sls:
        if not unpacks(p, R[s][3], R[lc][3], R[lc][1]): raise AssertionError('rf_ext: a slice does not unpack')
    L0 = len(R); e = fresh(R)
    p.do(('forkcomm2', lc, lf, e + 1, e + 2, e + 3, e + 4))
    lX, lY = lc, lf    # fork pX [..], fork pY [..]
    part = []
    for k, s in enumerate(sls):
        p.do(('absorb', L0 + k, s)); do_unpack(p, s)
        if R[s][3] not in (('var', 0), ('var', 1)): raise AssertionError('rf_ext: slice %d unpacked to %r' % (k, R[s][3]))
        part.append(R[s][3][1])
    if sorted(part) != [0, 1]: raise AssertionError('rf_ext: slices %r' % part)
    # 4. forkcomm2 of each slice before its fork: one comp for the data copy, one for the test's
    T, per = sh
    dl = []
    for k, s in enumerate(sls):
        lfo, d, t_ = per[k]; os_ = list(R[lfo][2])
        L1 = len(R); e = fresh(R)
        p.do(('forkcomm2', s, lfo, e + 1, e + 2, e + 3, e + 4))
        ld = L1 + os_.index(d); lt = L1 + os_.index(t_)
        # the test absorbs its copy
        it = list(R[T][1]); oc = R[lt][2]
        if it[-1] != oc: p.do(('reorder', T, [c for c in it if c != oc] + [oc]))
        p.do(('absorb', lt, T))
        dl.append(ld)
    # 5. flatten the copies of X and Y into one fork each; the test reads one copy of each (dedupe)
    cT = R[T][2]; dch = [R[ld][2] for ld in dl]
    rf_flatten(p, [pX, pY])
    T = Q.writers(R, cT)[0]; dl = [Q.writers(R, c)[0] for c in dch]
    for pc in (pX, pY):
        lfp = [l for l in Q.readers(R, pc) if R[l][0] == 'fork'][0]
        tin = [c for c in R[T][1] if c in R[lfp][2]]
        while len(tin) > 1:
            p.do(('dedupe', lfp, T, tin[0], tin[1])); tin = [c for c in R[T][1] if c in R[lfp][2]]
    lX = [l for l in Q.readers(R, pX) if R[l][0] == 'fork'][0]
    lY = [l for l in Q.readers(R, pY) if R[l][0] == 'fork'][0]
    # 6. each data copy stops waiting for the other part (unjoin)
    lk = Q.readers(R, R[T][2])[0]
    for k, ld in enumerate(dl):
        ax, an = (lX, lY) if part[k] == 0 else (lY, lX)
        ins_d = list(R[ld][1])
        x2 = [c for c in ins_d if c in R[ax][2]][0]; n2 = [c for c in ins_d if c in R[an][2]][0]
        if ins_d != [x2, n2]: p.do(('reorder', ld, [x2, n2]))
        it = list(R[T][1]); x1 = [c for c in it if c in R[ax][2]][0]; n1 = [c for c in it if c in R[an][2]][0]
        if it != [x1, n1]: p.do(('reorder', T, [x1, n1]))
        os_ = list(R[an][2])
        if os_[0] != n2: p.do(('forder', an, [n2] + [c for c in os_ if c != n2]))
        lb = branch_data(R[ld][2])
        p.do(('unjoin', ax, an, T, lk, lb, ld))
    p.ext = getattr(p, 'ext', 0) + 1
    return True

def rf_unpack(p):
    """Fused side (BDC_RING_FUSE): a one- or two-input packed cell, its fork and its two or three slices become the
    test and the updates as separate comps; an update stops waiting for the input it does not read (unjoin).
    A three-input cell with two slices is first factored into a two-input one (rf_prefactor: unabsorb).
    Returns the number of cells done."""
    R = p.rs; done = 0; skip = set()
    def branch_data(ch):
        rd = Q.readers(R, ch); return rd[0] if len(rd) == 1 and R[rd[0]][0] == 'branch' and R[rd[0]][2] == ch else None
    while True:
        hit = None
        for lc, r in enumerate(R):
            if r[0] != 'comp' or len(r[1]) < 1 or lc in skip: continue
            Wf = Q.readers(R, r[2])
            if len(Wf) != 1 or R[Wf[0]][0] != 'fork' or len(R[Wf[0]][2]) not in (2, 3): continue
            lf = Wf[0]; sl = [Q.readers(R, z) for z in R[lf][2]]
            if not all(len(a) == 1 and R[a[0]][0] == 'comp' and len(R[a[0]][1]) == 1 for a in sl): continue
            if not all(unpacks(p, R[a[0]][3], r[3], r[1]) for a in sl): continue
            hit = (lc, lf, [a[0] for a in sl]); break
        if hit is None: return done
        lc, lf, sls = hit; fac = None
        if len(R[lc][1]) >= 3 and ext_shape(R, lc, sls, branch_data) is not None:   # an external test (rf_ext)
            if rf_ext(p, lc, lf, sls, branch_data): done += 1
            else: skip.add(lc)
            continue
        if len(R[lc][1]) > 3: skip.add(lc); continue
        pins2 = []   # (two-input cells) the forks above the inputs, flattened at the end as rf_split does
        if len(R[lc][1]) == 2 and len(sls) == 2 and p.Wi is not None:
            for c in R[lc][1]:
                Wc = Q.writers(R, c)
                if len(Wc) == 1 and R[Wc[0]][0] == 'fork': pins2.append(R[Wc[0]][1])
        if len(R[lc][1]) == 3:   # a three-input cell: factored into a two-input one first (unabsorb)
            fac = rf_prefactor(p, lc, sls, branch_data)
            if fac is None: fac = rf_gate(p, lc, sls, branch_data)
            if fac is None: skip.add(lc); continue
        one = len(R[lc][1]) == 1; k3 = len(sls) == 3
        L0 = len(R); e = fresh(R); f = lambda i: e + 1 + i
        labs = {'lc': lc, 'lf': lf, 'sls': list(sls)}
        if not k3:
            if one: p.do(('forkcomm', lc, lf, f(0), f(1))); src = [lf, L0]
            else: p.do(('forkcomm2', lc, lf, f(0), f(1), f(2), f(3))); src = [L0, L0 + 1]
            lx, ln = lc, (None if one else lf)
        else:
            p.do(('forksplit', lf, 2, e))
            if one:
                p.do(('forkcomm', lc, lf, f(0), f(1)))           # lc: fork a [x0, x1]; lf: comp [x0] e; L0+1: comp [x1] z2
                p.do(('forkcomm', lf, L0, f(2), f(3)))           # lf: fork x0 [x00, x01]; L0: comp [x00] z0; L0+2: z1
                src = [L0, L0 + 2, L0 + 1]
            else:
                p.do(('forkcomm2', lc, lf, f(0), f(1), f(2), f(3)))           # L0+1: comp [x0,n0] e; L0+2: z2
                p.do(('forkcomm2', L0 + 1, L0, f(4), f(5), f(6), f(7)))       # L0+3: z0; L0+4: z1
                src = [L0 + 3, L0 + 4, L0 + 2]
        for k, ls in enumerate(sls):
            p.do(('absorb', src[k], ls)); do_unpack(p, ls)
        if k3:   # flatten the input fork trees: the inner fork merges into the outer one
            if one:
                labs['lx'] = lc; rf_merge(p, lf, lc, labs); lx, ln = labs['lx'], None
            else:
                labs['lx'], labs['ln'], labs['inn'] = lc, lf, L0
                labs['lx'] = rf_merge(p, L0 + 1, lc, labs)
                labs['ln'] = rf_merge(p, labs['inn'], labs['ln'], labs)
                lx, ln = labs['lx'], labs['ln']
        sls = labs['sls']
        outs = [R[ls][2] for ls in sls]
        ups = [k for k in range(len(sls)) if branch_data(outs[k]) is not None]
        tests = [k for k in range(len(sls)) if k not in ups]
        if len(tests) != 1 or not ups: return done
        lt = sls[tests[0]]; rk = Q.readers(R, outs[tests[0]])
        if len(rk) != 1 or R[rk[0]][0] != 'fork': return done
        lk = rk[0]
        if any(R[branch_data(outs[k])][1] not in R[lk][2] for k in ups): return done
        if not one:
            for k in ups:
                lu = sls[k]; lb = branch_data(outs[k]); F = R[lu][3]
                r0, r1 = uses_var(F, 0), uses_var(F, 1)
                if r0 and r1: continue
                if not r0 and not r1: return done
                if r0:
                    ax, an = lx, ln
                    it = R[lt][1]
                    if Q.writers(R, it[0]) == [ln]: p.do(('reorder', lt, [it[1], it[0]]))
                else:     # the update reads the second input: swap roles, the first input's copy is the extra wait
                    ax, an = ln, lx
                    ins = R[lu][1]; p.do(('reorder', lu, [ins[1], ins[0]]))
                    it = R[lt][1]
                    if Q.writers(R, it[0]) == [lx]: p.do(('reorder', lt, [it[1], it[0]]))
                it = R[lt][1]
                if not (Q.writers(R, it[0]) == [ax] and Q.writers(R, it[1]) == [an]): return done
                n2 = R[lu][1][1]; os_ = list(R[an][2])
                if os_[0] != n2: p.do(('forder', an, [n2] + [c for c in os_ if c != n2]))
                p.do(('unjoin', ax, an, lt, lk, lb, lu))
        # canonical fork order: the updates' copies (in slice order) first, then the test's
        upd_ins = [c for k in ups for c in R[sls[k]][1]]
        for lfk in [l for l in (lx, ln) if l is not None]:
            os_ = list(R[lfk][2]); want = [c for c in upd_ins if c in os_] + [c for c in os_ if c not in upd_ins]
            if want != os_: p.do(('forder', lfk, want))
        if fac:   # each factored comp `comp as pc f` now feeds a two-way fork of pc: one copy per comp (forkcomm2)
            pins = []
            for pc, as_ in fac:
                Lp = Q.writers(R, pc); lfp = Q.readers(R, pc)
                if len(Lp) != 1 or len(lfp) != 1 or R[lfp[0]][0] != 'fork' or len(R[lfp[0]][2]) != 2: return done
                for c in as_:
                    W = Q.writers(R, c)
                    if len(W) == 1 and R[W[0]][0] == 'fork' and R[W[0]][1] not in pins: pins.append(R[W[0]][1])
                e2 = fresh(R)
                p.do(('forkcomm2', Lp[0], lfp[0], e2, e2 + 1, e2 + 2, e2 + 3))
            rf_flatten(p, pins); rf_order(p, pins)
        if pins2: rf_flatten(p, pins2); rf_order(p, pins2)
        done += 1

def rf_split(p):
    """Unfused side: an update `comp [x] s F` whose fork feeds one branch (data) and one two-input test comp moves
    after a fork of `x` (forkcomm), so the test's copy can be absorbed into the test."""
    R = p.rs; done = 0; pins = []
    for lc in range(len(R)):
        r = R[lc]
        if r[0] != 'comp' or len(r[1]) not in (1, 2) or len(set(r[1])) != len(r[1]): continue
        rd = Q.readers(R, r[2])
        if len(rd) != 1 or R[rd[0]][0] != 'fork' or len(R[rd[0]][2]) != 2: continue
        lf = rd[0]; s0, s1 = R[lf][2]
        def kind(ch):
            a = Q.readers(R, ch)
            if len(a) != 1: return None
            q = R[a[0]]
            if q[0] == 'branch' and q[2] == ch: return 'data'
            if q[0] == 'comp' and len(q[1]) == 1:   # a one-input comp on the way to the branch (absorbed later)
                b = Q.readers(R, q[2])
                if len(b) == 1 and R[b[0]][0] == 'branch' and R[b[0]][2] == q[2]: return 'data'
            if q[0] == 'comp' and len(q[1]) in (1, 2): return 'test'
            return None
        ks = (kind(s0), kind(s1))
        if set(ks) != {'data', 'test'}: continue
        e = fresh(R)
        if len(r[1]) == 1:
            p.do(('forkcomm', lc, lf, e, e + 1)); done += 1
            if ks[0] != 'data': p.do(('forder', lc, [e + 1, e]))   # the update's copy first, as on the fused side
            continue
        # a two-input update (sqrtsub: n - odd): both inputs forked, one comp per copy (forkcomm2); the test's copy is
        # absorbed later, and its input forks are flattened into their parents so that duplicate reads dedupe
        L0 = len(R)
        p.do(('forkcomm2', lc, lf, e, e + 1, e + 2, e + 3)); done += 1
        for lfk in (lc, lf):    # the update's copy first
            if ks[0] != 'data': p.do(('forder', lfk, [R[lfk][2][1], R[lfk][2][0]]))
        for c in r[1]:    # remember the fork tree above each input; flattened after every split is done
            W = Q.writers(R, c)
            if len(W) == 1 and R[W[0]][0] == 'fork': pins.append(R[W[0]][1])
    rf_flatten(p, pins)   # every fork fed by the parent fork merges into it (so duplicate reads can dedupe)
    rf_order(p, pins)     # canonical order, as on the fused side: the updates' copies first, the test's last
    return done

def rf_extsplit(p):
    """Unfused side of `rf_ext`: a two-input comp `c` forked to two updates U0, U1, each forked to [the data of a
    branch, a copy read by one two-input test T] (the same T). `c` moves after its fork (forkcomm2) and each copy is
    absorbed into its update (then the updates read one copy of each input: flatten, dedupe). Each update
    `comp ins X F` is then factored as `comp [p] X v0` after `comp ins p F` (unabsorb), and moves after its fork
    (forkcomm): the branch reads a copy through `comp [p0] Xd v0` and the test absorbs its copy, as on the fused side.
    Returns the number of comps `c` done."""
    R = p.rs; done = 0
    def shape(lc):
        r = R[lc]
        if r[0] != 'comp' or len(r[1]) != 2 or len(set(r[1])) != 2: return None
        rd = Q.readers(R, r[2])
        if len(rd) != 1 or R[rd[0]][0] != 'fork' or len(R[rd[0]][2]) != 2: return None
        lf = rd[0]; T = None
        for o in R[lf][2]:
            a = Q.readers(R, o)
            if len(a) != 1 or R[a[0]][0] != 'comp' or len(R[a[0]][1]) < 2 or list(R[a[0]][1]).count(o) != 1: return None
            b = Q.readers(R, R[a[0]][2])
            if len(b) != 1 or R[b[0]][0] != 'fork' or len(R[b[0]][2]) != 2: return None
            kinds = []
            for z in R[b[0]][2]:
                q = Q.readers(R, z)
                if len(q) != 1: return None
                if R[q[0]][0] == 'branch' and R[q[0]][2] == z: kinds.append('d')
                elif R[q[0]][0] == 'comp' and len(R[q[0]][1]) == 2:
                    kinds.append('t'); T = q[0] if T in (None, q[0]) else -1
                else: return None
            if sorted(kinds) != ['d', 't']: return None
        if T is None or T < 0: return None
        return lf, T
    while True:
        hit = next(((lc, sh) for lc in range(len(R)) for sh in [shape(lc)] if sh is not None), None)
        if hit is None: return done
        lc, (lf, T) = hit
        cT = R[T][2]; ucs = [R[Q.readers(R, o)[0]][2] for o in R[lf][2]]   # the updates' output channels
        pins = []
        for c in R[lc][1]:
            W = Q.writers(R, c)
            if len(W) == 1 and R[W[0]][0] == 'fork' and R[W[0]][1] not in pins: pins.append(R[W[0]][1])
        L0 = len(R); e = fresh(R)
        p.do(('forkcomm2', lc, lf, e + 1, e + 2, e + 3, e + 4))
        for k in range(2):
            lu = Q.readers(R, R[L0 + k][2])[0]; ins = list(R[lu][1]); o = R[L0 + k][2]
            if ins[-1] != o: p.do(('reorder', lu, [c for c in ins if c != o] + [o]))
            p.do(('absorb', L0 + k, lu))
        rf_flatten(p, pins)
        for pin in pins:
            for lfk in [l for l in Q.readers(R, pin) if R[l][0] == 'fork']: comps_first(p, lfk)
        for uc in ucs:   # each update reads one copy of each input
            while True:
                lu = Q.writers(R, uc)[0]; hitd = None
                for lfk in range(len(R)):
                    if R[lfk][0] != 'fork': continue
                    cs = [c for c in R[lu][1] if c in R[lfk][2]]
                    if len(cs) >= 2: hitd = (lfk, cs); break
                if hitd is None: break
                p.do(('dedupe', hitd[0], lu, hitd[1][0], hitd[1][1]))
        for uc in ucs:
            lu = Q.writers(R, uc)[0]; ins = list(R[lu][1]); F = R[lu][3]
            pc = fresh(R)
            p.do(('unabsorb', lu, [], ins, pc, F, ('var', 0)))
            lfu = Q.readers(R, uc)[0]; L1 = len(R); e = fresh(R); os_ = list(R[lfu][2])
            p.do(('forkcomm', lu, lfu, e + 1, e + 2))      # lu: fork pc [..]; lfu: comp -> os_[0]; L1: comp -> os_[1]
            T = Q.writers(R, cT)[0]
            lt = lfu if Q.readers(R, os_[0]) == [T] else L1
            oc = R[lt][2]; it = list(R[T][1])
            if it[-1] != oc: p.do(('reorder', T, [c for c in it if c != oc] + [oc]))
            p.do(('absorb', lt, T))
        done += 1

def rf_litpush(p):
    """A literal comp `comp [k] o (lit v)` whose fork feeds comps that only wait on it (BDC_CONST_DATA already put
    the literal in their expressions): one literal comp per copy (forksplit / forkcomm), each then absorbed into its
    reader, which waits on its own copy of k, as a ring-fused cell does (iterative_division's unfused side)."""
    R = p.rs; done = 0
    while True:
        hit = None
        for lc, r in enumerate(R):
            if r[0] != 'comp' or len(r[1]) != 1 or r[3][0] != 'lit': continue
            rd = Q.readers(R, r[2])
            if len(rd) != 1 or R[rd[0]][0] != 'fork' or len(R[rd[0]][2]) < 2: continue
            ok = True
            for o in R[rd[0]][2]:
                a = Q.readers(R, o)
                if len(a) != 1 or R[a[0]][0] != 'comp' or uses_var(R[a[0]][3], list(R[a[0]][1]).index(o)): ok = False
            if ok: hit = (lc, rd[0]); break
        if hit is None: return done
        lc, lf = hit; k = R[lc][1][0]
        Wk = Q.writers(R, k); pin = R[Wk[0]][1] if len(Wk) == 1 and R[Wk[0]][0] == 'fork' else k
        while True:
            n = len(R[lf][2]); nxt = None
            if n > 2:
                e = fresh(R); p.do(('forksplit', lf, n - 1, e)); nxt = len(R) - 1   # lf: fork o [e, last]
            e0 = fresh(R)
            p.do(('forkcomm', lc, lf, e0, e0 + 1))   # lc: fork k [e0, e0+1]; lf: comp [e0] (e or first) lit
            if nxt is None: break
            lc, lf = lf, nxt
        rf_flatten(p, [pin]); rf_order(p, [pin]); done += 1

def root_key(R, c, NA, depth=0):
    """A description of where channel c comes from that does not depend on channel numbers (except the inputs,
    which keep theirs on both sides): through forks to the first other writer."""
    seen = 0
    while True:
        W = Q.writers(R, c)
        if not W: return ('in', c) if c < NA else ('free',)
        r = R[W[0]]
        if r[0] == 'fork' and seen < 50: c = r[1]; seen += 1; continue
        if depth >= 4: return (r[0],)
        if r[0] == 'branch': return ('branch', r[3] == c, root_key(R, r[2], NA, depth + 1))
        if r[0] == 'comp': return ('comp', repr(r[3]), tuple(root_key(R, x, NA, depth + 1) for x in r[1]))
        return (r[0],)

def rf_canon_forks(p):
    """Fork outputs read by comps, sorted (stably, among themselves) by what the reader computes and where its other
    inputs come from: an order both sides reach whatever order the planner built the copies in."""
    R = p.rs
    for lf, r in enumerate(R):
        if r[0] != 'fork': continue
        os_ = list(r[2]); pos = []; keys = []
        for i, o in enumerate(os_):
            rd = Q.readers(R, o)
            if len(rd) == 1 and R[rd[0]][0] == 'comp':
                q = R[rd[0]]; others = tuple(root_key(R, x, p.NA) for x in q[1] if x != o)
                pos.append(i); keys.append((repr(q[3]), list(q[1]).index(o), repr(others)))
        if len(pos) < 2: continue
        order = sorted(range(len(pos)), key=lambda j: keys[j])
        new = list(os_)
        for slot, j in zip(pos, order): new[slot] = os_[pos[j]]
        if new != os_: p.do(('forder', lf, new))

def normal_form(rs, rf=None, wi=None, ext=0):
    p = FPlan(rs); R = p.rs
    if wi is not None: p.Wi, p.NA = wi
    # BDC_CONST_DATA's move, on both sides: a comp reads a constant-only channel as the literal
    for l, r in enumerate(R):
        if r[0] != 'comp': continue
        for i, ch in enumerate(r[1]):
            cc = const_class(R, ch)
            if cc is None or not uses_var(R[l][3], i) or R[l][2] in cc[1]: continue
            p.do(('constdata', l, i, cc[0], cc[1]))
    def fuse_loop():
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
    fuse_loop()
    # BDC_RING_FUSE: after maximal fusion (a packed cell's inputs are then those of its region)
    if rf == 'unpack': p.rf = rf_unpack(p)
    elif rf == 'split':
        if ext and p.Wi is not None: p.rf = rf_extsplit(p)   # the other side unpacked a cell with an external test
        p.rf += rf_split(p)
    lp = rf_litpush(p) if (rf and p.Wi is not None) else 0
    if p.rf or lp: fuse_loop()
    if rf == 'unpack':   # slices left inside a fused expression (no fork between the cell and its readers)
        for l, r in enumerate(R):
            if r[0] == 'comp' and unslice_n(8, r[3]) != r[3]: p.do(('unpack', l)); p.rf += 1
    if p.Wi is not None and rf: rf_canon_forks(p)
    # canonical input order: first read in the expression
    for l, r in enumerate(R):
        if r[0] != 'comp' or len(r[1]) < 2: continue
        order = first_vars(r[3], [])
        ins = list(r[1]); ins2 = [ins[i] for i in order if i < len(ins)]
        ins2 += [c for c in ins if c not in ins2]
        if ins2 != ins: p.do(('reorder', l, ins2))
    p.drops()
    return p

RF_STEPS = ('forkcomm2', 'unpack', 'unjoin', 'permute', 'forkmerge', 'unabsorb')
CTL = None
WUSED = None

def mutate(R, ctl):
    """Negative controls on B (each changes what a ring-fused graph computes; each must be refused).
    slice_low: every multi-result slice reads the low part (research's NEGCTL mistake, in the model).
    upd_plus2: the packed cell's update part computes x + 2 instead of x + 1.
    part_plus1: the first packed cell's highest part computes (part + 1), whatever it is (sqrtsub: n - odd + 1)."""
    out = []; hits = 0
    for r in R:
        if ctl == 'slice_low' and r[0] == 'comp' and r[3][0] == 'un' and r[3][1] == ('trunci',):
            sh = r[3][3]
            if sh[0] == 'bin' and sh[1] == ('shrui',) and sh[3] == ('var', 0) and sh[4][0] == 'lit' and sh[4][1] > 0:
                r = ('comp', r[1], r[2], ('un', ('trunci',), r[3][2], ('bin', ('shrui',), sh[2], sh[3], ('lit', 0))))
                hits += 1
        if ctl == 'upd_plus2' and r[0] == 'comp' and r[3][0] == 'bin' and r[3][1] == ('addi',) and \
                r[3][4][0] == 'bin' and r[3][4][1] == ('shli',):
            t = r[3][4]
            if t[3] == ('bin', ('addi',), 32, ('var', 0), ('lit', 1)):
                t = ('bin', ('shli',), t[2], ('bin', ('addi',), 32, ('var', 0), ('lit', 2)), t[4])
                r = ('comp', r[1], r[2], ('bin', ('addi',), r[3][2], r[3][3], t)); hits += 1
        if ctl == 'part_plus1' and r[0] == 'comp' and r[3][0] == 'bin' and r[3][1] == ('addi',) and \
                r[3][4][0] == 'bin' and r[3][4][1] == ('shli',) and not hits:
            t = r[3][4]   # the first packed cell's highest part computes (part + 1) (32-bit parts)
            t = ('bin', ('shli',), t[2], ('bin', ('addi',), 32, t[3], ('lit', 1)), t[4])
            r = ('comp', r[1], r[2], ('bin', ('addi',), r[3][2], r[3][3], t)); hits += 1
        out.append(r)
    assert hits, 'control ' + ctl + ' found nothing to mutate'
    print(f'fuse_check: control {ctl}: {hits} rule(s) mutated')
    return out

def ser_step_rf(st):
    if st[0] == 'unabsorb':
        _, lq, bs, as_, pc, f, g = st
        return f'.unabsorb {lq} {PP.ser(list(bs))} {PP.ser(list(as_))} {pc} {PP.ser(f)} {PP.ser(g)}'
    return Q.ser_step(st) if st[0] in RF_STEPS else '.base (' + Q.ser_step(st) + ')'

TEMPLATE_RF = (Q.TEMPLATE.replace('import Formal.Rewrite.Steps.ScriptSound', 'import Formal.Rewrite.Steps.ScriptRF')
               .replace('List Step :=', 'List StepRF :=').replace('runScript rules', 'runScriptRF rules')
               .replace('runScript_sound', 'runScriptRF_sound'))
assert TEMPLATE_RF.count('runScriptRF_sound') == 4 and TEMPLATE_RF.count('List StepRF') == 2

W_STEPS = ('unpackw', 'undedupe', 'back')

def ser_step_w(st):
    if st[0] == 'unpackw': return f'.unpackw {st[1]} {PP.ser(list(st[2]))}'
    if st[0] == 'undedupe':
        _, lf, lc, a, b, os2, ins2, F2 = st
        return f'.undedupe {lf} {lc} {a} {b} {PP.ser(list(os2))} {PP.ser(list(ins2))} {PP.ser(F2)}'
    if st[0] == 'back':
        _, ed, app, ss = st
        return (f'.back [' + ', '.join(f'({l}, {PP.ser(r)})' for l, r in ed) + '] ' + PP.ser(list(app)) +
                ' [' + ', '.join(ser_step_rf(s) for s in ss) + ']')
    return '.rf (' + ser_step_rf(st) + ')'

# Under the width assumption (Formal.Rewrite.Steps.Width): the scripts run in runScriptW, and the pass theorems carry
# the hypothesis hW (every input token fits its declared width Wi).
TEMPLATE_W = (TEMPLATE_RF.replace('import Formal.Rewrite.Steps.ScriptRF', 'import Formal.Rewrite.Steps.Width')
              .replace('List StepRF :=', 'List StepW :=').replace('runScriptRF rules', 'runScriptW {NA} Wi rules')
              .replace('def s1 : List StepW', '/-- Declared width of each input channel (0: control token, no width). -/\n'
                       'def Wi : List Nat := {Wi}\n\ndef s1 : List StepW')
              .replace('runScriptRF_sound h1).fwd (', 'runScriptW_sound h1).fwd (inP_mk h0 hW) (')
              .replace('runScriptRF_sound h2).symm.fwd (', 'runScriptW_sound h2).symm.fwd (inP_mk h0 hW) (')
              .replace('runScriptRF_sound h2).fwd (', 'runScriptW_sound h2).fwd (inP_mk h0 hW) (')
              .replace('runScriptRF_sound h1).bwd (', 'runScriptW_sound h1).bwd (inP_mk h0 hW) (')
              .replace('theorem pass_forward {{', '/-- Under the width assumption `hW`: every input token fits its declared width. -/\n'
                       'theorem pass_forward_w {{')
              .replace('theorem pass_backward {{', '/-- Under the width assumption `hW`: every input token fits its declared width. -/\n'
                       'theorem pass_backward_w {{')
              .replace('σ0 ch = [])\n    (hr :', 'σ0 ch = [])\n    (hW : ∀ ch v, v ∈ σ0 ch → InW Wi ch v) (hr :')
              .replace('#print axioms Eq2CheckRun.pass_forward\n', '#print axioms Eq2CheckRun.pass_forward_w\n')
              .replace('#print axioms Eq2CheckRun.pass_backward\n', '#print axioms Eq2CheckRun.pass_backward_w\n'))
assert TEMPLATE_W.count('inP_mk h0 hW') == 4 and TEMPLATE_W.count('(hW :') == 2 and TEMPLATE_W.count('pass_forward_w') == 2, TEMPLATE_W

def refuse(why):
    print('fuse_check: REFUSED -- ' + why); return 2

def input_widths(path, NA):
    """Declared width of each input channel (0 for a control token, which carries no width); None if unknown."""
    try: d = json.load(open(path))
    except (OSError, ValueError): return None
    ch = d['chan']; out = []
    for c in range(NA):
        e = ch[c] if c < len(ch) else None
        if e is None: return None
        w, ctl = e
        out.append(0 if ctl else int(w))
    return out

def parse_env(s):
    return dict(kv.split('=', 1) for kv in s.split(',') if kv) if s else {}

def imp(mlir, out, ns, env):
    env = dict(env); env['FA_W_LOG'] = out + '.widths.json'
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
    global CTL
    if '--ctl' in args:   # negative controls: mutate B's rules after import (see controls/fuse/README.md)
        i = args.index('--ctl'); CTL = args[i + 1]; del args[i:i + 2]
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
    if rc == 0 and WUSED: print(f'fuse_check: PROVED UNDER THE WIDTH ASSUMPTION (every input token fits its declared '
                                f'width, Wi = {WUSED[0]}; pass_forward_w / pass_backward_w) -- {args[1]} [{eb}] is equal to '
                                f'{args[0]} [{ea}] (Lean: {tmp}/Eq2CheckRun.lean; axioms propext, Classical.choice, Quot.sound)')
    elif rc == 0: print(f'fuse_check: PROVED -- {args[1]} [{eb}] is equal to {args[0]} [{ea}] '
                      f'(Lean: {tmp}/Eq2CheckRun.lean; axioms propext, Classical.choice, Quot.sound)')
    return rc

def run(fa, fb, ea, eb, tmp):
    Ra, Na, oa, naa = imp(fa, os.path.join(tmp, 'A.lean'), 'FuA', ea)
    Rb, Nb, ob, nab = imp(fb, os.path.join(tmp, 'B.lean'), 'FuB', eb)
    if CTL:
        Rb = mutate(Rb, CTL)
        open(os.path.join(tmp, 'B.lean'), 'w').write('-- mutated: ' + CTL + '\n')
    if Ra == Rb: print('fuse_check: A and B import to the same rules'); return 3
    if naa != nab: return refuse('different numbers of inputs')
    if oa is None or ob is None: return refuse('no data output channel (chOut)')
    # declared input widths (MLIR argument types, read by bdc's emitter): the width assumption is stated in these
    wa, wb = (input_widths(os.path.join(tmp, f + '.lean.widths.json'), naa) for f in ('A', 'B'))
    wi = (wa, naa) if (wa is not None and wa == wb) else None
    if wi is None: print('fuse_check: input widths unavailable or ambiguous (A %r, B %r): no width assumption' % (wa, wb))
    # BDC_RING_FUSE: unpack a fused side's packed cells; split the other side's update to meet it.
    # Pass 1 is the planner without widths (unconditional theorems); only if its normal forms differ, pass 2 plans
    # with the width map (width-checked steps; the theorems then carry the width assumption).
    n1, n2 = os.path.join(tmp, 'nf1.lean'), os.path.join(tmp, 'nf2.lean')
    mp = os.path.join(tmp, 'maps.json')
    for w in ([None, wi] if wi is not None else [None]):
        try:
            pa, pb = normal_form(Ra, 'unpack', w), normal_form(Rb, 'unpack', w)
            if pb.rf and not pa.rf: pa = normal_form(Ra, 'split', w, getattr(pb, 'ext', 0))
            elif pa.rf and not pb.rf: pb = normal_form(Rb, 'split', w, getattr(pa, 'ext', 0))
        except AssertionError as ex:   # a planner step did not apply: no plan from this pass
            if w is wi or wi is None: return refuse('planner: %s' % ex)
            continue
        open(n1, 'w').write('def rules : List Rule := ' + PP.ser_rules(pa.rs) + '\n')
        open(n2, 'w').write('def rules : List Rule := ' + PP.ser_rules(pb.rs) + '\n')
        ri = subprocess.run([sys.executable, os.path.join(HERE, 'rules_iso.py'), n1, n2, mp], capture_output=True, text=True)
        if ri.returncode == 0: break
    WMODE = any(st[0] in W_STEPS for st in pa.steps + pb.steps)
    RF = bool(pa.rf or pb.rf or getattr(pa, 'rfs', 0) or getattr(pb, 'rfs', 0))
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
    RF = RF or any(st[0] in RF_STEPS for st in pa.steps + pb.steps)
    ser = ser_step_w if WMODE else ser_step_rf if RF else Q.ser_step
    s1 = '[' + ', '.join(ser(s) for s in pa.steps) + ']'
    s2 = '[' + ', '.join(ser(s) for s in pb.steps) + ']'
    lean = (TEMPLATE_W if WMODE else TEMPLATE_RF if RF else Q.TEMPLATE).format(Wi=(wi[0] if wi else []), inp=f'{os.path.abspath(fa)} [{ea}]', out=f'{os.path.abspath(fb)} [{eb}]',
                             rin=PP.ser_rules(Ra), rout=PP.ser_rules(Rb), s1=s1, s2=s2, P=P, Pi=Pi, T=T, Ti=Ti,
                             NA=naa, oi=oa, oo=ob, **Q.lits(pa, pb)).replace('eq2_check.py', 'fuse_check.py')
    lf = os.path.join(tmp, 'Eq2CheckRun.lean'); open(lf, 'w').write(lean)
    env = dict(os.environ); env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')
    global WUSED
    WUSED = (wi[0], naa) if WMODE else None
    b = subprocess.run(['lake', 'build', 'Formal.Rewrite.Steps.Width' if WMODE else
                        'Formal.Rewrite.Steps.ScriptRF' if RF else 'Formal.Rewrite.Steps.ScriptSound',
                        'Formal.Rewrite.Rename'], cwd=LEAN,
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
