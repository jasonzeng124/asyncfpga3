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
    rf = 0
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

def rf_unpack(p):
    """Fused side (BDC_RING_FUSE): a one- or two-input packed cell, its fork and its two or three slices become the
    test and the updates as separate comps; an update stops waiting for the input it does not read (unjoin).
    Returns the number of cells done."""
    R = p.rs; done = 0
    def branch_data(ch):
        rd = Q.readers(R, ch); return rd[0] if len(rd) == 1 and R[rd[0]][0] == 'branch' and R[rd[0]][2] == ch else None
    while True:
        hit = None
        for lc, r in enumerate(R):
            if r[0] != 'comp' or len(r[1]) not in (1, 2): continue
            Wf = Q.readers(R, r[2])
            if len(Wf) != 1 or R[Wf[0]][0] != 'fork' or len(R[Wf[0]][2]) not in (2, 3): continue
            lf = Wf[0]; sl = [Q.readers(R, z) for z in R[lf][2]]
            if not all(len(a) == 1 and R[a[0]][0] == 'comp' and len(R[a[0]][1]) == 1 for a in sl): continue
            if not all(unslice_n(8, Q.subst(R[a[0]][3], [r[3]])) != Q.subst(R[a[0]][3], [r[3]]) for a in sl): continue
            hit = (lc, lf, [a[0] for a in sl]); break
        if hit is None: return done
        lc, lf, sls = hit; one = len(R[lc][1]) == 1; k3 = len(sls) == 3
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
            p.do(('absorb', src[k], ls)); p.do(('unpack', ls))
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
                if r0: ax, an = lx, ln
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
        done += 1

def rf_split(p):
    """Unfused side: an update `comp [x] s F` whose fork feeds one branch (data) and one two-input test comp moves
    after a fork of `x` (forkcomm), so the test's copy can be absorbed into the test."""
    R = p.rs; done = 0
    for lc in range(len(R)):
        r = R[lc]
        if r[0] != 'comp' or len(r[1]) != 1: continue
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
        p.do(('forkcomm', lc, lf, e, e + 1)); done += 1
        if ks[0] != 'data': p.do(('forder', lc, [e + 1, e]))   # the update's copy first, as on the fused side
    return done

def normal_form(rs, rf=None):
    p = FPlan(rs); R = p.rs
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
    elif rf == 'split': p.rf = rf_split(p)
    if p.rf: fuse_loop()
    if rf == 'unpack':   # slices left inside a fused expression (no fork between the cell and its readers)
        for l, r in enumerate(R):
            if r[0] == 'comp' and unslice_n(8, r[3]) != r[3]: p.do(('unpack', l)); p.rf += 1
    # canonical input order: first read in the expression
    for l, r in enumerate(R):
        if r[0] != 'comp' or len(r[1]) < 2: continue
        order = first_vars(r[3], [])
        ins = list(r[1]); ins2 = [ins[i] for i in order if i < len(ins)]
        ins2 += [c for c in ins if c not in ins2]
        if ins2 != ins: p.do(('reorder', l, ins2))
    p.drops()
    return p

RF_STEPS = ('forkcomm2', 'unpack', 'unjoin', 'permute', 'forkmerge')
CTL = None

def mutate(R, ctl):
    """Negative controls on B (each changes what a ring-fused graph computes; each must be refused).
    slice_low: every multi-result slice reads the low part (research's NEGCTL mistake, in the model).
    upd_plus2: the packed cell's update part computes x + 2 instead of x + 1."""
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
        out.append(r)
    assert hits, 'control ' + ctl + ' found nothing to mutate'
    print(f'fuse_check: control {ctl}: {hits} rule(s) mutated')
    return out

def ser_step_rf(st):
    return Q.ser_step(st) if st[0] in RF_STEPS else '.base (' + Q.ser_step(st) + ')'

TEMPLATE_RF = (Q.TEMPLATE.replace('import Formal.Rewrite.Steps.ScriptSound', 'import Formal.Rewrite.Steps.ScriptRF')
               .replace('List Step :=', 'List StepRF :=').replace('runScript rules', 'runScriptRF rules')
               .replace('runScript_sound', 'runScriptRF_sound'))
assert TEMPLATE_RF.count('runScriptRF_sound') == 4 and TEMPLATE_RF.count('List StepRF') == 2

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
    if rc == 0: print(f'fuse_check: PROVED -- {args[1]} [{eb}] is equal to {args[0]} [{ea}] '
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
    # BDC_RING_FUSE: unpack a fused side's packed cells; split the other side's update to meet it
    pa, pb = normal_form(Ra, 'unpack'), normal_form(Rb, 'unpack')
    if pb.rf and not pa.rf: pa = normal_form(Ra, 'split')
    elif pa.rf and not pb.rf: pb = normal_form(Rb, 'split')
    RF = bool(pa.rf or pb.rf or getattr(pa, 'rfs', 0) or getattr(pb, 'rfs', 0))
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
    RF = RF or any(st[0] in RF_STEPS for st in pa.steps + pb.steps)
    ser = ser_step_rf if RF else Q.ser_step
    s1 = '[' + ', '.join(ser(s) for s in pa.steps) + ']'
    s2 = '[' + ', '.join(ser(s) for s in pb.steps) + ']'
    lean = (TEMPLATE_RF if RF else Q.TEMPLATE).format(inp=f'{os.path.abspath(fa)} [{ea}]', out=f'{os.path.abspath(fb)} [{eb}]',
                             rin=PP.ser_rules(Ra), rout=PP.ser_rules(Rb), s1=s1, s2=s2, P=P, Pi=Pi, T=T, Ti=Ti,
                             NA=naa, oi=oa, oo=ob, **Q.lits(pa, pb)).replace('eq2_check.py', 'fuse_check.py')
    lf = os.path.join(tmp, 'Eq2CheckRun.lean'); open(lf, 'w').write(lean)
    env = dict(os.environ); env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')
    b = subprocess.run(['lake', 'build', 'Formal.Rewrite.Steps.ScriptRF' if RF else 'Formal.Rewrite.Steps.ScriptSound',
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
