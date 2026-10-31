#!/usr/bin/env python3
"""autoproof: generate an all-inputs token-level Lean proof for a loop kernel (probe C-vk2).

    python3 autoproof.py MLIR C_FILE FUNC --name NAME [--seg-module MOD --graph-ns NS]
                         [--out FILE.lean | --combined FILE.lean] [--dfargs ...]
                         [--vecs "a,b a,b"] [--seed N]

Input: the handshake MLIR bdc consumes and the C function. Output: a Lean file proving

    theorem auto_computes {fuel x0 .. r : Nat} (h : kC fuel x0 .. = some r) :
      (exists n, Run (step G) (St T0 [x0, ..]) n (St Tfin [r])) /\
      (forall m t, Run .. m t -> Terminal (step G) t -> t = St Tfin [r]) /\
      (exists n, forall m u, Run .. m u -> m <= n)

where `kC` is the C function transcribed by `cfront.py` (generated, readable, printed in
the file next to the C source lines) and the graph is dfimport's export of the MLIR.
That is the statement of the hand-written theorems in Formal/Net/<K>HwProof.lean, with
the generated transcription in place of the hand one.

How (nothing kernel-specific):
 1. dfimport (C-8i, imported unchanged) exports the graph and its symbolic segments: a
    template automaton, one branch fact per segment.
 2. cfront cuts the C function at its tests: a test-point automaton.
 3. Co-simulation on many inputs (the kernel's vectors, random and boundary values)
    aligns the two automata step by step (each step consumes exactly one test on both
    sides) and GUESSES: the C test point of each template (`L`), each template variable
    as an expression over the C state there (`rho`, from a pool of C variables, the
    point's test and the subexpressions of its outgoing code), constant C variables and
    copies as template invariants (`Is`), and the pairing of C edges with graph edges (`M`).
    Guesses are checked numerically on random C states before any Lean is written.
 4. The Lean file instantiates `Formal.Net.Auto.sim_call` (AutoLib.lean, proved once):
    the coverage of the pairing is `decide`d, each pairing's obligation (fact outcome,
    new environment, invariant) is split into component lemmas, each closed by `rfl` or by
    the generic tactic `auto_ops` after abstraction of numerically equal subterms (`abs_eq`,
    recursively), the entry by `rfl`/`auto_ops`, and every-schedule determinacy by C-8i's `determinate` /
    `no_longer` (as in the hand proofs). Lean checks everything; the guesses are not
    trusted. A wrong guess or an unprovable obligation makes Lean fail: NOT PROVED.

Exit: 0 Lean file written (it still has to be checked by Lean), 2 no correspondence found
(not proved; reason printed), 1 the co-simulation found an input where the graph's
result differs from the C's (a counterexample under the Python semantics; printed).
"""
import argparse
import os
import random
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "dfimport"))
import cfront  # noqa: E402
from cfront import ev, subst, show  # noqa: E402

M32 = 1 << 32


class NotProved(Exception):
    pass


def e_lean(e):
    t = e[0]
    if t == "var":
        return f"(.var {e[1]})"
    if t == "lit":
        return f"(.lit {e[1]})"
    if t == "un":
        o = e[1]
        os_ = f"(.extsi {o[1]})" if isinstance(o, tuple) else f".{o}"
        return f"(.un {os_} {e[2]} {e_lean(e[3])})"
    if t == "bin":
        o = e[1]
        os_ = f"(.cmpi .{o[1]})" if isinstance(o, tuple) else f".{o}"
        return f"(.bin {os_} {e[2]} {e_lean(e[3])} {e_lean(e[4])})"
    return f"(.sel {e_lean(e[1])} {e_lean(e[2])} {e_lean(e[3])})"


def lst(xs):
    return "[" + ", ".join(e_lean(x) for x in xs) + "]"


def size(e):
    return 1 + sum(size(x) for x in e[1:] if isinstance(x, tuple) and x and x[0] in ("var", "lit", "un", "bin", "sel"))


def subexprs(e, acc):
    if e[0] in ("var", "lit"):
        return
    if e not in acc:
        acc.append(e)
    for x in e[1:]:
        if isinstance(x, tuple) and x and x[0] in ("var", "lit", "un", "bin", "sel"):
            subexprs(x, acc)


def maxvar(e):
    if e[0] == "var":
        return e[1]
    if e[0] == "lit":
        return -1
    return max([-1] + [maxvar(x) for x in e[1:] if isinstance(x, tuple) and x and
                       x[0] in ("var", "lit", "un", "bin", "sel")])


def vars_of(e, acc=None):
    acc = [] if acc is None else acc
    if e[0] == "var":
        acc.append(e)
    elif e[0] != "lit":
        for x in e[1:]:
            if isinstance(x, tuple) and x and x[0] in ("var", "lit", "un", "bin", "sel"):
                vars_of(x, acc)
    return acc


def is_bool(e):
    return e[0] == "bin" and isinstance(e[1], tuple)


# ---------------------------------------------------------------------------
# graph side

class GA:
    def __init__(self, mlir):
        import mlir2lean
        env = {x: y for x, y in os.environ.items() if not x.startswith("BDC_")}
        os.environ.clear()
        os.environ.update(env)
        self.g = mlir2lean.Graph(mlir)
        self.templates, edges = mlir2lean.explore(self.g)
        self.edges = []
        for k, (ti, facts, sched, tj, sig, _) in enumerate(edges):
            if len(facts) != 1:
                raise NotProved(f"segment {k} has {len(facts)} branch facts (autoproof needs exactly one)")
            self.edges.append(dict(i=k, src=ti, fact=facts[0][0], br=facts[0][1], sig=sig, dst=tj))
        srcs = {e["src"] for e in self.edges}
        fins = [k for k in range(len(self.templates)) if k not in srcs]
        if len(fins) != 1:
            raise NotProved(f"{len(fins)} final templates (expected one)")
        self.fin = fins[0]
        nv = max([-1] + [maxvar(x) for row in self.templates[self.fin] for x in row]) + 1
        if nv != 1:
            raise NotProved(f"the final template has {nv} variables (expected one: the result)")
        self.nargs = sum(1 for a in self.g.func.args if not a.is_control)

    def nvars(self, k):
        return max([-1] + [maxvar(x) for row in self.templates[k] for x in row]) + 1

    def run(self, ins, fuel):
        k, env, trace = 0, list(ins), []
        for _ in range(fuel):
            out = [e for e in self.edges if e["src"] == k]
            b = ev(out[0]["fact"], env) % 2 == 1
            e = [x for x in out if x["br"] == b][0]
            trace.append((k, env, e["i"]))
            env = [ev(s, env) for s in e["sig"]]
            k = e["dst"]
            if k == self.fin:
                return env[0], trace
        return None, trace


# ---------------------------------------------------------------------------
# correspondence

def inputs(nargs, vecs, seed):
    rnd = random.Random(seed)
    special = [0, 1, 2, 3, 5, 7, 12, 18, 2 ** 31 - 1, 2 ** 31, 2 ** 32 - 1, 2 ** 32 - 2, 2 ** 16]
    out = [tuple(x % M32 for x in v) for v in vecs]
    for _ in range(60):
        out.append(tuple(rnd.choice(special) for _ in range(nargs)))
    for _ in range(120):
        out.append(tuple(rnd.randrange(64) for _ in range(nargs)))
    for _ in range(120):
        out.append(tuple(rnd.randrange(M32) for _ in range(nargs)))
    for _ in range(60):
        out.append(tuple(rnd.randrange(-64, 64) % M32 for _ in range(nargs)))
    return out


class Corr:
    def __init__(self, ga, P, vecs, seed=1, fuel=400):
        self.ga, self.P = ga, P
        nT = len(ga.templates)
        obs = {k: [] for k in range(nT)}      # k -> [(p, sigma, env)]
        pairs = {}                            # (k, ce index) -> set of graph edge indices
        self.cex = None
        for ins in inputs(ga.nargs, vecs, seed):
            gr, gt = ga.run(ins, fuel)
            cr, ct = cfront.run(P, list(ins), fuel)
            n = min(len(gt), len(ct))
            for i in range(n):
                k, env, gi = gt[i]
                p, st, ci = ct[i]
                obs[k].append((p, st, env))
                pairs.setdefault((k, ci), set()).add(gi)
            if gr is not None and cr is not None and gr != cr and self.cex is None:
                self.cex = (ins, gr, cr, len(gt), len(ct))
            if (gr is None) != (cr is None) and len(gt) != len(ct) and self.cex is None:
                if gr is not None or cr is not None:
                    self.cex = (ins, gr, cr, len(gt), len(ct))
        self.obs, self.pairs = obs, pairs

    def infer(self):
        P, ga, obs = self.P, self.ga, self.obs
        nT = len(ga.templates)
        self.K = [k for k in range(nT) if k != ga.fin]
        L = [None] * nT
        for k in self.K:
            ps = {o[0] for o in obs[k]}
            if len(ps) > 1:
                raise NotProved(f"template T{k}: aligned with C test points {sorted(ps)}")
            if ps:
                L[k] = ps.pop()
        self.L = L
        if L[0] != P.start:
            raise NotProved(f"T0 aligns with C test point {L[0]}, but the C starts at {P.start}")
        self.derived = []          # (k', k, graph edge, C edge): templates never reached by the co-simulation
        self.infer_inv()
        self.infer_rho()
        self.infer_matches()
        self.bad = self.search()

    def infer_inv(self):
        """constant C variables and equal pairs of C variables at each template (the
        rewrite direction of an equality is towards the lower slot, e.g. a copy of a parameter)"""
        nv = len(self.P.vars)
        self.Is = []
        for k in range(len(self.ga.templates)):
            I = []
            if k in self.K and self.obs[k]:
                const = set()
                for i in range(nv):
                    vals = {o[1][i] for o in self.obs[k]}
                    if len(vals) == 1:
                        I.append((("var", i), ("lit", vals.pop())))
                        const.add(i)
                for i in range(nv):
                    for j in range(i):
                        if i not in const and j not in const and all(o[1][i] == o[1][j] for o in self.obs[k]):
                            I.append((("var", i), ("var", j)))
                            break
            self.Is.append(I)

    def pool(self, p):
        P = self.P
        cands = [("var", i) for i in range(len(P.vars))]
        sub = []
        roots = [P.tests[p]]
        for e in P.edges:
            if e[0] != p:
                continue
            roots += [x for i, x in enumerate(e[2]) if x != ("var", i)]
            if e[3] is not None:
                roots.append(subst(e[2], P.tests[e[3]]))
            else:
                roots.append(subst(e[2], e[4]))
        for r in roots:
            subexprs(r, sub)
        sub.sort(key=size)
        for e in sub:
            if e not in cands:
                cands.append(e)
                if is_bool(e):
                    cands.append(("bin", ("cmpi", "eq"), 32, e, ("lit", 0)))
        return cands

    def infer_rho(self):
        """every candidate consistent with the observations, in preference order; `search`
        picks among them"""
        self.cands, self.sel = {}, {}
        for k in self.K:
            if not self.obs[k]:
                continue
            pool = self.pool(self.L[k])
            for j in range(self.ga.nvars(k)):
                vals = [(o[1], o[2][j]) for o in self.obs[k]]
                cs = [c for c in pool if all(ev(c, st) == v for st, v in vals)]
                vs = {v for _, v in vals}
                if len(vs) == 1:
                    cs.append(("lit", vs.pop()))
                if not cs:
                    raise NotProved(f"T{k} variable {j}: no expression over the C state at test point "
                                    f"{self.L[k]} matches its values (e.g. {vals[0][1]} at C state {vals[0][0]})")
                self.cands[(k, j)] = cs
                self.sel[(k, j)] = 0
        self.set_rho()

    def set_rho(self):
        self.rho = [[self.cands[(k, j)][self.sel[(k, j)]] for j in range(self.ga.nvars(k))]
                    if k in self.K and self.obs[k] else [] for k in range(len(self.ga.templates))]
        for k2, k, gi, ci in self.derived:
            self.rho[k2] = [subst(self.rho[k], x) for x in self.ga.edges[gi]["sig"]]

    def polarity(self, k, n=400, seed=5):
        """does the graph fact out of template k agree with the C test at L[k] (True), or is it
        its negation (False)? Numerical, on random C states satisfying k's invariant."""
        rnd = random.Random(seed)
        nv = len(self.P.vars)
        fact = [e for e in self.ga.edges if e["src"] == k][0]["fact"]
        gf = subst(self.rho[k], fact)
        t = self.P.tests[self.L[k]]
        fixed = {a[1]: b[1] for a, b in self.Is[k] if b[0] == "lit"}
        eqs = [(a[1], b[1]) for a, b in self.Is[k] if b[0] == "var"]
        same = diff = 0
        for _ in range(n):
            st = [fixed.get(i, rnd.choice([rnd.randrange(M32), rnd.randrange(40)])) for i in range(nv)]
            for i, j in eqs:
                st[i] = st[j]
            if (ev(t, st) % 2) == (ev(gf, st) % 2):
                same += 1
            else:
                diff += 1
        if same and diff:
            raise NotProved(f"T{k}: the graph's branch fact is neither the C test at point {self.L[k]} nor its negation")
        return diff == 0

    def search(self, rounds=200):
        """greedy repair: advance the candidate of a variable a failing obligation blames"""
        for _ in range(rounds):
            bad = self.check(n=400)
            if not bad:
                return []
            m, why, st, blame = bad[0]
            moved = False
            for kj in blame:
                if kj in self.sel and self.sel[kj] + 1 < len(self.cands[kj]):
                    self.sel[kj] += 1
                    moved = True
                    break
            if not moved:
                return bad
            self.set_rho()
        return self.check()

    def infer_matches(self):
        """pair C edges with graph edges, template by template; a template the co-simulation never
        reached (an infeasible path of the graph, e.g. isprime's first `s <= half` test) is derived
        from its predecessor: same C test point as the C edge's destination, rho = the segment's
        sig over the predecessor's rho, provided that edge's C code leaves those variables unchanged"""
        P, ga = self.P, self.ga
        self.M = []
        work = [k for k in self.K if self.obs[k]]
        done = set()
        while work:
            k = work.pop(0)
            if k in done:
                continue
            done.add(k)
            outs = [(ci, ce) for ci, ce in enumerate(P.edges) if ce[0] == self.L[k]]
            gout = [e for e in ga.edges if e["src"] == k]
            seen = {}
            for ci, ce in outs:
                gs = self.pairs.get((k, ci), set())
                if len(gs) > 1:
                    raise NotProved(f"T{k}: C edge {ci} pairs with several graph edges {sorted(gs)}")
                if gs:
                    seen[ci] = next(iter(gs))
            for ci, ce in outs:
                if ci not in seen:
                    other = [c for c in seen if c != ci]
                    if other:
                        go = ga.edges[seen[other[0]]]
                        cand = [e for e in gout if e["br"] != go["br"]]
                    else:
                        same = self.polarity(k)
                        cand = [e for e in gout if e["br"] == (ce[1] if same else not ce[1])]
                    seen[ci] = cand[0]["i"]
                g = ga.edges[seen[ci]]
                if ce[3] is None and g["dst"] != ga.fin:
                    raise NotProved(f"T{k}: C edge {ci} returns but graph edge {g['i']} goes to T{g['dst']}")
                if ce[3] is not None and g["dst"] == ga.fin:
                    raise NotProved(f"T{k}: C edge {ci} goes to test point {ce[3]}, graph edge {g['i']} returns")
                if ce[3] is not None and self.L[g["dst"]] is None:
                    k2 = g["dst"]
                    keep = {i for i, x in enumerate(ce[2]) if x == ("var", i)}
                    r2 = [subst(self.rho[k], x) for x in g["sig"]]
                    if any(v[1] not in keep for x in r2 for v in vars_of(x)):
                        raise NotProved(f"T{k2}: never reached in the co-simulation, and not derivable from T{k} "
                                        f"(C edge {ci} changes a variable it depends on)")
                    self.L[k2] = ce[3]
                    self.Is[k2] = [(a_, b_) for a_, b_ in self.Is[k]
                                   if all(v[1] in keep for v in vars_of(a_) + vars_of(b_))]
                    self.derived.append((k2, k, g["i"], ci))
                    self.set_rho()
                    work.append(k2)
                if ce[3] is not None and self.L[g["dst"]] != ce[3]:
                    raise NotProved(f"T{k}: C edge {ci} goes to test point {ce[3]}, graph edge {g['i']} to T{g['dst']}")
                self.M.append((k, ci, g["i"]))
        missing = [k for k in self.K if k not in done]
        if missing:
            raise NotProved(f"templates {missing} are neither reached by the co-simulation nor derivable")

    # ---- obligations in substituted form, and their numerical check ----
    def obligation(self, m):
        k, ci, gi = m
        P, g = self.P, self.ga.edges[gi]
        ce = P.edges[ci]
        rk = self.rho[k]
        t = P.tests[ce[0]]
        ia = [a for a, _ in self.Is[k]]
        ib = [b for _, b in self.Is[k]]
        gf = subst(rk, g["fact"])
        l1 = [subst(rk, s) for s in g["sig"]]
        tgt = [ce[4]] if ce[3] is None else self.rho[g["dst"]]
        l2 = [subst(ce[2], x) for x in tgt]
        tin = [] if ce[3] is None else self.Is[g["dst"]]
        ja = [subst(ce[2], a) for a, _ in tin]
        jb = [subst(ce[2], b) for _, b in tin]
        return dict(t=t, br=ce[1], gb=g["br"], ia=ia, ib=ib, gf=gf, l1=l1, l2=l2, ja=ja, jb=jb)

    def samples(self, m, ob, n=48, seed=11):
        """random C states satisfying the obligation's hypotheses (invariant and C outcome)"""
        rnd = random.Random(seed)
        nv = len(self.P.vars)
        special = [0, 1, 2, 3, 2 ** 31 - 1, 2 ** 31, 2 ** 32 - 1, 2 ** 31 + 1]
        fixed = {a[1]: b[1] for a, b in self.Is[m[0]] if b[0] == "lit"}
        eqs = [(a[1], b[1]) for a, b in self.Is[m[0]] if b[0] == "var"]
        out = []
        for _ in range(n * 200):
            st = [fixed.get(i, rnd.choice([rnd.randrange(M32), rnd.randrange(40), rnd.choice(special)]))
                  for i in range(nv)]
            for i, j in eqs:
                st[i] = st[j]
            if (ev(ob["t"], st) % 2 == 1) == ob["br"]:
                out.append(st)
                if len(out) >= n:
                    break
        return out

    def check(self, seed=7, n=3000):
        rnd = random.Random(seed)
        nv = len(self.P.vars)
        special = [0, 1, 2, 3, 2 ** 31 - 1, 2 ** 31, 2 ** 32 - 1, 2 ** 31 + 1]
        bad = []
        for m in self.M:
            ob = self.obligation(m)
            k = m[0]
            fixed = {a[1]: b[1] for a, b in self.Is[k]}
            for _ in range(n):
                st = [fixed.get(i, rnd.choice([rnd.randrange(M32), rnd.randrange(40), rnd.choice(special)]))
                      for i in range(nv)]
                if (ev(ob["t"], st) % 2 == 1) != ob["br"]:
                    continue
                if any(ev(a, st) != ev(b, st) for a, b in zip(ob["ia"], ob["ib"])):
                    continue
                why, blame = None, []
                g = self.ga.edges[m[2]]
                if (ev(ob["gf"], st) % 2 == 1) != ob["gb"]:
                    why = "branch fact"
                    blame = [(k, j) for j in range(self.ga.nvars(k)) if ("var", j) in vars_of(g["fact"])]
                else:
                    for i, (a, b) in enumerate(zip(ob["l1"], ob["l2"])):
                        if ev(a, st) != ev(b, st):
                            why = f"new environment, component {i}"
                            dst = g["dst"]
                            blame = ([(dst, i)] if dst != self.ga.fin else []) + \
                                [(k, j) for j in range(self.ga.nvars(k)) if ("var", j) in vars_of(g["sig"][i])]
                            break
                if why is None and any(ev(a, st) != ev(b, st) for a, b in zip(ob["ja"], ob["jb"])):
                    why = "invariant"
                if why:
                    bad.append((m, why, st, blame))
                    break
        return bad


# ---------------------------------------------------------------------------
# proof scripts: component lemmas, with abstraction of common subterms

def children(e):
    return [x for x in e[1:] if isinstance(x, tuple) and x and x[0] in ("var", "lit", "un", "bin", "sel")]


def repl(e, m):
    """replace subterms by the map m (outermost first)"""
    if e in m:
        return m[e]
    t = e[0]
    if t in ("var", "lit"):
        return e
    if t == "un":
        return ("un", e[1], e[2], repl(e[3], m))
    if t == "bin":
        return ("bin", e[1], e[2], repl(e[3], m), repl(e[4], m))
    return ("sel", repl(e[1], m), repl(e[2], m), repl(e[3], m))


def contains(e, x):
    return e == x or any(contains(c, x) for c in children(e))


def bound_w(e):
    """width w with eval < 2^w provable by `abs_lt` (a `bin` node), else None"""
    return e[2] if e[0] == "bin" and e[2] > 0 else None


class Prover:
    def __init__(self, pfx, ob, nC, envs):
        self.pfx, self.ob, self.decls, self.cnt = pfx, ob, [], 0
        self.nC, self.envs0 = nC, envs

    def sig(self, ranges):
        ob = self.ob
        r = "".join(f" (r{j} : E.eval σ (.var {j}) < 2 ^ {w})" for j, w in ranges)
        return (f"(σ : List Nat) (hI : List.map (E.eval σ) {lst(ob['ia'])} = List.map (E.eval σ) {lst(ob['ib'])})\n"
                f"    (h : isT (E.eval σ {e_lean(ob['t'])}) = {'true' if ob['br'] else 'false'}){r}")

    def args(self, ranges):
        return "σ hI h" + "".join(f" r{j}" for j, _ in ranges)

    def leaf(self, ranges):
        rs = " ".join(f"r{j}" for j, _ in ranges)
        L = []
        if self.ob["ia"]:
            L.append("  simp only [List.map, List.cons.injEq, and_true, E.eval] at hI")
            L.append(f"  simp only [E.eval] at h {rs} ⊢")
            L.append(f"  try simp only [hI] at h {rs} ⊢")
        else:
            L.append(f"  simp only [E.eval] at h {rs} ⊢")
        for j, w in ranges:
            if w == 1:
                L.append(f"  try rw [lt2_ite _ r{j}] at h")
                L.append(f"  try rw [lt2_ite _ r{j}]")
        L.append("  auto_ops")
        return "\n".join(L)

    def name(self):
        self.cnt += 1
        return f"{self.pfx}_{self.cnt}"

    def guard(self, gf, gb):
        nm = self.name()
        self.decls.append(f"theorem {nm} {self.sig([])} :\n    isT (E.eval σ {e_lean(gf)}) = {'true' if gb else 'false'} := by\n"
                          + self.leaf([]))
        return nm

    def eq(self, X, Y, n=None, ranges=(), envs=None, depth=0):
        """emit a lemma `E.eval σ X = E.eval σ Y` under the obligation's hypotheses; return its name"""
        n = self.nC if n is None else n
        envs = self.envs0 if envs is None else envs
        ranges = list(ranges)
        nm = self.name()
        head = f"theorem {nm} {self.sig(ranges)} :\n    E.eval σ {e_lean(X)} = E.eval σ {e_lean(Y)} :="
        if X == Y:
            self.decls.append(head + " rfl")
            return nm
        pairs = self.pairs(X, Y, envs) if depth < 6 else []
        while pairs:
            res = self.residual(X, Y, pairs, n, envs)
            if res:
                break
            pairs = pairs[:-1]
        if not pairs:
            self.decls.append(head + " by\n" + self.leaf(ranges))
            return nm
        X2, Y2, thx, thy, newr, envs2 = res
        qs = []
        for i, (a, b) in enumerate(pairs):
            qs.append("rfl" if a == b else f"({self.eq(a, b, n, ranges, envs, depth + 1)} {self.args(ranges)})")
        ranges2 = ranges + newr
        rn = self.eq(X2, Y2, n + len(pairs), ranges2, envs2, depth + 1)
        chain = "rfl"
        for q in reversed(["rfl"] * n + qs):
            chain = f"map_cons_eq {q} ({chain})" if q != "rfl" or chain != "rfl" else "rfl"
        rargs = ["(tr_hyp (by decide +kernel) (by decide +kernel) hI)", "(tr_isT (by decide +kernel) h)"]
        rargs += [f"(tr_lt (by decide +kernel) r{j})" for j, _ in ranges]
        for j, _ in newr:
            a = thx[j]
            o = f"(.cmpi .{a[1][1]})" if isinstance(a[1], tuple) else f".{a[1]}"
            rargs.append(f"(abs_lt (j := {j}) (o := {o}) (w := {a[2]}) (a := {e_lean(a[3])}) (b := {e_lean(a[4])}) "
                         f"(by decide +kernel) (by decide))")
        self.decls.append(
            head + "\n" +
            f"  abs_eq (θx := {lst(thx)})\n    (θy := {lst(thy)})\n"
            f"    (X' := {e_lean(X2)}) (Y' := {e_lean(Y2)})\n"
            f"    (by decide +kernel) (by decide +kernel) ({chain})\n"
            f"    ({rn} (List.map (E.eval σ) {lst(thx)})\n      " + " ".join(rargs) + ")")
        return nm

    def pairs(self, X, Y, envs):
        fp = lambda e: tuple(ev(e, s) for s in envs)  # noqa: E731
        fX = {}
        for a in self.subs(X):
            fX.setdefault(fp(a), []).append(a)
        out = []

        def walk(b):
            if b[0] in ("var", "lit"):
                return
            f = fp(b)
            if len(set(f)) > 1 and f in fX:
                cs = fX[f]
                a = b if b in cs else max(cs, key=size)
                out.append((a, b))
                return
            for c in children(b):
                walk(c)
        for c in children(Y):
            walk(c)
        # no nesting among the a's (keep the larger), no duplicates
        out.sort(key=lambda p: -size(p[0]))
        keep = []
        for a, b in out:
            if any(contains(a2, a) or contains(a, a2) for a2, _ in keep) or any(b == b2 for _, b2 in keep):
                continue
            keep.append((a, b))
        return keep

    def subs(self, X):
        acc = []
        for c in children(X):
            subexprs(c, acc)
        return acc

    def residual(self, X, Y, pairs, n, envs):
        mx = {a: ("var", n + i) for i, (a, _) in enumerate(pairs)}
        my = {b: ("var", n + i) for i, (_, b) in enumerate(pairs)}
        X2, Y2 = repl(X, mx), repl(Y, my)
        ident = [("var", i) for i in range(n)]
        thx, thy = ident + [a for a, _ in pairs], ident + [b for _, b in pairs]
        if subst(thx, X2) != X or subst(thy, Y2) != Y:
            return None
        newr = [(n + i, bound_w(a)) for i, (a, _) in enumerate(pairs) if bound_w(a)]
        rnd = random.Random(n)
        envs2 = []
        for s in envs:
            z = [ev(a, s) for a, _ in pairs]
            envs2.append(list(s[:n]) + z)
            # and arbitrary values in range, to check the residual does not rely on more than the bound
            zr = [rnd.randrange(1 << bound_w(a)) if bound_w(a) else rnd.randrange(1 << 34) for a, _ in pairs]
            envs2.append(list(s[:n]) + zr)
        hyp = lambda e: (ev(self.ob["t"], e) % 2 == 1) == self.ob["br"] and all(  # noqa: E731
            ev(a, e) == ev(b, e) for a, b in zip(self.ob["ia"], self.ob["ib"]))
        if not all(ev(X2, e) == ev(Y2, e) for e in envs2 if hyp(e)):
            return None
        return X2, Y2, thx, thy, newr, envs2


# ---------------------------------------------------------------------------
# Lean emission

def cedge_lean(ce):
    src, br, upd, dst, ret = ce
    return (f"{{ src := {src}, br := {'true' if br else 'false'}, upd := {lst(upd)}, "
            f"dst := {'none' if dst is None else f'some {dst}'}, ret := {e_lean(ret)} }}")


def gedge_lean(g):
    return (f"{{ src := {g['src']}, fact := {e_lean(g['fact'])}, br := {'true' if g['br'] else 'false'}, "
            f"sig := sig{g['i']}, dst := {g['dst']} }}")


def emit(C, opt, P, cpath):
    ga = C.ga
    out = []
    w = out.append
    pv = P.params
    pn = [x + "₀" for x in pv]          # Lean binder names (never clash with n m t u)
    args = " ".join(pn)
    argl = "[" + ", ".join(pn) + "]"
    rel = os.path.relpath(os.path.abspath(cpath), ROOT)
    csrc = open(cpath).read().split("\n")
    w(f"/-!\n# GENERATED by formal/tools/autoproof/autoproof.py -- DO NOT EDIT\n")
    w(f"All-inputs token-level theorem for `{opt.name}`, no hand proof (probe C-vk2).")
    w(f"Graph: dfimport's export of `{os.path.relpath(os.path.abspath(opt.mlir), ROOT)}` "
      f"(`{opt.graph_ns}`: `rules`, templates `T*`, segments `seg*`).")
    w(f"C: `{rel}`, function `{opt.func}`, transcribed by `formal/tools/autoproof/cfront.py` into the")
    w("test-point automaton `P` below (int = i32 bit pattern, wraparound arithmetic: the circuit's")
    w("`Ops`, not C's undefined signed overflow). Correspondence found by co-simulation and")
    w("checked here by Lean: `L` (C test point of each template), `ρ` (template variables over the")
    w("C state), `Is` (template invariants), `M` (pairing of C and graph edges).\n")
    w("Statement (`auto_computes`): for all naturals on the input channels and any fuel on which")
    w(f"the transcription `kC` returns `r`: a complete run reaching `[r]` on the output exists;")
    w("every complete run, under any schedule and any arbitration, ends in that store; no run is")
    w("longer. NOT covered: termination of the C (fuelled), that the transcription is the C beyond")
    w("cfront's reading (tested against the compiled C), gates, delays, cells.\n")
    w("## The C transcription, test points")
    for p, t in enumerate(P.tests):
        line = csrc[P.lines[p] - 1].strip() if 0 < P.lines[p] <= len(csrc) else ""
        w(f"* test {p} (line {P.lines[p]}: `{line}`): `{show(t, P.vars)}`")
    w(f"* state: `{', '.join(P.vars)}`; entry: `" +
      ", ".join(f"{P.vars[i]} := {show(x, pv)}" for i, x in enumerate(P.entry)) + f"`, then test {P.start}")
    w("-/\n")
    w("set_option linter.unusedVariables false\n")
    w(f"namespace {opt.ns}\n")
    w(f"open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Auto {opt.graph_ns}\n")
    w("/-! ## The C function -/\n")
    for ci, ce in enumerate(P.edges):
        desc = ", ".join(f"{P.vars[i]} := {show(x, P.vars)}" for i, x in enumerate(ce[2]) if x != ("var", i))
        tail = f"return {show(ce[4], P.vars)}" if ce[3] is None else f"to test {ce[3]}"
        w(f"/-- test {ce[0]} {'true' if ce[1] else 'false'}: {desc or '(no assignment)'}; {tail} -/")
        w(f"def ce{ci} : CEdge := {cedge_lean(ce)}")
    w("")
    w("def P : CProg where")
    w(f"  entry := {lst(P.entry)}")
    w(f"  start := {P.start}")
    w(f"  tests := {lst(P.tests)}")
    w(f"  edges := [{', '.join(f'ce{i}' for i in range(len(P.edges)))}]\n")
    w(f"/-- `{opt.func}` as transcribed: `none` = fuel ran out. -/")
    w(f"def kC (fuel {args} : Nat) : Option Nat := P.call fuel {argl}\n")
    w("/-! ## The graph side -/\n")
    w("abbrev G := graph rules")
    w("def St (t : List (List E)) (env : List Nat) : Store Nat Nat := ofL (lmap env t)")
    w("def Reach (s t : Store Nat Nat) : Prop := ∃ n, Run (step G) s n t")
    w("theorem reach_trans {s u t : Store Nat Nat} (h1 : Reach s u) (h2 : Reach u t) : Reach s t :=")
    w("  let ⟨_, a⟩ := h1; let ⟨_, b⟩ := h2; ⟨_, run_trans a b⟩\n")
    w("theorem edge {F : List (E × Bool)} {sched : List Nat} {sig : List E} {Ti Tj : List (List E)}")
    w("    (hl : Ti.length = N) (h : execL (symVI F) rules Ti sched = some (Tj.map (List.map (E.subst sig))))")
    w("    (env : List Nat) (hF : FactsOK env F) : Reach (St Ti env) (St Tj (sig.map (E.eval env))) := by")
    w("  have := sym_run bounded_ok hl sched h env hF")
    w("  rw [lmap_subst] at this")
    w("  exact ⟨_, this⟩\n")
    w("theorem fact1 {env : List Nat} {e : E} {b : Bool} (h : isT (e.eval env) = b) :")
    w("    FactsOK env [(e, b)] := by")
    w("  intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact h\n")
    nT = len(ga.templates)
    srcs = sorted({e["src"] for e in ga.edges})
    for k in srcs:
        w(f"theorem lenT{k} : T{k}.length = N := by decide +kernel")
    w("")
    w(f"def Ts : List (List (List E)) := [{', '.join(f'T{k}' for k in range(nT))}]")
    w("def Tm (k : Nat) (env : List Nat) : Store Nat Nat := St (Ts.getD k []) env\n")
    for g in ga.edges:
        w(f"def g{g['i']} : GEdge := {gedge_lean(g)}")
    gnames = ", ".join("g%d" % g["i"] for g in ga.edges)
    w(f"def GE : List GEdge := [{gnames}]\n")
    w("theorem hG : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →")
    w("    Reach (Tm g.src env) (Tm g.dst (g.sig.map (E.eval env))) := by")
    w("  intro g hg env hf")
    w("  simp only [GE, List.mem_cons, List.not_mem_nil, or_false] at hg")
    w("  rcases hg with " + " | ".join("rfl" for _ in ga.edges))
    for g in ga.edges:
        w(f"  · exact edge (Ti := T{g['src']}) (Tj := T{g['dst']}) lenT{g['src']} seg{g['i']} env (fact1 hf)")
    w("")
    w("/-! ## The correspondence (found by co-simulation, checked below) -/\n")
    w(f"def L : List Nat := {[x if x is not None else 0 for x in C.L]}")
    w(f"def K : List Nat := {C.K}")
    w("def ρ : List (List E) := [" + ", ".join(lst(r) for r in C.rho) + "]")
    w("def Is : List (List (E × E)) := [" + ", ".join(
        "[" + ", ".join(f"({e_lean(a)}, {e_lean(b)})" for a, b in I) + "]" for I in C.Is) + "]")
    w("def M : List Match := [" + ", ".join(f"⟨{k}, ce{ci}, g{gi}⟩" for k, ci, gi in C.M) + "]\n")
    w(f"theorem cover : Cover P L K {ga.fin} GE M = true := by decide +kernel\n")
    for n, m in enumerate(C.M):
        ob = C.obligation(m)
        k, ci, gi = m
        ce = P.edges[ci]
        pr = Prover(f"o{n}", ob, len(P.vars), C.samples(m, ob))
        gname = pr.guard(ob["gf"], ob["gb"])
        cl1 = [pr.eq(x, y) for x, y in zip(ob["l1"], ob["l2"])]
        cl2 = [pr.eq(x, y) for x, y in zip(ob["ja"], ob["jb"])]
        w(f"/-! ### T{k} with C edge {ci} (test {ce[0]} {'true' if ce[1] else 'false'}) and graph segment {gi} -/\n")
        for d in pr.decls:
            w(d + "\n")

        def chain(names):
            c = "rfl"
            for nm in reversed(names):
                c = f"map_cons_eq ({nm} σ hI h) ({c})"
            return c
        w(f"/-- Under T{k}'s invariant and the C outcome, the segment's fact has outcome "
          f"{'true' if ob['gb'] else 'false'}, its new environment is ρ of the C's new state, and the "
          f"target invariant holds. -/")
        w(f"theorem o{n} : ∀ σ : List Nat,")
        w(f"    List.map (E.eval σ) {lst(ob['ia'])} = List.map (E.eval σ) {lst(ob['ib'])} →")
        w(f"    isT (E.eval σ {e_lean(ob['t'])}) = {'true' if ob['br'] else 'false'} →")
        w(f"    isT (E.eval σ {e_lean(ob['gf'])}) = {'true' if ob['gb'] else 'false'} ∧")
        w(f"    List.map (E.eval σ) {lst(ob['l1'])} =")
        w(f"      List.map (E.eval σ) {lst(ob['l2'])} ∧")
        w(f"    List.map (E.eval σ) {lst(ob['ja'])} = List.map (E.eval σ) {lst(ob['jb'])} :=")
        w(f"  fun σ hI h => ⟨{gname} σ hI h, {chain(cl1)}, {chain(cl2)}⟩\n")
        w(f"theorem m{n} : MatchSem P ρ Is ⟨{k}, ce{ci}, g{gi}⟩ :=")
        w("  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)")
        w(f"    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o{n}\n")
    w("theorem hM : ∀ m ∈ M, MatchSem P ρ Is m := by")
    w("  intro m hm")
    w("  simp only [M, List.mem_cons, List.not_mem_nil, or_false] at hm")
    w("  rcases hm with " + " | ".join("rfl" for _ in C.M))
    for n in range(len(C.M)):
        w(f"  · exact m{n}")
    w("")
    w(f"theorem hin ({args} : Nat) : (ρ.getD 0 []).map (E.eval (P.entry.map (E.eval {argl}))) = {argl} := by")
    w("  first | rfl | (simp only [ρ, P, List.getD, List.map, List.cons.injEq, and_true]; auto_ops)\n")
    w(f"theorem hI0 ({args} : Nat) : InvH (Is.getD 0 []) (P.entry.map (E.eval {argl})) := by")
    w("  first | rfl | (simp only [InvH, Is, P, List.getD, List.map, List.cons.injEq, and_true]; auto_ops)\n")
    w("/-! ## The whole function, on every schedule -/\n")
    w(f"theorem reach_kC {{fuel {args} r : Nat}} (h : kC fuel {args} = some r) :")
    w(f"    Reach (St T0 {argl}) (St T{ga.fin} [r]) :=")
    w(f"  sim_call Tm Reach reach_trans P L K ρ Is {ga.fin} GE M hG cover hM (by decide) rfl")
    w(f"    (hin {args}) (hI0 {args}) h\n")
    w("theorem cnt_lmap (Q : List Nat) (env : List Nat) (l : List (List E)) :")
    w("    cnt Q (ofL (lmap env l)) = (Q.map fun c => (ofL l c).length).sum := by")
    w("  unfold cnt; congr 1; apply List.map_congr_left; intro c _; simp [ofL_lmap]\n")
    w(f"theorem init_inv ({args} : Nat) : Formal.Net.GcdHw.Inv spine (St T0 {argl}) := by")
    w("  unfold Formal.Net.GcdHw.Inv St; rw [cnt_lmap]; decide +kernel\n")
    w(f"theorem final_terminal (r : Nat) : Terminal (step G) (St T{ga.fin} [r]) := by")
    w("  apply terminal_of_dead")
    w("  rw [List.all_eq_true]; intro x hx")
    w("  rw [St, dead_lmap]")
    w(f"  exact List.all_eq_true.mp (by decide +kernel : rules.all (Rule.dead (ofL T{ga.fin})) = true) x hx\n")
    if opt.witness:
        wv, wr = opt.witness
        w(f"/-- Non-vacuity of the hypothesis of `auto_computes`: the transcription returns on "
          f"{wv} (value from autoproof's Python run of this automaton; re-checked here by the kernel). -/")
        w(f"theorem witness : kC 10000 {' '.join(str(x % M32) for x in wv)} = some {wr} := by decide +kernel\n")
    w(f"/-- **The imported graph computes the C function `{opt.func}`** (generated proof). -/")
    w(f"theorem auto_computes {{fuel {args} r : Nat}} (h : kC fuel {args} = some r) :")
    w(f"    (∃ n, Run (step G) (St T0 {argl}) n (St T{ga.fin} [r])) ∧")
    w(f"    (∀ m t, Run (step G) (St T0 {argl}) m t → Terminal (step G) t → t = St T{ga.fin} [r]) ∧")
    w(f"    (∃ n, ∀ m u, Run (step G) (St T0 {argl}) m u → m ≤ n) := by")
    w("  obtain ⟨n, hn⟩ := reach_kC h")
    w("  refine ⟨⟨n, hn⟩, fun m t ht hT => ?_, ⟨n, fun m u hu => ?_⟩⟩")
    w(f"  · exact (determinate spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv {args})")
    w("      hn (final_terminal r) ht hT).1")
    w(f"  · exact no_longer spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv {args})")
    w("      hn (final_terminal r) hu\n")
    w(f"end {opt.ns}")
    return "\n".join(out) + "\n"


def nocomment(text):
    """a `/-` inside a line (e.g. in a path) would open a nested Lean comment"""
    return "\n".join(l[:1] + l[1:].replace("/-", "/ -") for l in text.split("\n"))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("mlir")
    ap.add_argument("cfile")
    ap.add_argument("func")
    ap.add_argument("--name", required=True, help="Lean base name, e.g. Ipow -> Formal.Net.AutoIpow")
    ap.add_argument("--graph-ns", required=True, help="namespace of the dfimport graph/segments")
    ap.add_argument("--seg-module", help="import this module for the graph and segments")
    ap.add_argument("--dfargs", default="", help="dfimport naming options (for --combined)")
    ap.add_argument("--out", help="write the proof file (imports --seg-module)")
    ap.add_argument("--combined", help="write graph + segments + proof in ONE file")
    ap.add_argument("--vecs", default="")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--corr-from", help="negative controls: guess the correspondence on THIS (reference) MLIR, "
                    "then emit the proof for the MLIR given as first argument (implies --force)")
    ap.add_argument("--force", action="store_true",
                    help="negative controls: write the Lean file even if the numerical check fails")
    a = ap.parse_args()
    a.ns = f"Formal.Net.Auto{a.name}"
    vecs = [tuple(int(x) for x in v.split(",")) for v in a.vecs.split()] if a.vecs else []
    try:
        P = cfront.front(a.cfile, a.func)
        ga = GA(a.mlir)
        if ga.nargs != len(P.params):
            raise NotProved(f"the graph has {ga.nargs} data inputs, the C function {len(P.params)}")
        if a.corr_from:
            a.force = True
            C = Corr(GA(a.corr_from), P, vecs, a.seed)
            C.infer()
            if len(ga.edges) != len(C.ga.edges) or any(
                    (x["src"], x["br"], x["dst"]) != (y["src"], y["br"], y["dst"]) for x, y in zip(ga.edges, C.ga.edges)):
                raise NotProved("--corr-from: the two graphs' template automata differ")
            C.ga = ga
            C.cex = None
        else:
            C = Corr(ga, P, vecs, a.seed)
    except (NotProved, SyntaxError) as e:
        print(f"AUTOPROOF NOT PROVED: {e}")
        return 2
    if C.cex and not a.force:
        ins, gr, cr, ng, nc = C.cex
        sins = ",".join(str(x - M32 if x >= 2 ** 31 else x) for x in ins)
        print(f"AUTOPROOF COUNTEREXAMPLE (Python semantics): input ({sins}): graph template run "
              f"returns {gr} after {ng} segments, C returns {cr} after {nc} tests")
        return 1
    try:
        if not a.corr_from:
            C.infer()
        else:
            C.bad = C.check()
    except NotProved as e:
        print(f"AUTOPROOF NOT PROVED: {e}")
        return 2
    bad = C.bad
    print(f"autoproof: {len(ga.templates)} templates, {len(ga.edges)} segments, {len(P.tests)} C test points, "
          f"{len(C.M)} matches; L = {C.L}")
    for k in C.K:
        print(f"  T{k} ~ test {C.L[k]}: [" + ", ".join(show(x, P.vars) for x in C.rho[k]) + "]" +
              (("  inv " + ", ".join(f"{show(x, P.vars)}={show(y, P.vars)}" for x, y in C.Is[k])) if C.Is[k] else ""))
    if bad:
        for m, why, st, _ in bad:
            print(f"  numerical check FAILS for T{m[0]}/C edge {m[1]}/segment {m[2]} ({why}) at C state "
                  + ", ".join(f"{P.vars[i]}={v}" for i, v in enumerate(st)))
        if not a.force:
            print("AUTOPROOF NOT PROVED: a guessed correspondence fails on some C state (see above)")
            return 2
        print("autoproof: --force: writing the Lean file anyway (negative control: Lean must reject it)")
    a.witness = None
    for v in (vecs or [tuple(range(1, len(P.params) + 1))]):
        r, _ = cfront.run(P, [x % M32 for x in v], 5000)
        if r is not None:
            a.witness = (v, r)
            break
    body = emit(C, a, P, a.cfile)
    if a.combined:
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            g, s = os.path.join(td, "G.lean"), os.path.join(td, "S.lean")
            env = {x: y for x, y in os.environ.items() if not x.startswith("BDC_")}
            subprocess.run([sys.executable, os.path.join(ROOT, "formal/tools/dfimport/mlir2lean.py"), a.mlir,
                            "-o", g, "--segments", s] + a.dfargs.split(), check=True, env=env)
            gt, st = open(g).read(), open(s).read()
        strip = lambda t: "\n".join(l for l in t.split("\n") if not l.startswith("import "))  # noqa: E731
        text = ("import Formal.Net.GcdHwLib\nimport Formal.Net.AutoLib\n\n" + strip(gt) + "\n" + strip(st) +
                "\n" + body)
        open(a.combined, "w").write(nocomment(text))
        print(f"autoproof: wrote {a.combined}")
    if a.out:
        text = f"import {a.seg_module}\nimport Formal.Net.AutoLib\n\n" + body
        open(a.out, "w").write(nocomment(text))
        print(f"autoproof: wrote {a.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
