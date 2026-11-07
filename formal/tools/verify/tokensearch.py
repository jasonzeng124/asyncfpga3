#!/usr/bin/env python3
"""Bounded explicit-state counterexample search on the token-level graph (probe C-vk).

    python3 tokensearch.py MLIR --c C_FILE --func F [--vec a,b ...] [--max-states N]
                           [--no-por] [--trace-max N] [--domain-note TEXT]

The graph is exactly the one formal/tools/dfimport/mlir2lean.py exports to Lean (its
`Graph` class, imported read-only: bdc's parser + fusion plan + lowering choices). The
firing semantics below mirror `Formal.Net.GcdHw.Rule.fire` with `natVI` and Kahn's
`applyF` (GcdHwLib.lean / Kahn.lean) line by line: strict rules pop one token from each
listed input and push their outputs; `mux` pops the select and the selected input only;
each `control_merge` input is its own rule (so every arbiter outcome is a schedule); a
condition token is true iff bit 0 is set.

For each input vector, the C reference value comes from compiling the C file (cref.py).
The search explores EVERY interleaving of rule firings from the initial store (one token
per function argument), breadth first, so the first bad terminal store found has a
shortest schedule. A terminal store (no rule enabled) is CORRECT iff it is exactly
`[C result]` on the data output, `[0]` on the end token, and nothing anywhere else -- the
final store of the Lean theorems. Anything else (wrong value, deadlock, leftover tokens)
is printed as a COUNTEREXAMPLE with its full schedule.

Reduction (default; --no-por turns it off): a rule that shares no input channel and no
output channel with any other rule commutes with every other firing and can neither
disable nor be disabled by one, so when it is enabled it alone is a persistent set
(Godefroid 1996): exploring only it preserves every reachable terminal store. Rules that
share channels (the inputs of a control_merge share `res`/`index`) are always branched on.
selftest.sh checks the reduced and full searches give the same terminal stores.

Exit: 0 = every vector: all terminal stores correct, search complete, no cycle found;
      1 = a counterexample was printed; 2 = inconclusive (state bound hit).
What a 0 does NOT prove: anything about inputs not in the vector list, or about runs
longer than the bound (there are none when the search completes), or about the circuit.
"""
import argparse
import os
import sys
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "dfimport"))
sys.path.insert(0, HERE)
for k in ["BDC_OP_FUSION", "BDC_CONST_FOLD", "BDC_FORK_FUSION", "BDC_MAX_FUSE_NODES", "BDC_PROBE"]:
    os.environ.pop(k, None)
import mlir2lean  # noqa: E402  (read-only import of C-8i's exporter)
from cref import c_reference  # noqa: E402


# ---------------------------------------------------------------------------
# Ops: Formal.Net.GcdHw.Ops, on Python ints (= Lean Nat)

def P(w):
    return 1 << w


def wm1(w):
    return w - 1 if w >= 1 else 0     # Lean Nat subtraction


def flip(w, a):
    return (a % P(w) + P(wm1(w))) % P(w)


def bop(op, w, a, b):
    if isinstance(op, tuple):          # ("cmpi", pred)
        p = op[1]
        x, y = a % P(w), b % P(w)
        sx, sy = flip(w, a), flip(w, b)
        r = {"eq": x == y, "ne": x != y, "ult": x < y, "ule": x <= y, "ugt": y < x,
             "uge": y <= x, "slt": sx < sy, "sle": sx <= sy, "sgt": sy < sx, "sge": sy <= sx}[p]
        return 1 if r else 0
    if op == "addi":
        return (a + b) % P(w)
    if op == "subi":
        return (a % P(w) + P(w) - b % P(w)) % P(w)
    if op == "muli":
        return (a * b) % P(w)
    if op == "andi":
        return (a & b) % P(w)
    if op == "ori":
        return (a | b) % P(w)
    if op == "xori":
        return (a ^ b) % P(w)
    if op == "shli":                    # (a <<< b) % 2^w, without building a huge int
        return 0 if b >= w else ((a % P(w)) << b) % P(w)
    if op == "shrui":
        return (a % P(w)) >> b
    if op == "shrsi":
        x = a % P(w)
        if x < P(wm1(w)):
            return x >> b
        return (P(w) - 1) - ((P(w) - 1 - x) >> b)
    raise ValueError(op)


def uop(op, w, a):
    if op in ("trunci", "extui"):
        return a % P(w)
    if isinstance(op, tuple) and op[0] == "extsi":
        dw = op[1]
        x = a % P(w)
        return x if x < P(wm1(w)) else x + P(dw) - P(w)
    raise ValueError(op)


def ev(e, env):
    t = e[0]
    if t == "var":
        return env[e[1]] if e[1] < len(env) else 0
    if t == "lit":
        return e[1]
    if t == "un":
        return uop(e[1], e[2], ev(e[3], env))
    if t == "bin":
        return bop(e[1], e[2], ev(e[3], env), ev(e[4], env))
    if t == "sel":
        return ev(e[2], env) if ev(e[1], env) % 2 == 1 else ev(e[3], env)
    raise ValueError(e)


# ---------------------------------------------------------------------------
# Rule.fire (natVI) + applyF

def fire(r, st):
    """-> (pops: dict chan->n, pushes: list of (chan, value)) or None."""
    k = r[0]
    if k == "mux":
        _, s, ds, o, iw = r[:5]
        if not st[s]:
            return None
        j = st[s][0]
        idx = j % P(iw)
        if idx >= len(ds):
            return None
        d = ds[idx]
        if d == s or not st[d]:
            return None
        return {s: 1, d: 1}, [(o, st[d][0])]
    ins = mlir2lean.Graph.rule_ins(r)
    if any(not st[c] for c in ins):
        return None
    vs = [st[c][0] for c in ins]
    pops = {c: 1 for c in ins}
    if k == "comp":
        return pops, [(r[2], ev(r[3], vs))]
    if k == "fork":
        return pops, [(c, vs[0]) for c in r[2]]
    if k == "branch":
        return pops, [(r[3] if vs[0] % 2 == 1 else r[4], vs[1])]
    if k == "cm":
        return pops, [(r[2], vs[0]), (r[3], r[4])]
    if k == "sink":
        return pops, []
    raise ValueError(r)


def apply(st, res):
    pops, pushes = res
    st = list(st)
    touched = set(pops) | {c for c, _ in pushes}
    for c in touched:
        q = list(st[c][pops.get(c, 0):])
        q += [v for cc, v in pushes if cc == c]
        st[c] = tuple(q)
    return tuple(st)


def rule_outs(r):
    k = r[0]
    if k == "comp":
        return [r[2]]
    if k == "fork":
        return list(r[2])
    if k == "branch":
        return [r[3], r[4]]
    if k == "mux":
        return [r[3]]
    if k == "cm":
        return [r[2], r[3]]
    return []


def independent_rules(rules):
    """Rules sharing no input and no output channel with any other rule."""
    ins = [set(mlir2lean.Graph.rule_ins(r)) for r in rules]
    outs = [set(rule_outs(r)) for r in rules]
    ind = []
    for i in range(len(rules)):
        ok = True
        for j in range(len(rules)):
            if i != j and (ins[i] & ins[j] or outs[i] & outs[j]):
                ok = False
                break
        ind.append(ok)
    return ind


# ---------------------------------------------------------------------------

class Search:
    def __init__(self, g, por=True, max_states=300000):
        self.g = g
        self.rules = g.rules
        self.por = por
        self.ind = independent_rules(self.rules) if por else [False] * len(self.rules)
        self.max_states = max_states
        ins, outs = mlir2lean.port_names(g)
        self.ins = ins
        self.outs = dict(outs)
        self.width = [g.em.width(v) for v in g.chname]

    def initial(self, vec):
        st = [()] * self.g.N
        k = 0
        for a in self.g.func.args:
            c = self.g.chan[self.g.A(a.ssa_name)]
            if a.is_control:
                st[c] = (0,)
            else:
                st[c] = (vec[k] % P(self.width[c]),)
                k += 1
        if k != len(vec):
            raise SystemExit(f"vector {vec} has {len(vec)} values, the function has {k} data inputs")
        return tuple(st)

    def expected(self, cres):
        st = [()] * self.g.N
        if "chOut" in self.outs:
            c = self.outs["chOut"]
            st[c] = (cres % P(self.width[c]),)
        st[self.outs["chEnd"]] = (0,)
        return tuple(st)

    def successors(self, st):
        en = []
        for i, r in enumerate(self.rules):
            res = fire(r, st)
            if res is not None:
                if self.ind[i]:
                    return [(i, res)]
                en.append((i, res))
        return en

    def run(self, vec, cres):
        """BFS. -> dict(status, states, terminals, bad=(store, path) or None, cycle)."""
        s0 = self.initial(vec)
        want = self.expected(cres)
        parent = {s0: None}
        q = deque([s0])
        terminals = {}
        bad = None
        edges = 0
        succ_count = {}
        while q:
            st = q.popleft()
            nx = self.successors(st)
            if not nx:
                terminals[st] = terminals.get(st, 0) + 1
                if st != want and bad is None:
                    bad = st
                    break
                continue
            succ_count[st] = []
            for i, res in nx:
                t = apply(st, res)
                edges += 1
                succ_count[st].append(t)
                if t not in parent:
                    parent[t] = (st, i, res)
                    if len(parent) > self.max_states:
                        return dict(status="bound", states=len(parent), terminals=terminals,
                                    bad=None, want=want, parent=parent)
                    q.append(t)
        cycle = None if bad is not None else self.find_cycle(succ_count)
        return dict(status="bad" if bad is not None else ("cycle" if cycle else "ok"),
                    states=len(parent), terminals=terminals, bad=bad, want=want,
                    parent=parent, cycle=cycle, edges=edges)

    @staticmethod
    def find_cycle(succ):
        """A list of states forming a cycle of the explored graph (an infinite run), or None.
        Kahn's algorithm removes every state not reachable from a cycle; in what is left
        every state has a predecessor that is left, so walking predecessors must repeat."""
        indeg, pred = {}, {}
        for s, ts in succ.items():
            indeg.setdefault(s, 0)
            for t in ts:
                indeg[t] = indeg.get(t, 0) + 1
                pred.setdefault(t, []).append(s)
        ready = [s for s, d in indeg.items() if d == 0]
        while ready:
            s = ready.pop()
            for t in succ.get(s, ()):
                indeg[t] -= 1
                if indeg[t] == 0:
                    ready.append(t)
        left = {s for s, d in indeg.items() if d > 0}
        if not left:
            return None
        s, seen, walk = next(iter(left)), {}, []
        while s not in seen:
            seen[s] = len(walk)
            walk.append(s)
            s = next(p for p in pred[s] if p in left)
        cyc = walk[seen[s]:]
        cyc.reverse()                    # forward order: cyc[i] -> cyc[i+1] -> ... -> cyc[0]
        return cyc

    def path(self, parent, st):
        out = []
        while parent[st] is not None:
            p, i, res = parent[st]
            out.append((p, i, res, st))
            st = p
        out.reverse()
        return out

    # -- printing ------------------------------------------------------------
    def cn(self, c):
        return f"{c}:{self.g.chname[c]}"

    def fmt_store(self, st, w=None):
        parts = []
        for c, toks in enumerate(st):
            if toks:
                parts.append(f"{self.cn(c)}={list(toks)}")
        return ", ".join(parts) if parts else "(empty)"

    def fmt_step(self, n, p, i, res):
        r = self.rules[i]
        pops, pushes = res
        takes = ", ".join(f"{self.cn(c)}={p[c][0]}" for c in pops)
        gives = ", ".join(f"{self.cn(c)}={v}" for c, v in pushes) or "-"
        return f"  {n:4d}. rule {i:3d} {r[0]:6s} [{r[-1]}]  takes {takes}  gives {gives}"


def signed(v, w):
    v %= P(w)
    return v - P(w) if w and v >= P(wm1(w)) else v


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("mlir")
    ap.add_argument("--c", required=True)
    ap.add_argument("--func", required=True)
    ap.add_argument("--vecs", required=True,
                    help="input vectors, space separated, each a,b (signed C ints): \"3,7 -3,5\"")
    ap.add_argument("--max-states", type=int, default=300000)
    ap.add_argument("--no-por", action="store_true")
    ap.add_argument("--trace-max", type=int, default=400,
                    help="print at most this many firings of a counterexample (head+tail)")
    ap.add_argument("--terminals", action="store_true", help="print every terminal store (selftest)")
    a = ap.parse_args()

    g = mlir2lean.Graph(a.mlir)
    S = Search(g, por=not a.no_por, max_states=a.max_states)
    vecs = [tuple(int(x) for x in v.split(",")) for v in a.vecs.split()]
    crefs = c_reference(a.c, a.func, vecs)
    nind = sum(S.ind)
    print(f"graph: {len(g.rules)} rules, {g.N} channels (dfimport's export of {os.path.relpath(a.mlir, ROOT)});"
          f" reduction: {'off' if a.no_por else f'{nind} independent rules'}; C reference: {a.c} ({a.func}, gcc -fwrapv)")
    worst = 0
    for vec, cres in zip(vecs, crefs):
        R = S.run(vec, cres)
        tag = ",".join(map(str, vec))
        if a.terminals:
            for t in sorted(R["terminals"]):
                print(f"  terminal {tag}: {S.fmt_store(t)}")
        if R["status"] == "ok":
            print(f"  vector ({tag}): C = {cres}; all {len(R['terminals'])} terminal store(s) correct; "
                  f"{R['states']} states, {R['edges']} edges, no cycle (search complete)")
            continue
        if R["status"] == "bound":
            print(f"  vector ({tag}): C = {cres}; INCONCLUSIVE: state bound {a.max_states} hit, "
                  f"no counterexample among {R['states']} states")
            worst = max(worst, 2)
            continue
        if R["status"] == "cycle":
            cyc = R["cycle"]
            head = S.path(R["parent"], cyc[0])
            oc = S.outs.get("chOut")
            print(f"\nCOUNTEREXAMPLE  input ({tag})  (infinite run)")
            print(f"  C reference ({os.path.basename(a.c)}:{a.func}) returns {cres}")
            print(f"  this schedule reaches a store and then returns to it after {len(cyc)} firings, "
                  "forever: the graph never delivers a result")
            print(f"  schedule to the repeating store ({len(head)} firings):")
            for n, (p, i, res, t) in enumerate(head[-a.trace_max:], max(1, len(head) - a.trace_max + 1)):
                print(S.fmt_step(n, p, i, res))
            print(f"  repeating store: {S.fmt_store(cyc[0])}")
            print(f"  the loop ({len(cyc)} firings, back to the same store):")
            loop = cyc + [cyc[0]]
            for n in range(len(cyc)):
                u, v = loop[n], loop[n + 1]
                for i, res in S.successors(u):
                    if apply(u, res) == v:
                        print(S.fmt_step(n + 1, u, i, res))
                        break
            if oc is not None:
                print(f"  data output on the loop: {list(cyc[0][oc]) or 'no token'}")
            worst = 1
            break
        bad, want = R["bad"], R["want"]
        path = S.path(R["parent"], bad)
        oc = S.outs.get("chOut")
        got = list(bad[oc]) if oc is not None else []
        w = S.width[oc] if oc is not None else 32
        print(f"\nCOUNTEREXAMPLE  input ({tag})")
        print(f"  C reference ({os.path.basename(a.c)}:{a.func}) returns {cres}"
              f"  (as the {w}-bit output token: {cres % P(w)})")
        if got:
            print(f"  this schedule ends with out = {got}  (signed: {[signed(x, w) for x in got]})")
        else:
            print("  this schedule ends with NO token on the data output")
        extra = [c for c in range(g.N) if bad[c] != want[c]]
        print("  channels that differ from the expected final store: " +
              "; ".join(f"{S.cn(c)} has {list(bad[c])}, expected {list(want[c])}" for c in extra))
        print(f"  schedule ({len(path)} firings; terminal: no rule enabled):")
        steps = list(enumerate(path, 1))
        if len(steps) > a.trace_max:
            h = a.trace_max // 2
            steps = steps[:h] + [None] + steps[-h:]
        for s in steps:
            if s is None:
                print(f"  ... ({len(path) - 2 * (a.trace_max // 2)} firings omitted; --trace-max) ...")
                continue
            n, (p, i, res, t) = s
            print(S.fmt_step(n, p, i, res))
        print(f"  final store: {S.fmt_store(bad)}")
        worst = 1
        break
    print("token search:", {0: "PASS (no counterexample; complete on every vector)",
                            1: "FAIL (counterexample above)", 2: "INCONCLUSIVE (bound hit)"}[worst])
    return worst


if __name__ == "__main__":
    try:
        sys.exit(main())
    except BrokenPipeError:
        sys.exit(1)
