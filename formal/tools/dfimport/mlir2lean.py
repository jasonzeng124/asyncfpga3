#!/usr/bin/env python3
"""Export the dataflow graph bdc EMITS for a kernel as a Lean `List Rule` (probe C-8i).

    python3 formal/tools/dfimport/mlir2lean.py [MLIR] [-o OUT.lean] [--segments SEG.lean]
        [--ns LEAN.NAMESPACE --graph-module LEAN.MODULE --label LABEL --short SHORT]

The defaults of the four naming options reproduce the gcd_hw files of C-8i
(namespace Formal.Net.GcdHw.Gcd, module Formal.Net.GcdHw).  Nothing else in
this tool is kernel-specific (probe C-8v ran it unchanged on ipow); the
generated port names are `ch<ArgName>` for each function argument (argNames,
first letter capitalised), `chOut` for the one data result and `chEnd` for the
end control result.

MLIR defaults to the file cells/hw/build_hw.sh feeds bdc for gcd_hw:
build/frontend/gcd/comp/handshake_transformed.mlir if it exists, else its
committed copy cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir
(cloud/setup-toolchain.sh restores build/frontend from there).

It does NOT re-parse MLIR itself.  It imports bdc's own modules read-only
(bdc/hs/parse.py, bdc/emit.py) and reads bdc's internal graph:
  * `func.nodes` from bdc's parser,
  * bdc's `Emitter(func)`: channel widths (`e.ch`) and the op-fusion plan
    (`e.fusion`, BDC_OP_FUSION, default on): fused regions become ONE
    `Rule.comp` each (their expression DAG, with bdc's folded literals and
    absorbed forks), absorbed (source, constant) pairs disappear,
  * the lowering choices of emit.py: `br` and 1-input `merge` are wires
    (pass-through), a 1-input `control_merge` is a fork + constant index 0,
    an n-input `control_merge` is an arbiter + fork (n `Rule.cm` labels),
    `cond_br` steers on cond bit 0, a 2-way `mux` selects on bit 0, an n-way
    mux on the low ceil(log2 n) bits.

One modelling step is this tool's own (H_SOURCE_ETERNAL): a `source`, and
every fork/constant driven only by sources, is an always-valid channel; its
consumers read the literal.  bdc does exactly this for the (source, constant)
pairs it absorbs; this tool extends it to the source->fork->constant chains
bdc leaves live (bd_src holds req high, so at token level these never wait).

With --segments it also runs a symbolic execution of the exported rules
(same rules, same expression type as `Formal.Net.GcdHw.symVI`) and writes the
schedule certificates that GcdHwSeg.lean checks with the kernel.
"""

import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "bdc"))

import emit  # noqa: E402  (bdc/emit.py, read-only)
from hs import parse  # noqa: E402  (bdc/hs/parse.py, read-only)


def default_mlir():
    b = os.path.join(ROOT, "build/frontend/gcd/comp/handshake_transformed.mlir")
    if os.path.exists(b):
        return b
    return os.path.join(ROOT, "cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir")


# ---------------------------------------------------------------------------
# Expressions: tuples mirroring Lean's `E`
#   ("var", k) ("lit", v) ("un", uop, w, a) ("bin", bop, w, a, b) ("sel", s, a, b)
#   uop: "trunci" | "extui" | ("extsi", dw);  bop: "addi".. | ("cmpi", pred)

def mask(v, w):
    return int(v) & ((1 << w) - 1) if w > 0 else 0


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
    if t == "sel":
        return f"(.sel {e_lean(e[1])} {e_lean(e[2])} {e_lean(e[3])})"
    raise ValueError(e)


def e_subst(sig, e):
    t = e[0]
    if t == "var":
        return sig[e[1]] if e[1] < len(sig) else ("lit", 0)
    if t == "lit":
        return e
    if t == "un":
        return ("un", e[1], e[2], e_subst(sig, e[3]))
    if t == "bin":
        return ("bin", e[1], e[2], e_subst(sig, e[3]), e_subst(sig, e[4]))
    return ("sel", e_subst(sig, e[1]), e_subst(sig, e[2]), e_subst(sig, e[3]))


# ---------------------------------------------------------------------------
# Graph export

class Graph:
    def __init__(self, path):
        self.path = path
        funcs = [f for f in parse.parse_module(open(path).read(), filename=path)
                 if not f.is_declaration]
        if len(funcs) != 1:
            raise SystemExit(f"{path}: expected one handshake.func, got {len(funcs)}")
        self.func = f = funcs[0]
        self.em = em = emit.Emitter(f)
        self.fusion = fu = em.fusion
        nodes = f.nodes
        skip = fu.skip if fu is not None else set()

        # wires: br, 1-input merge
        alias = {}
        for n in nodes:
            if n.op == "br" or (n.op == "merge" and len(n.operands) == 1):
                alias[n.results[0]] = n.operands[0]

        def A(v):
            while v in alias:
                v = alias[v]
            return v
        self.A = A

        # H_SOURCE_ETERNAL: values always valid with a fixed (or no) value
        eternal = {}
        changed = True
        while changed:
            changed = False
            for i, n in enumerate(nodes):
                if any(r in eternal for r in n.results):
                    continue
                if n.op == "source":
                    eternal[n.results[0]] = None
                    changed = True
                elif n.op == "fork" and A(n.operands[0]) in eternal:
                    for r in n.results:
                        eternal[r] = eternal[A(n.operands[0])]
                    changed = True
                elif n.op == "constant" and A(n.operands[0]) in eternal:
                    w = em.width(n.results[0])
                    eternal[n.results[0]] = mask(self.const_value(n), w)
                    changed = True
        self.eternal = eternal

        self.chan = {}
        self.chname = []
        for a in f.args:
            self.ch(a.ssa_name)
        self.rules = []   # (lean text, python tuple, comment)
        self.collapsed = []
        self.ops_seen = {}
        outputs = []

        def lit_of(v):
            return ("lit", eternal[A(v)])

        def comp(ins, out, expr, comment):
            # eternal inputs become literals; renumber the rest
            live, sig = [], []
            for v in ins:
                if A(v) in eternal:
                    if eternal[A(v)] is None:
                        raise SystemExit(f"{comment}: reads a bare source as data")
                    sig.append(lit_of(v))
                else:
                    sig.append(("var", len(live)))
                    live.append(self.ch(v))
            expr = e_subst(sig, expr)
            self.rules.append(("comp", live, self.ch(out), expr, comment))

        for i, n in enumerate(nodes):
            nm = n.attrs.get("handshake.name", n.op)
            self.ops_seen[n.op] = self.ops_seen.get(n.op, 0) + 1
            if i in skip:
                continue
            if any(r in eternal for r in n.results):
                self.collapsed.append(nm)
                continue
            if fu is not None and i in fu.anchor_region:
                reg = fu.anchor_region[i]
                expr = self.region_expr(reg, reg.anchor)
                names = "+".join(nodes[j].attrs.get("handshake.name", nodes[j].op)
                                 for j in reg.node_ids)
                comp(list(reg.ext_inputs), n.results[0], expr, f"fused {names}")
                continue
            op = n.op
            if op in ("br",) or (op == "merge" and len(n.operands) == 1):
                continue
            if op == "merge":
                raise SystemExit(f"{nm}: n-input merge not modelled (nondeterministic data merge)")
            if op == "fork":
                self.rules.append(("fork", self.ch(n.operands[0]),
                                   [self.ch(r) for r in n.results], nm))
            elif op == "cond_br":
                c, d = n.operands
                t, fl = n.results
                if A(c) in eternal or A(d) in eternal:
                    raise SystemExit(f"{nm}: cond_br on an eternal channel")
                self.rules.append(("branch", self.ch(c), self.ch(d), self.ch(t), self.ch(fl), nm))
            elif op == "mux":
                sel, ins = n.operands[0], n.operands[1:]
                iw = 1 if len(ins) == 2 else max(1, (len(ins) - 1).bit_length())
                self.rules.append(("mux", self.ch(sel), [self.ch(x) for x in ins],
                                   self.ch(n.results[0]), iw, nm))
            elif op == "control_merge":
                res, idx = n.results
                for k, x in enumerate(n.operands):
                    self.rules.append(("cm", self.ch(x), self.ch(res), self.ch(idx), k,
                                       f"{nm} input {k}"))
            elif op == "sink":
                if A(n.operands[0]) in eternal:
                    self.collapsed.append(nm)
                    continue
                self.rules.append(("sink", self.ch(n.operands[0]), nm))
            elif op == "constant":
                w = em.width(n.results[0])
                comp([n.operands[0]], n.results[0], ("lit", mask(self.const_value(n), w)), nm)
                # the trigger is consumed, its value ignored: drop the var
                r = self.rules[-1]
            elif op in ("trunci", "extui", "extsi"):
                x = n.operands[0]
                sw, dw = em.width(x), em.width(n.results[0])
                uo = {"trunci": "trunci", "extui": "extui", "extsi": ("extsi", dw)}[op]
                w = dw if op == "trunci" else sw
                comp([x], n.results[0], ("un", uo, w, ("var", 0)), nm)
            elif op in emit.FUSABLE_OPS:
                # unfused lowering (BDC_OP_FUSION=0): one comp per op
                expr = self.op_expr(i, {p: ("var", pos) for p, pos in
                                        emit._FUSABLE_CHANS[op].items()})
                comp(list(n.operands), n.results[0], expr, nm)
            elif op == "end":
                outputs = [self.ch(v) for v in n.operands]
            else:
                raise SystemExit(f"{nm}: op {op!r} has no rule")
        self.outputs = outputs
        self.N = len(self.chname)
        # control spine: control channels not consumed by a comp rule
        comp_ins = {c for r in self.rules if r[0] == "comp" for c in r[1]}
        consumed = set()
        for r in self.rules:
            for c in self.rule_ins(r):
                consumed.add(c)
        self.spine = [c for c, v in enumerate(self.chname)
                      if self.is_ctl(v) and c not in comp_ins and c in consumed]

    def is_ctl(self, v):
        return self.em.ch[v][1]

    def ch(self, v):
        v = self.A(v)
        if v not in self.chan:
            self.chan[v] = len(self.chname)
            self.chname.append(v)
        return self.chan[v]

    @staticmethod
    def const_value(n):
        val = n.attrs.get("value")
        raw = getattr(val, "value", val)
        if isinstance(raw, bool):
            return int(raw)
        if not isinstance(raw, int):
            raise SystemExit(f"constant {raw!r} is not an integer")
        return raw

    def op_expr(self, i, ports):
        n = self.func.nodes[i]
        op = n.op
        w = self.em.width(n.operands[0]) if op != "select" else self.em.width(n.results[0])
        if op == "cmpi":
            pred = self.em._predicate(n)
            return ("bin", ("cmpi", pred), self.em.width(n.operands[0]), ports["a"], ports["b"])
        if op == "select":
            return ("sel", ports["s"], ports["a"], ports["b"])
        return ("bin", op, self.em.width(n.results[0]), ports["a"], ports["b"])

    def region_expr(self, reg, i):
        n = self.func.nodes[i]
        ports = {}
        for port, pos in emit._FUSABLE_CHANS[n.op].items():
            kind, x = reg.ref[(i, port)]
            if kind == "const":
                w = self.em.width(n.operands[pos])
                ports[port] = ("lit", mask(int(x), w))
            elif kind == "ext":
                ports[port] = ("var", x)
            else:
                ports[port] = self.region_expr(reg, x)
        return self.op_expr(i, ports)

    @staticmethod
    def rule_ins(r):
        k = r[0]
        if k == "comp":
            return r[1]
        if k in ("fork", "cm", "sink"):
            return [r[1]]
        if k == "branch":
            return [r[1], r[2]]
        if k == "mux":
            return [r[1]] + r[2]
        raise ValueError(r)

    @staticmethod
    def rule_lean(r):
        k = r[0]
        L = lambda xs: "[" + ", ".join(map(str, xs)) + "]"
        if k == "comp":
            return f".comp {L(r[1])} {r[2]} {e_lean(r[3])}"
        if k == "fork":
            return f".fork {r[1]} {L(r[2])}"
        if k == "branch":
            return f".branch {r[1]} {r[2]} {r[3]} {r[4]}"
        if k == "mux":
            return f".mux {r[1]} {L(r[2])} {r[3]} {r[4]}"
        if k == "cm":
            return f".cm {r[1]} {r[2]} {r[3]} {r[4]}"
        if k == "sink":
            return f".sink {r[1]}"
        raise ValueError(r)


# ---------------------------------------------------------------------------
# Symbolic execution (mirrors Formal.Net.GcdHw.Rule.fire with symVI)

class Sym:
    def __init__(self, g, facts):
        self.g = g
        self.facts = facts  # list of (expr, bool)

    def test(self, v):
        for e, b in self.facts:
            if e == v:
                return b
        return None

    def fire(self, r, st):
        k = r[0]
        if k == "mux":
            _, s, ds, o, iw = r[:5]
            if not st[s]:
                return None
            v = st[s][0]
            if v[0] != "lit":
                return None
            j = v[1] % (1 << iw)
            if j >= len(ds):
                return None
            d = ds[j]
            if d == s or not st[d]:
                return None
            pop = {s: 1}
            pop[d] = pop.get(d, 0) + 1
            return pop, {o: [st[d][0]]}
        ins = self.g.rule_ins(r)
        if any(not st[c] for c in ins):
            return None
        vs = [st[c][0] for c in ins]
        pop = {c: 1 for c in ins}
        if k == "comp":
            return pop, {r[2]: [e_subst(vs, r[3])]}
        if k == "fork":
            return pop, {c: vs[:1] for c in r[2]}
        if k == "branch":
            b = self.test(vs[0])
            if b is None:
                return None
            return pop, {(r[3] if b else r[4]): [vs[1]]}
        if k == "cm":
            out = {r[2]: vs[:1]}
            out.setdefault(r[3], []).append(("lit", r[4]))
            return pop, out
        if k == "sink":
            return pop, {}
        raise ValueError(r)

    def apply(self, st, res):
        pop, push = res
        st = [list(x) for x in st]
        for c, n in pop.items():
            st[c] = st[c][n:]
        for c, xs in push.items():
            st[c] = st[c] + xs
        return st

    def run(self, st):
        """Fire the lowest enabled rule until none is enabled."""
        sched = []
        self.trace = []
        while True:
            for i, r in enumerate(self.g.rules):
                res = self.fire(r, st)
                if res is not None:
                    st = self.apply(st, res)
                    sched.append(i)
                    self.trace.append(st)
                    break
            else:
                return st, sched
            if len(sched) > 5000:
                raise SystemExit("symbolic run does not get stuck")


def generalize(g, st):
    """Abstract every data token (non-control, not on an index channel) into a
    variable, equal expressions into the same variable: returns (template,
    sigma)."""
    idx_chans = {r[1] for r in g.rules if r[0] == "mux"}
    sig, tmpl = [], []
    for c, toks in enumerate(st):
        row = []
        for t in toks:
            if g.is_ctl(g.chname[c]) or (c in idx_chans and t[0] == "lit"):
                row.append(t)
            else:
                if t not in sig:
                    sig.append(t)
                row.append(("var", sig.index(t)))
        tmpl.append(row)
    return tmpl, sig


def store_lean(st):
    return "[" + ", ".join("[" + ", ".join(e_lean(t) for t in row) + "]" for row in st) + "]"


def sparse_lean(g, st):
    ent = [f"({c}, [" + ", ".join(e_lean(t) for t in row) + "])" for c, row in enumerate(st) if row]
    return f"sp {g.N} [" + ", ".join(ent) + "]"


def conds_pending(g, st):
    """The condition tokens waiting at branches that cannot fire."""
    out = []
    for r in g.rules:
        if r[0] == "branch" and st[r[1]] and st[r[2]]:
            v = st[r[1]][0]
            if v not in out:
                out.append(v)
    return out


def explore(g):
    """Cut the symbolic run at every pending branch condition.  States are
    templates (generalized stuck stores); edges are (from, facts, schedule,
    to, sigma).  Returns templates, edges."""
    init = [[] for _ in range(g.N)]
    for k, a in enumerate(g.func.args):
        c = g.chan[g.A(a.ssa_name)]
        init[c] = [("lit", 0)] if a.is_control else [("var", k)]
    templates = []   # list of (name, template)
    edges = []
    tkey = {}

    def add_template(t):
        key = repr(t)
        if key not in tkey:
            tkey[key] = len(templates)
            templates.append(t)
            work.append(tkey[key])
        return tkey[key]

    work = []
    # state 0: the initial store itself (not generalized: env = [a, b])
    templates.append(init)
    tkey[repr(init)] = 0
    work.append(0)
    while work:
        ti = work.pop(0)
        t = templates[ti]
        sy0 = Sym(g, [])
        s0, sched0 = sy0.run(t)
        tr0 = sy0.trace
        conds = conds_pending(g, s0)
        if not conds:
            tmpl, sig = generalize(g, s0)
            if not sched0:
                continue          # quiescent: a final template
            tj = add_template(tmpl)
            edges.append((ti, [], sched0, tj, sig, tr0))
            continue
        if len(conds) > 1:
            raise SystemExit(f"template {ti}: {len(conds)} independent pending conditions")
        c = conds[0]
        for b in (True, False):
            sy1 = Sym(g, [(c, b)])
            s1, sched1 = sy1.run(s0)
            tmpl, sig = generalize(g, s1)
            tj = add_template(tmpl)
            edges.append((ti, [(c, b)], sched0 + sched1, tj, sig, tr0 + sy1.trace))
        if len(templates) > 60:
            raise SystemExit("too many templates")
    return templates, edges


# ---------------------------------------------------------------------------

def port_names(g):
    """Lean names of the function's input and output channels (generic)."""
    ins = []
    for k, a in enumerate(g.func.args):
        nm = getattr(a, "name", None) or a.ssa_name
        nm = "".join(ch for ch in nm if ch.isalnum()) or f"In{k}"
        ins.append((f"ch{nm[0].upper()}{nm[1:]}", g.chan[g.A(a.ssa_name)]))
    data = [c for c in g.outputs if not g.is_ctl(g.chname[c])]
    ctl = [c for c in g.outputs if g.is_ctl(g.chname[c])]
    if len(data) > 1 or len(ctl) != 1:
        raise SystemExit(f"results: {len(data)} data, {len(ctl)} control; "
                         "expected at most one data result and one end token")
    outs = ([("chOut", data[0])] if data else []) + [("chEnd", ctl[0])]
    return ins, outs


def lean_graph(g, opt):
    out = []
    w = out.append
    w("import Formal.Net.GcdHwLib")
    w("")
    w("/-!")
    w("# GENERATED by formal/tools/dfimport/mlir2lean.py -- DO NOT EDIT")
    w("")
    w(f"Source: `{os.path.relpath(g.path, ROOT)}` (the handshake MLIR bdc consumes for")
    w(f"{opt.label}), read with bdc's own parser and lowered with bdc's own fusion plan")
    w(f"(BDC_OP_FUSION={'1' if g.fusion is not None else '0'}, "
      f"BDC_FORK_FUSION={'1' if emit.BDC_FORK_FUSION else '0'}, "
      f"BDC_MAX_FUSE_NODES={emit.MAX_FUSE_NODES}).")
    w(f"{len(g.func.nodes)} MLIR ops -> {len(g.rules)} firing rules over {g.N} channels.")
    w("MLIR op counts: " + ", ".join(f"{k} {v}" for k, v in sorted(g.ops_seen.items())) + ".")
    w("Collapsed as always-valid (H_SOURCE_ETERNAL): " + ", ".join(g.collapsed) + ".")
    w("-/")
    w("")
    w(f"namespace {opt.ns}")
    w("")
    w("open Formal.Net.GcdHw")
    w("")
    w("/-- Channel names (bdc SSA values), by channel number. -/")
    w("def chanNames : List String := [" +
      ", ".join(f'"{v}"' for v in g.chname) + "]")
    w("")
    w(f"def N : Nat := {g.N}")
    w("")
    w("def rules : List Rule := [")
    for k, r in enumerate(g.rules):
        sep = "," if k + 1 < len(g.rules) else ""
        w(f"  {g.rule_lean(r)}{sep}  -- {k}: {r[-1]}")
    w("]")
    w("")
    w("/-- The control spine (H_ONE_INVOCATION counts tokens here). -/")
    w("def spine : List Nat := [" + ", ".join(map(str, g.spine)) + "]")
    w("")
    w("/-- Function inputs and outputs. -/")
    ins, outs = port_names(g)
    for nm, c in ins + outs:
        w(f"def {nm} : Nat := {c}")
    w("")
    w("theorem spine_nodup : spine.Nodup := by decide +kernel")
    w("theorem ins_ok : checkIns rules = true := by decide +kernel")
    w("theorem outs_ok : checkOuts spine rules = true := by decide +kernel")
    w("theorem spine_ok : rules.all (Rule.okP spine) = true := by decide +kernel")
    w("theorem bounded_ok : bounded N rules = true := by decide +kernel")
    w("")
    w(f"end {opt.ns}")
    return "\n".join(out) + "\n"


def lean_segments(g, templates, edges, opt):
    out = []
    w = out.append
    w(f"import {opt.graph_module}")
    w("")
    w("/-!")
    w("# GENERATED by formal/tools/dfimport/mlir2lean.py --segments -- DO NOT EDIT")
    w("")
    w(f"Symbolic schedule certificates for the imported {opt.short} graph. `T k` is a")
    w("template store (tokens are expressions over environment variables); each")
    w("`seg_k` is one kernel-checked symbolic run from a template, under at most one")
    w("branch fact, to another template instantiated by `sig_k`.")
    w(f"{len(templates)} templates, {len(edges)} segments.")
    w("-/")
    w("")
    w(f"namespace {opt.ns}")
    w("")
    w("open Formal.Net.GcdHw")
    w("")
    for k, t in enumerate(templates):
        nv = max([-1] + [_maxvar(e) for row in t for e in row]) + 1
        nz = {c: row for c, row in enumerate(t) if row}
        desc = ", ".join(f"{g.chname[c]}:{len(row)}" for c, row in nz.items())
        w(f"/-- template {k} ({nv} vars): {desc} -/")
        w(f"def T{k} : List (List E) := {sparse_lean(g, t)}")
        w("")
    for k, (ti, facts, sched, tj, sig, trace) in enumerate(edges):
        F = "[" + ", ".join(f"({e_lean(e)}, {'true' if b else 'false'})" for e, b in facts) + "]"
        w(f"def F{k} : List (E × Bool) := {F}")
        w(f"def sched{k} : List Nat := {sched}")
        w(f"def sig{k} : List E := [" + ", ".join(e_lean(e) for e in sig) + "]")
        w(f"/-- segment {k}: T{ti} -> T{tj}, {len(sched)} firings -/")
        w(f"def trace{k} : List (List (List E)) := [")
        for n, st in enumerate(trace):
            w(f"  {sparse_lean(g, st)}{',' if n + 1 < len(trace) else ''}")
        w("]")
        w(f"theorem seg{k} : execL (symVI F{k}) rules T{ti} sched{k} = "
          f"some (T{tj}.map (List.map (E.subst sig{k}))) :=")
        w(f"  execL_of_chainOK (ms := trace{k}) (by decide +kernel)")
        w("")
    w(f"end {opt.ns}")
    return "\n".join(out) + "\n"


def _maxvar(e):
    if e[0] == "var":
        return e[1]
    if e[0] == "lit":
        return -1
    return max(_maxvar(x) for x in e[1:] if isinstance(x, tuple) and x and
               isinstance(x[0], str) and x[0] in ("var", "lit", "un", "bin", "sel"))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("mlir", nargs="?", default=None)
    ap.add_argument("-o", "--out", default=None)
    ap.add_argument("--segments", default=None)
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--ns", default="Formal.Net.GcdHw.Gcd", help="Lean namespace")
    ap.add_argument("--graph-module", default="Formal.Net.GcdHw",
                    help="Lean module of the -o file (imported by --segments)")
    ap.add_argument("--label", default="gcd_hw", help="design name for the docstring")
    ap.add_argument("--short", default="gcd", help="kernel name for the docstring")
    a = ap.parse_args()
    g = Graph(a.mlir or default_mlir())
    text = lean_graph(g, a)
    if a.out:
        open(a.out, "w").write(text)
    elif not a.segments and not a.summary:
        sys.stdout.write(text)
    if a.segments or a.summary:
        templates, edges = explore(g)
        if a.segments:
            open(a.segments, "w").write(lean_segments(g, templates, edges, a))
        if a.summary:
            print(f"rules {len(g.rules)} channels {g.N} spine {len(g.spine)}")
            print("collapsed", g.collapsed)
            for k, (ti, facts, sched, tj, sig, _) in enumerate(edges):
                print(f"seg{k}: T{ti} -{'+' if facts and facts[0][1] else ('-' if facts else '')}"
                      f"-> T{tj}  {len(sched)} firings  sig={len(sig)} vars")
    return 0


if __name__ == "__main__":
    sys.exit(main())
