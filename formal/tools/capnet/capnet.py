#!/usr/bin/env python3
"""capnet: the concrete circuit network of a bdc kernel, for the circuit-level safety proof.

Probe C-8y. This is the generalisation of two single-kernel generators written for gcd_hw:
  * formal/lean/Wip/C8l/linkexport.py  (bdc's link placement -> `links`, ring certificate)
  * formal/lean/Wip/C8m/netgen.py      (bdc's graph + links -> the Ops network `tab`/`ops`)
  * formal/lean/Wip/C8r/spinegen.py    (the circuit spine `spL`)
Those files are left untouched. With `--kernel gcd --gcd-compat` this script reproduces
their outputs byte for byte (regression check, see check.sh); with `--kernel ipow` it emits
the ipow files. Nothing in the network construction is kernel-specific: the kernel enters
only through its handshake MLIR (read with bdc's own parser and Emitter, through C-8i's
importer formal/tools/dfimport/mlir2lean.py) and the Lean names in PROFILES.

Usage:
  capnet.py --kernel ipow links -o Formal/Net/IpowCapLinks.lean
  capnet.py --kernel ipow net   -o Formal/Net/IpowCapNet.lean
  capnet.py --kernel ipow spine            # prints `spL` and `start` (consumed by instantiate.py)
  capnet.py --kernel gcd --gcd-compat links|net|spine   # gcd regression (must equal the 8l/8m/8r files)

Shape assumptions (asserted, so a kernel that breaks them fails loudly, not silently):
  * function arguments are channels 0, 1, 2 = two data inputs and the start token (the Lean
    side's `srcV a b` / `OpChk .src` hard-code this shape);
  * one data result (`chOut`) and one end token (`chEnd`);
  * control_merges have 1, 2 or 3 inputs; muxes 2 or 3 data inputs (the Lean operator kinds).
"""
import argparse, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "dfimport"))
for k in ["BDC_OP_FUSION", "BDC_CONST_FOLD", "BDC_FORK_FUSION", "BDC_MAX_FUSE_NODES", "BDC_PROBE",
          "BDC_RING_PAD", "BDC_LINK_FASTFALL", "BDC_SELECT_PAD"]:
    os.environ.pop(k, None)
import mlir2lean  # noqa: E402

PROFILES = {
    "gcd": dict(mlir="gcd", label="gcd_hw", G="GcdHw", gns="Formal.Net.GcdHw.Gcd", gmod="Formal.Net.GcdHw",
                lns="Formal.Net.GcdHw.Gcd", nns="Formal.Net.CapNet.Gcd", nimport="Formal.Net.CapstoneNetSound",
                lgen="formal/lean/Wip/C8l/linkexport.py", ngen="formal/lean/Wip/C8m/netgen.py",
                nopen="Formal.Net Formal.Net.CapNet Formal.Net.GcdHw"),
    "ipow": dict(mlir="ipow", label="ipow_ps", G="IpowHw", gns="Formal.Net.IpowHw", gmod="Formal.Net.IpowHw",
                 lns="Formal.Net.IpowCap", nns="Formal.Net.IpowCap", nimport="Formal.Net.IpowCapNetSound",
                 lgen="formal/tools/capnet/capnet.py links", ngen="formal/tools/capnet/capnet.py net",
                 lmod="Formal.Net.IpowCapLinks", pre="ipowhw",
                 nopen="Formal.Net Formal.Net.GcdHw\nopen Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk"),
}


def kernel_mlir(k):
    b = os.path.join(ROOT, f"build/frontend/{k}/comp/handshake_transformed.mlir")
    return b if os.path.exists(b) else os.path.join(ROOT, f"cloud/fixtures/frontend/{k}/comp/handshake_transformed.mlir")


def outs_of(r):
    k = r[0]
    if k == "fork": return list(r[2])
    if k == "comp": return [r[2]]
    if k == "branch": return [r[3], r[4]]
    if k == "mux": return [r[3]]
    if k == "cm": return [r[2], r[3]]
    if k == "sink": return []
    raise SystemExit(f"unknown rule {r}")


# ====================================================================== links (was linkexport.py)
def links_of(g):
    em = g.em
    linked = sorted(em.linked)
    depth = dict(em.depth)
    chan_links, unmapped = {}, []
    for v in linked:
        a = g.A(v)
        if a in g.chan:
            c = g.chan[a]
            chan_links[c] = chan_links.get(c, 0) + depth.get(v, 1)
        else:
            unmapped.append((v, a, "eternal" if a in g.eternal else "no channel"))
    return linked, chan_links, unmapped


def gen_links(g, P):
    linked, chan_links, unmapped = links_of(g)
    rules = list(g.rules)
    ins = [mlir2lean.Graph.rule_ins(r) for r in rules]
    cons = {}
    for i, cs in enumerate(ins):
        for c in cs: cons.setdefault(c, []).append(i)
    succ = {i: set() for i in range(len(rules))}
    for i, r in enumerate(rules):
        for c in outs_of(r):
            if c in chan_links: continue
            for j in cons.get(c, []): succ[i].add(j)
    indeg = {i: 0 for i in succ}
    for i in succ:
        for j in succ[i]: indeg[j] += 1
    order = [i for i in succ if indeg[i] == 0]; k = 0
    while k < len(order):
        i = order[k]; k += 1
        for j in succ[i]:
            indeg[j] -= 1
            if indeg[j] == 0: order.append(j)
    if len(order) != len(rules):
        raise SystemExit(f"a cycle of {P['G']} rules carries no link: {set(succ) - set(order)}")
    rank = {i: 0 for i in succ}
    for i in order:
        for j in succ[i]: rank[j] = max(rank[j], rank[i] + 1)
    print(f"rules {len(rules)} channels {g.N} linked SSA {len(linked)} -> {len(chan_links)} channels,"
          f" stages {sum(chan_links.values())}, unmapped {len(unmapped)}, max rank {max(rank.values())}",
          file=sys.stderr)
    for u in unmapped: print("  unmapped:", u, file=sys.stderr)
    prods = {}
    for i, r in enumerate(rules):
        for c in outs_of(r): prods.setdefault(c, []).append(i)
    edges = []
    for c in sorted(set(prods) & set(cons)):
        for p in prods[c]:
            for q in cons[c]:
                edges.append((p, q, chan_links.get(c, 0), c))
    NN = max(max(p, q) for p, q, _, _ in edges) + 1
    K = 3
    cert = []
    for s0 in range(NN):
        d = [K] * NN
        changed = True
        while changed:
            changed = False
            for (p, q, wt, _) in edges:
                cand = min(K, wt) if p == s0 else min(K, d[p] + wt)
                if cand < d[q]: d[q] = cand; changed = True
        cert.append(d)
    mincyc = min(cert[s0][s0] for s0 in range(NN))
    print(f"ring graph: {NN} nodes, {len(edges)} edges, min cycle stages (capped at {K}): {mincyc}", file=sys.stderr)
    adj = {}
    for idx, (p, q, wt, c) in enumerate(edges): adj.setdefault(p, []).append((q, idx))

    def find_cycle():
        for s0 in range(NN):
            stack = [(s0, [])]; seen = set()
            while stack:
                v, path = stack.pop()
                for (q, idx) in adj.get(v, []):
                    if q == s0: return s0, path + [idx]
                    if q not in seen:
                        seen.add(q); stack.append((q, path + [idx]))
        return None
    cyc = find_cycle()
    out = []
    w = out.append
    w(f"import {P['gmod']}")
    w("import Formal.Net.RingCheckCert")
    w("")
    w("/-!")
    w(f"# GENERATED by {P['lgen']} -- DO NOT EDIT")
    w("")
    w(f"bdc's storage placement for {P['label']} (`emit.Emitter(func).linked` / `.depth`: link_sites =")
    w("rule 1 measurability + rule 2 cycle breaking; ring_depths + slack stages), mapped onto the")
    w(f"channels of `{P['gns']}.rules`. {len(linked)} linked SSA values -> {len(chan_links)} {P['G']}")
    w(f"channels, {sum(chan_links.values())} bd_link stages in all.")
    if unmapped:
        w(f"Linked values with no {P['G']} channel (not modelled as channels at token level):")
        for v, a, why in unmapped:
            w(f"* `{v}` (root `{a}`): {why}")
    w("-/")
    w("")
    w(f"namespace {P['lns']}")
    w("")
    w("set_option maxRecDepth 20000")
    w("")
    w("/-- (channel, number of bd_link stages on it). -/")
    w("def links : List (Nat × Nat) := [" + ", ".join(f"({c}, {n})" for c, n in sorted(chan_links.items())) + "]")
    w("")
    w("/-- Rank certificate: every rule-to-rule edge through an unlinked channel goes up. -/")
    w("def rank : List Nat := [" + ", ".join(str(rank[i]) for i in range(len(rules))) + "]")
    w("")
    w("/-- The rule graph with bdc's storage: node = firing rule, edge = channel from its producer")
    w("rule to its consumer rule, weight = bd_link stages on the channel (0 = wire). -/")
    w("def ringG : Formal.Net.RingCheck.Graph := [" + ", ".join(f"⟨{p}, {q}, {wt}⟩" for p, q, wt, _ in edges) + "]")
    w("")
    w("/-- The channel of each edge of `ringG` (same order). -/")
    w("def ringCh : List Nat := [" + ", ".join(str(c) for _, _, _, c in edges) + "]")
    w("")
    w("/-- Untrusted certificate (capped shortest closed-walk tables, from Python). -/")
    w("def ringCert : List (List Nat) := [" + ", ".join("[" + ", ".join(map(str, d)) + "]" for d in cert) + "]")
    w("")
    w(f"/-- A cycle of `ringG` (edge indices), for the non-vacuity witness. -/")
    w("def aCycle : List Nat := [" + ", ".join(map(str, cyc[1])) + "]")
    w(f"def aCycleStart : Nat := {cyc[0]}")
    w(f"def ringN : Nat := {NN}")
    w("")
    w(f"end {P['lns']}")
    cw = sum(edges[i][2] for i in cyc[1])
    return "\n".join(out) + "\n", dict(NN=NN, mincyc=mincyc, cyclen=len(cyc[1]), cw=cw)


def gen_ring(info, P, pre):
    """The ring theorem file: kernel-checks the certificate in chunks of 8 nodes and proves
    `<pre>_ring_ge3`, `<pre>_cycle_linked`, `<pre>_has_cycle` and the tightness control
    `<pre>_not_ge(cw+1)` (the explicit cycle carries cw stages). Reuses C-8l's generic
    `follow` lemmas and C-9b's checker."""
    NN, cw = info["NN"], info["cw"]
    out = []; w = out.append
    w(f"import {P['lmod']}\nimport Formal.Net.CapstoneRing\n")
    w(f"/-!\n# GENERATED by formal/tools/capnet/capnet.py ring -- DO NOT EDIT\n")
    w(f"Every cycle of the {P['label']} circuit carries >= 3 bd_link stages (C-8l's statement for gcd_hw,")
    w(f"same checker): `ringG` ({P['lmod']}) is bdc's {P['label']} graph at rule granularity, weighted by")
    w(f"bdc's link stages. `{pre}_ring_ge3`: every closed walk carries >= 3 stages (C-9b's verified")
    w(f"`RingCheck`, certificate re-checked by the kernel in chunks). `{pre}_has_cycle`: non-vacuity.")
    w(f"`{pre}_not_ge{cw + 1}`: the explicit cycle carries exactly {cw} stages, so the bound is "
      + ("tight." if cw == 3 else f"not tight (the found cycle has {cw})."))
    w("-/\n")
    w(f"namespace {P['lns']}\nopen Formal.Net.RingCheck\n")
    w(f"theorem ring_n : numNodes ringG = {NN} := by decide +kernel\n")
    chunks = [(a, min(8, NN - a)) for a in range(0, NN, 8)]
    for i, (a, n) in enumerate(chunks):
        w("set_option maxRecDepth 20000 in")
        w(f"theorem ring_B{i} : certCheckFrom ringG 3 ringCert (List.range' {a} {n}) = true := by decide +kernel")
    w("")
    last = len(chunks) - 1
    w(f"theorem ring_G{last} : certCheckFrom ringG 3 ringCert (List.range' {chunks[last][0]} {chunks[last][1]}) = true := ring_B{last}")
    for i in range(last - 1, -1, -1):
        a, n = chunks[i]
        rest = NN - a - n
        w(f"theorem ring_G{i} : certCheckFrom ringG 3 ringCert (List.range' {a} {NN - a}) = true :=")
        w(f"  certCheckFrom_append (m := {n}) (b := {rest}) ring_B{i} ring_G{i + 1}")
    w("")
    w(f"/-- Every closed walk of the {P['label']} circuit graph carries at least 3 bd_link stages. -/")
    w(f"theorem {pre}_ring_ge3 : AllCyclesGe ringG 3 := certCheckFrom_sound ring_n ring_G0\n")
    w(f"theorem {pre}_cycle_linked : AllCyclesGe ringG 1 := fun s c hw => by\n  have := {pre}_ring_ge3 s c hw; omega\n")
    w("/-- The ring graph's weights are the exported link stages. -/")
    w(f"theorem {pre}_ring_weights_are_links :")
    w("    (ringG.zip ringCh).all (fun p =>")
    w("      p.1.w == ((links.find? (fun q => q.1 == p.2)).map (·.2)).getD 0) = true ∧")
    w("    ringG.length = ringCh.length := by\n  decide +kernel\n")
    w(f"theorem aCycle_follow : Formal.Net.GcdHw.Gcd.follow ringG aCycle aCycleStart 0 = some (aCycleStart, {cw}) := by")
    w("  decide +kernel\n")
    w(f"theorem {pre}_cycle_{cw} : Walk ringG aCycleStart aCycleStart {cw} := by")
    w("  have h := aCycle_follow\n  unfold aCycle at h")
    w("  exact Formal.Net.GcdHw.Gcd.follow_start _ _ _ _ _ _ h\n")
    w(f"/-- Non-vacuity: the circuit graph has cycles. -/")
    w(f"theorem {pre}_has_cycle : ∃ s c, Walk ringG s s c := ⟨aCycleStart, {cw}, {pre}_cycle_{cw}⟩\n")
    w(f"/-- Negative control: \"every cycle carries at least {cw + 1}\" is false. -/")
    w(f"theorem {pre}_not_ge{cw + 1} : ¬ AllCyclesGe ringG {cw + 1} := by")
    w(f"  intro h; have := h _ _ {pre}_cycle_{cw}; omega\n")
    w(f"end {P['lns']}")
    return "\n".join(out) + "\n"


# ====================================================================== network (was netgen.py)
M = lambda w: 1 << w
def flip(w, a): return (a % M(w) + (M(w - 1) if w >= 1 else 0)) % M(w)
def cmpi(p, w, a, b):
    x, y = a % M(w), b % M(w); sx, sy = flip(w, a), flip(w, b)
    r = {"eq": x == y, "ne": x != y, "ult": x < y, "ule": x <= y, "ugt": y < x, "uge": y <= x,
         "slt": sx < sy, "sle": sx <= sy, "sgt": sy < sx, "sge": sy <= sx}[p]
    return 1 if r else 0
def shrsi(w, a, b):
    if a % M(w) < M(w - 1): return (a % M(w)) >> b
    return (M(w) - 1) - ((M(w) - 1 - a % M(w)) >> b)
def ev(e, env):
    t = e[0]
    if t == "var": return env[e[1]] if e[1] < len(env) else 0
    if t == "lit": return e[1]
    if t == "un":
        o, w, a = e[1], e[2], ev(e[3], env)
        if o == "trunci": return a % M(w)
        if o == "extui": return a % M(w)
        dw = o[1]
        return a % M(w) if a % M(w) < M(w - 1) else a % M(w) + M(dw) - M(w)
    if t == "bin":
        o, w, a, b = e[1], e[2], ev(e[3], env), ev(e[4], env)
        if isinstance(o, tuple): return cmpi(o[1], w, a, b)
        return {"addi": lambda: (a + b) % M(w), "subi": lambda: (a % M(w) + M(w) - b % M(w)) % M(w),
                "muli": lambda: (a * b) % M(w), "andi": lambda: (a & b) % M(w),
                "ori": lambda: (a | b) % M(w), "xori": lambda: (a ^ b) % M(w),
                "shli": lambda: (a << b) % M(w), "shrui": lambda: (a % M(w)) >> b,
                "shrsi": lambda: shrsi(w, a, b)}[o]()
    s = ev(e[1], env)
    return ev(e[2], env) if s % 2 == 1 else ev(e[3], env)


class Net:
    """The circuit network; the construction is netgen.py's, with the environment generic."""

    def __init__(self, g):
        self.g = g
        _, links, _ = links_of(g)
        self.links = links
        rules = self.rules = list(g.rules)
        NG = g.N
        ins_p, outs_p = mlir2lean.port_names(g)
        self.ports_in = [c for _, c in ins_p]
        po = dict(outs_p)
        assert self.ports_in == [0, 1, 2], ("expected 3 arguments on channels 0,1,2", ins_p)
        assert not g.is_ctl(g.chname[0]) and not g.is_ctl(g.chname[1]) and g.is_ctl(g.chname[2]), ins_p
        assert "chOut" in po and "chEnd" in po, outs_p
        self.chOut, self.chEnd = po["chOut"], po["chEnd"]
        L_ = mlir2lean.e_lean
        subst = mlir2lean.e_subst
        ctl = {c for c, v in enumerate(g.chname) if g.is_ctl(v)}
        prod_rule, cons_rule = {}, {}
        for l, r in enumerate(rules):
            for c in mlir2lean.Graph.rule_ins(r): cons_rule[c] = l
            for c in outs_of(r): prod_rule.setdefault(c, []).append(l)
        zd = {}
        for l, r in enumerate(rules):
            if r[0] == "comp":
                nm = r[4]
                for kind in ("constant", "trunci", "extui"):
                    if re.fullmatch(kind + r"\d+", nm): zd[l] = kind
        cms = {}
        for l, r in enumerate(rules):
            if r[0] == "cm": cms.setdefault(r[2], []).append((r[4], r[1], l, r[3]))
        cm_idx = {v[0][3] for v in cms.values()}
        ghost = set(ctl) | cm_idx
        changed = True
        while changed:
            changed = False
            for l, r in enumerate(rules):
                if r[0] == "fork" and r[1] in ghost:
                    for o in r[2]:
                        if o not in ghost: ghost.add(o); changed = True
        src_of = {c: c for c in range(NG)}
        hch = {}
        members = {c: [c] for c in range(NG)}
        fold_prod = {}
        for l, kind in zd.items():
            r = rules[l]; g1, g2 = r[1][0], r[2]
            rep = src_of[g1]
            src_of[g2] = rep
            members[rep].append(g2); members.pop(g2, None)
            if kind == "extui": fold_prod[g2] = (l, g1)
        for rep in members:
            ms = members[rep]
            ex = [c for c in ms if c in fold_prod]
            hch[rep] = ex[0] if ex else rep
        def sinkch(rep): return members[rep][-1]
        assert all(len(v) <= 2 for v in members.values())
        chans, cid = [], {}
        def newch(name):
            cid[name] = len(chans); chans.append(name); return cid[name]
        seg = {}
        for rep in sorted(members):
            nl = sum(links.get(c, 0) for c in members[rep])
            seg[rep] = [newch(f"g{rep}.{k}") for k in range(nl + 1)]
        def first(c): return seg[src_of[c]][0]
        def last(c): return seg[src_of[c]][-1]
        desc, ops, oms, dflt = {}, [], [], {}
        for l, r in enumerate(rules):
            k = r[0]
            if l in zd: continue
            if k == "fork":
                i, os_ = r[1], r[2]
                if hch[src_of[i]] in ghost:
                    ops.append(("forkG", last(i), [first(o) for o in os_]))
                else:
                    ops.append(("forkH", last(i), [(first(o), hch[src_of[o]]) for o in os_], l, i, os_))
            elif k == "comp":
                ins, o, e = r[1], r[2], r[3]
                cins, js = [], []
                for p, mch in enumerate(ins):
                    cins.append(last(mch))
                    pl = prod_rule.get(mch, [None])[0]
                    if pl in zd and zd[pl] == "trunci":
                        js.append(("fold", pl, p, rules[pl][1][0], rules[pl][3]))
                    elif pl in zd and zd[pl] == "constant":
                        js.append(("const", pl, rules[pl][1][0], rules[pl][3]))
                    else:
                        assert hch[src_of[mch]] == mch, (l, mch)
                        js.append(("direct", p))
                ops.append(("join", cins, first(o), e, js, l, ins, o))
            elif k == "branch":
                c, d, t, f = r[1], r[2], r[3], r[4]
                j = newch(f"j{l}")
                cin, din = last(c), last(d)
                assert c not in ghost
                pld = prod_rule.get(d, [None])[0]
                if d in ghost and not (pld in zd and zd[pld] == "constant"):
                    ops.append(("bjoin", [cin, din], j, ("var", 0), ("lit", 0), None))
                    ops.append(("steerC", j, first(t), first(f)))
                else:
                    jc = ("direct", 0)
                    jd = ("const", pld, rules[pld][1][0], rules[pld][3]) if (pld in zd and zd[pld] == "constant") \
                        else ("direct", 1)
                    ops.append(("bjoin", [cin, din], j, jc, jd, (l, c, d)))
                    ft = [fold_prod.get(cc) for cc in (sinkch(src_of[t]), sinkch(src_of[f]))]
                    if ft[0] is None:
                        assert ft[1] is None
                        fold = None; fd = ("var", 0)
                    else:
                        assert ft[1] is not None and rules[ft[0][0]][3] == rules[ft[1][0]][3]
                        fold = (ft[0][0], ft[1][0], hch[src_of[t]], hch[src_of[f]]); fd = rules[ft[0][0]][3]
                    ops.append(("steerD", j, first(t), first(f), fd, l, c, d, t, f, jc, jd, fold))
            elif k == "mux":
                s, ds, o, iw = r[1], r[2], r[3], r[4]
                if len(ds) == 2:
                    ops.append(("mux", last(s), last(ds[0]), last(ds[1]), first(o), l, s, ds, o))
                else:
                    assert len(ds) == 3, ("mux width", l)
                    ops.append(("muxn", last(s), [last(x) for x in ds], first(o), l, s, ds, o))
            elif k == "sink":
                ops.append(("sink", last(r[1])))
        for res, ins in cms.items():
            ins = sorted(ins)
            idx = ins[0][3]
            if len(ins) == 1:
                ops.append(("forkG", last(ins[0][1]), [first(res), first(idx)]))
            elif len(ins) == 2:
                z = newch(f"z{res}")
                w = len(oms); oms.append(("lab2", idx))
                ops.append(("amerge", last(ins[0][1]), last(ins[1][1]), z, w))
                desc[z] = ("cmz", last(ins[0][1]), last(ins[1][1]), w)
                ops.append(("forkG", z, [first(res), first(idx)]))
            else:
                assert len(ins) == 3, ("control_merge width", res)
                acc = newch(f"acc{res}"); z = newch(f"z{res}")
                w1 = len(oms); oms.append(("lo3", idx)); w2 = len(oms); oms.append(("hi3", idx))
                ops.append(("amerge", last(ins[0][1]), last(ins[1][1]), acc, w1))
                ops.append(("amerge", acc, last(ins[2][1]), z, w2))
                desc[acc] = ("cmz", last(ins[0][1]), last(ins[1][1]), w1)
                desc[z] = ("cmz", acc, last(ins[2][1]), w2)
                ops.append(("forkG", z, [first(res), first(idx)]))
        # environment (generic: argument k -> source `which = k`; out and end -> sinks)
        for k_, c in enumerate(self.ports_in):
            ops.append(("src", first(c), k_))
        ops.append(("sink", last(self.chEnd))); ops.append(("sink", last(self.chOut)))
        for rep in sorted(members):
            sg = seg[rep]
            for a, b in zip(sg, sg[1:]):
                ops.append(("link", a, b))
        prod_op, cons_op = {}, {}
        def op_ins(o):
            k = o[0]
            return {"forkG": lambda: [o[1]], "forkH": lambda: [o[1]], "join": lambda: o[1], "bjoin": lambda: o[1],
                    "steerC": lambda: [o[1]], "steerD": lambda: [o[1]], "mux": lambda: [o[1], o[2], o[3]],
                    "muxn": lambda: [o[1]] + o[2], "amerge": lambda: [o[1], o[2]], "link": lambda: [o[1]],
                    "src": lambda: [], "sink": lambda: [o[1]]}[k]()
        def op_outs(o):
            k = o[0]
            return {"forkG": lambda: o[2], "forkH": lambda: [p[0] for p in o[2]], "join": lambda: [o[2]],
                    "bjoin": lambda: [o[2]], "steerC": lambda: [o[2], o[3]], "steerD": lambda: [o[2], o[3]],
                    "mux": lambda: [o[4]], "muxn": lambda: [o[3]], "amerge": lambda: [o[3]],
                    "link": lambda: [o[2]], "src": lambda: [o[1]], "sink": lambda: []}[k]()
        for n_, o in enumerate(ops):
            for c in op_ins(o):
                assert c not in cons_op, ("two consumers", c, chans[c]); cons_op[c] = n_
            for c in op_outs(o):
                assert c not in prod_op, ("two producers", c, chans[c]); prod_op[c] = n_
        for c in range(len(chans)):
            assert c in prod_op and c in cons_op, ("dangling", c, chans[c])
        def jsig(j):
            if j[0] == "direct": return ("var", j[1])
            if j[0] == "fold": return subst([("var", j[2])], j[4])
            return j[3]
        sys.setrecursionlimit(100000)
        def d_of(c, stack=()):
            if c in dflt: return dflt[c]
            assert c not in stack, ("default cycle", [chans[x] for x in stack])
            o = ops[prod_op[c]]; k = o[0]; st = stack + (c,)
            if k == "link": v = d_of(o[1], st)
            elif k == "forkH": v = d_of(o[1], st)
            elif k == "join":
                vals = [jdef(j, o[1], st) for j in o[4]]
                v = ev(o[3], vals)
            elif k == "steerD":
                bj = ops[prod_op[o[1]]]
                cd = jdef(bj[3], bj[1], st); dd_ = jdef(bj[4], bj[1], st)
                b0 = cd % 2 == 1
                v = ev(o[4], [dd_]) if (c == o[2]) == b0 else 0
            elif k == "mux": v = d_of(o[2], st)
            elif k == "muxn": v = d_of(o[2][0], st)
            elif k == "src": v = 0
            else: raise SystemExit(("no default", k, chans[c]))
            dflt[c] = v
            return v
        def jdef(j, cins, st):
            if j[0] == "direct": return d_of(cins[j[1]], st)
            if j[0] == "fold": return ev(j[4], [d_of(cins[j[2]], st)])
            return ev(j[3], [])
        for c in range(len(chans)):
            if c in desc: continue
            o = ops[prod_op[c]]; k = o[0]
            if k == "link":
                pass
            elif k in ("forkH", "join", "steerD", "mux", "muxn") or (k == "src" and o[2] in (0, 1)):
                rep = int(chans[c][1:].split(".")[0])
                desc[c] = ("hist", hch[rep])
            elif k == "forkG": desc[c] = ("copy", o[1])
            elif k == "steerC": desc[c] = ("zero",)
            elif k == "src": desc[c] = ("zero",)
            elif k == "bjoin":
                desc[c] = ("bj", jsig(o[3]) if isinstance(o[3], tuple) and o[3][0] in ("direct", "fold", "const") else o[3],
                           jsig(o[4]) if isinstance(o[4], tuple) and o[4][0] in ("direct", "fold", "const") else o[4], o[1])
            else: raise SystemExit(("no desc", k, chans[c]))
        for rep in sorted(members):
            sg = seg[rep]
            for a, b in zip(sg, sg[1:]):
                desc[b] = desc[a] if desc[a][0] == "hist" else ("copy", a)
        for c in range(len(chans)):
            if desc[c][0] == "hist": d_of(c)
        rank = {}
        def deps(dsc):
            if dsc[0] == "copy": return [dsc[1]]
            if dsc[0] == "cmz": return [dsc[1], dsc[2]]
            if dsc[0] == "bj": return list(dsc[3])
            return []
        def rk(c, stack=()):
            if c in rank: return rank[c]
            assert c not in stack, "descriptor cycle"
            ds = deps(desc[c])
            rank[c] = 0 if not ds else 1 + max(rk(x, stack + (c,)) for x in ds)
            return rank[c]
        for c in range(len(chans)): rk(c)
        self.__dict__.update(chans=chans, ops=ops, oms=oms, desc=desc, dflt=dflt, rank=rank, prod_op=prod_op,
                             cons_op=cons_op, zd=zd, jsig=jsig, first=first, last=last, seg=seg, src_of=src_of,
                             prod_rule=prod_rule, L=L_)
        self.NF = max(rank.values()) + 3
        self.out0 = last(self.chOut)
        self.start = first(self.ports_in[2])

    def dd(self, c): return self.dflt.get(c, 0)

    def chase(self, c, f=32):
        while f > 0 and self.desc[c][0] == "copy": c = self.desc[c][1]; f -= 1
        return c

    def lean(self, P):
        L, dd, desc, ops, oms, rules, chans = self.L, self.dd, self.desc, self.ops, self.oms, self.rules, self.chans
        jsig, prod_op, prod_rule = self.jsig, self.prod_op, self.prod_rule
        def LJ(j, cins):
            if j[0] == "direct": return f"(.direct {j[1]} {dd(cins[j[1]])})"
            if j[0] == "fold": return f"(.fold {j[1]} {j[2]} {j[3]} {dd(cins[j[2]])} {L(j[4])})"
            return f"(.const {j[1]} {j[2]} {L(j[3])})"
        def LD(c):
            x = desc[c]
            if x[0] == "hist": return f".hist {x[1]} {dd(c)}"
            if x[0] == "copy": return f".copy {x[1]}"
            if x[0] == "zero": return ".zero"
            if x[0] == "cmz": return f".cmz {x[1]} {x[2]} {x[3]}"
            return f".bj {L(x[1])} {L(x[2])} [{', '.join(map(str, x[3]))}]"
        def lst(xs): return "[" + ", ".join(map(str, xs)) + "]"
        def LK(o):
            k = o[0]
            if k == "forkG": return f"K.forkG {o[1]} {lst(o[2])}"
            if k == "forkH":
                pairs = ", ".join(f"({a}, {b})" for a, b in o[2])
                return f"K.forkH {o[1]} [{pairs}] {o[3]} {o[4]} {dd(o[1])} {lst(o[5])}"
            if k == "join":
                _, cins, co, e, js, l, gins, go = o
                return (f"K.join {lst(cins)} {co} {L(e)} [{', '.join(LJ(j, cins) for j in js)}] "
                        f"⟨{l}, {lst(gins)}, {go}, {dd(co)}⟩")
            if k == "bjoin":
                _, cins, j, jc, jd, _x = o
                ec = jsig(jc) if jc[0] in ("direct", "fold", "const") else jc
                ed = jsig(jd) if jd[0] in ("direct", "fold", "const") else jd
                return f"K.bjoin {lst(cins)} {j} {L(ec)} {L(ed)}"
            if k == "steerC": return f"K.steerC {o[1]} {o[2]} {o[3]}"
            if k == "steerD":
                _, j, t, f, fd, l, gc, gd, gt, gf, jc, jd, fold = o
                bj = ops[prod_op[j]]; jins = bj[1]
                fl = "none" if fold is None else f"(some ({fold[0]}, {fold[1]}, {fold[2]}, {fold[3]}))"
                return (f"K.steerD {j} {t} {f} {L(fd)} ⟨{l}, {gc}, {gd}, {gt}, {gf}, {LJ(jc, jins)}, {LJ(jd, jins)}, "
                        f"{lst(jins)}, {fl}, {dd(t)}, {dd(f)}⟩")
            if k == "mux":
                _, c, x, y, z, l, gs, ds, go = o
                zc = self.chase(c); _, xa, ya, w = desc[zc]; gi = oms[w][1]
                lf = 0; hs = []
                if gs != gi:
                    lf = prod_rule[gs][0]; hs = rules[lf][2]; assert rules[lf][0] == "fork" and rules[lf][1] == gi
                return (f"K.mux {c} {x} {y} {z} ⟨{l}, {gs}, {ds[0]}, {ds[1]}, {go}, {dd(x)}, {dd(y)}, {dd(z)}, "
                        f"{zc}, {xa}, {ya}, {w}, {gi}, {lf}, {lst(hs)}⟩")
            if k == "muxn":
                _, c, xs, z, l, gs, ds, go = o
                zc = self.chase(c); _, acc, in2, w2 = desc[zc]; _, in0, in1, w1 = desc[acc]
                return (f"K.muxn {c} {xs[0]} {xs[1]} {xs[2]} {z} ⟨{l}, {gs}, {ds[0]}, {ds[1]}, {ds[2]}, {go}, "
                        f"{dd(xs[0])}, {dd(xs[1])}, {dd(xs[2])}, {dd(z)}, {zc}, {acc}, {in2}, {in0}, {in1}, {w2}, {w1}⟩")
            if k == "amerge": return f"K.amerge {o[1]} {o[2]} {o[3]} {o[4]}"
            if k == "link": return f"K.link {o[1]} {o[2]}"
            if k == "src": return f"K.src {o[1]} {o[2]} {dd(o[1])}"
            if k == "sink": return f"K.sink {o[1]}"
            raise ValueError(k)
        NC, NO = len(chans), len(ops)
        out0 = self.out0
        cnt = {}
        for o in ops: cnt[o[0]] = cnt.get(o[0], 0) + 1
        self.counts = cnt
        out = []
        w = out.append
        w(f"import {P['nimport']}\n")
        w(f"/-!\n# GENERATED by {P['ngen']} -- DO NOT EDIT\n")
        w(f"The concrete circuit network of {P['label']}: bdc's {P['label']} graph (C-8i importer, bdc's fusion plan)")
        w(f"with bdc's link placement (C-8l `links`): {NC} channels, {NO} operators")
        w("(" + ", ".join(f"{k} {v}" for k, v in sorted(cnt.items())) + ").")
        w(f"Zero-delay comps folded (no operator): {', '.join(rules[l][4] for l in sorted(self.zd))}.")
        w(f"out0 = circuit channel {out0} (`{chans[out0]}`).\n")
        w(f"Channel names: `gR.k` = segment k of the group whose source {P['G']} channel is R (k = number of")
        w("bd_link stages upstream), `jL` = branch rule L's joined (cond, data) channel, `zR`/`accR` =")
        w("the arbiter outputs of the control_merge whose result channel is R.\n-/\n")
        w(f"namespace {P['nns']}\nopen {P['nopen']}\n")
        w("set_option maxRecDepth 100000\n")
        w(f"abbrev NC : Nat := {NC}\nabbrev NO : Nat := {NO}\n")
        w("instance : NeZero NC := ⟨by decide⟩\ninstance : NeZero NO := ⟨by decide⟩\n")
        w("def chanNames : List String := [" + ", ".join(f'"{c}"' for c in chans) + "]\n")
        w("def tab : Tab where")
        w("  desc := [" + ", ".join(LD(c) for c in range(NC)) + "]")
        w("  om := [" + ", ".join(f".{a} {b}" for a, b in oms) + "]")
        w("  rank := " + lst([self.rank[c] for c in range(NC)]))
        w(f"  nf := {self.NF}\n")
        w("def ops : List (K NC) := [")
        w(",\n".join("  " + LK(o) for o in ops))
        w("]\n")
        w("def prodT : List (Fin NO) := " + lst([prod_op[c] for c in range(NC)]))
        w("def consT : List (Fin NO) := " + lst([self.cons_op[c] for c in range(NC)]) + "\n")
        w(f"def out0 : Fin NC := {out0}\n")
        w(f"end {P['nns']}")
        return "\n".join(out) + "\n"

    def spine(self):
        """spinegen.py: segments of spine channels, branch-joined channels whose data input is on
        the spine, arbiter outputs. Not trusted (the Lean side checks SpOK over all operators)."""
        spine = set(self.g.spine)
        bj = {}
        for o in self.ops:
            if o[0] == "bjoin": bj[o[2]] = o[1][1]
        sp = [False] * len(self.chans)
        for c, n in enumerate(self.chans):
            m = re.fullmatch(r"g(\d+)\.\d+", n)
            if m and int(m.group(1)) in spine: sp[c] = True
            if n.startswith("z") or n.startswith("acc"): sp[c] = True
        for c, n in enumerate(self.chans):
            if n.startswith("j") and sp[bj[c]]: sp[c] = True
        return sp


def _walktab(self):
    """C-8s's walkgen.py (H_WALK proof tables), generalised: for every circuit spine channel its
    token-graph group, position, adjacency, count list and consuming rule. The 3-input
    cascade's stage-1 output `accR` (gcd only) is the one channel that is not `adj` and counts
    its two inputs. Not trusted: <Prefix>WalkTab checks everything by kernel evaluation."""
    names, ops, sp = self.chans, self.ops, self.spine()
    NC = len(names)
    cons = {}
    for n_, o in enumerate(ops):
        k = o[0]
        ins = {"forkG": lambda: [o[1]], "forkH": lambda: [o[1]], "join": lambda: o[1], "bjoin": lambda: o[1],
               "steerC": lambda: [o[1]], "steerD": lambda: [o[1]], "mux": lambda: [o[1], o[2], o[3]],
               "muxn": lambda: [o[1]] + o[2], "amerge": lambda: [o[1], o[2]], "link": lambda: [o[1]],
               "src": lambda: [], "sink": lambda: [o[1]]}[k]()
        for c in ins: cons[c] = o
    bjin = {o[2]: (o[1][0], o[1][1]) for o in ops if o[0] == "bjoin"}
    spC = [c for c in range(NC) if sp[c]]
    grp = [0] * NC
    for c in spC:
        m = re.fullmatch(r"g(\d+)\.\d+", names[c]) or re.fullmatch(r"z(\d+)", names[c]) or re.fullmatch(r"acc(\d+)", names[c])
        if m: grp[c] = int(m.group(1))
    for c in spC:
        if names[c].startswith("j"): grp[c] = grp[bjin[c][1]]
    adj = [True] * NC
    al = [[grp[c]] for c in range(NC)]
    accs = [c for c in spC if names[c].startswith("acc")]
    self.acc_info = []
    for ACC in accs:
        st1 = [o for o in ops if o[0] == "amerge" and o[3] == ACC][0]
        r1 = [r for r in self.rules if r[0] == "cm" and r[2] == grp[ACC]]
        ins01 = [grp[st1[1]], grp[st1[2]]]
        adj[ACC] = False; al[ACC] = ins01
        self.acc_info.append((ACC, ins01))
    def succs(c):
        o = cons[c]
        if o[0] in ("link",): return [o[2]]
        if o[0] == "bjoin": return [o[2]]
        if o[0] == "forkG": return [x for x in o[2] if sp[x]][:1]
        if o[0] == "steerC": return [o[2], o[3]]
        if o[0] == "amerge": return [o[3]]
        if o[0] == "sink": return [None]
        raise ValueError(names[c], o)
    rho = [0] * NC
    for _ in range(20):
        for c in spC:
            for o in succs(c):
                if o is not None and grp[o] == grp[c]:
                    rho[o] = max(rho[o], rho[c] + 1)
    gcons = {}
    for i, r in enumerate(self.rules):
        for ch in mlir2lean.Graph.rule_ins(r): gcons[ch] = i
    lc = [gcons.get(grp[c], 0) if sp[c] else 0 for c in range(NC)]
    def B(cur, c):
        if cur is None: return 0
        return 1 if (adj[c] and grp[c] == grp[cur] and rho[c] <= rho[cur]) else 0
    bad = 0
    for c in spC:
        for o in succs(c):
            stay = o is not None and grp[o] == grp[c]
            dg = None if stay else grp[c]
            for d in spC:
                if B(c, d) + (1 if o == d else 0) != (al[d].count(dg) if dg is not None else 0) + B(o, d):
                    bad += 1; print("transOK fails", names[c], "->", o, "at", names[d], file=sys.stderr); break
    st = self.start
    init_ok = all(B(st, d) == (1 if d == st else 0) for d in spC)
    print(f"-- {len(spC)} spine channels; transitions bad={bad}; init_ok={init_ok}", file=sys.stderr)
    if bad or not init_ok: raise SystemExit("walktab: self-check failed")
    L = lambda xs: "[" + ", ".join(xs) + "]"
    out = [f"def spN : List Nat := {L(str(c) for c in spC)}",
           f"def grpL : List Nat := {L(str(x) for x in grp)}",
           f"def rhoL : List Nat := {L(str(x) for x in rho)}",
           f"def adjL : List Bool := {L('true' if x else 'false' for x in adj)}",
           f"def alL : List (List Nat) := {L(L(str(y) for y in x) for x in al)}",
           f"def lcL : List Nat := {L(str(x) for x in lc)}",
           "def recs : List (Nat × Nat × Nat × Bool × List Nat) := " +
           L('(%d, %d, %d, %s, %s)' % (c, grp[c], rho[c], 'true' if adj[c] else 'false', L(str(y) for y in al[c])) for c in spC)]
    return "\n\n".join(out) + "\n"


Net.walktab = _walktab


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kernel", required=True, choices=sorted(PROFILES))
    ap.add_argument("--gcd-compat", action="store_true", help="(gcd only) reproduce the 8l/8m/8r outputs")
    ap.add_argument("what", choices=["links", "ring", "net", "spine", "walktab", "summary"])
    ap.add_argument("-o", "--out", default=None)
    a = ap.parse_args()
    P = PROFILES[a.kernel]
    g = mlir2lean.Graph(kernel_mlir(P["mlir"]))
    if a.what == "links":
        text, info = gen_links(g, P)
    elif a.what == "ring":
        _, info = gen_links(g, P)
        text = gen_ring(info, P, P["pre"])
    else:
        net = Net(g)
        if a.what == "net":
            text = net.lean(P)
            print(f"{len(net.chans)} channels, {len(net.ops)} operators, {net.counts}", file=sys.stderr)
        elif a.what == "walktab":
            text = net.walktab()
        elif a.what == "spine":
            sp = net.spine()
            print(f"-- {sum(sp)} spine channels of {len(sp)}", file=sys.stderr)
            text = "[" + ", ".join("true" if b else "false" for b in sp) + "]\n"
            if not a.gcd_compat:
                text = f"spL {text}start {net.start}\nout0 {net.out0}\nout0d {net.dd(net.out0)}\nchOut {net.chOut}\nchEnd {net.chEnd}\n"
        else:
            net.lean(P)
            text = (f"kernel {a.kernel}: {g.N} token channels, {len(net.rules)} rules; circuit {len(net.chans)} "
                    f"channels, {len(net.ops)} operators {net.counts}; out0 {net.out0} start {net.start} "
                    f"chOut {net.chOut} chEnd {net.chEnd}; links {len(net.links)} channels, "
                    f"{sum(net.links.values())} stages\n")
    if a.out:
        open(a.out, "w").write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
