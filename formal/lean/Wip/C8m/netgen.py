#!/usr/bin/env python3
"""Generate formal/lean/Formal/Net/CapstoneNet.lean: the concrete circuit network of gcd_hw.

Input (read-only): bdc's gcd_hw graph through C-8i's importer (formal/tools/dfimport/mlir2lean.py,
which runs bdc's own parser and fusion plan) and bdc's link placement as exported by C-8l
(`links` in formal/lean/Formal/Net/CapstoneLinks.lean, produced by Wip/C8l/linkexport.py).

Circuit structure per GcdHw rule (bdc/emit.py):
* fork            -> bd_fork                      (K.forkG / K.forkH)
* comp            -> bd_join + compute + delay    (K.join)
* comp, zero delay (constantN, trunciN, extuiN: `_op_constant`, `_reshape`) -> NO operator:
  the output channel is the input's handshake. trunci/constant fold into the consumer
  (J.fold / J.const); extui (the outputs of cond_br17) fold into the producing steer's f.
* branch          -> bd_join(cond, data) + bd_steer (K.bjoin + K.steerD / K.steerC)
* mux (2 inputs)  -> bd_mux (K.mux); mux (3 inputs) -> bdc_muxn3 (K.muxn)
* control_merge, 1 input  -> bd_fork(N=2) (K.forkG)
* control_merge, 2 inputs -> bdc_amerge2 + bd_fork(N=2) (K.amerge + K.forkG)
* control_merge, 3 inputs -> bdc_amerge3 = two arbiter stages (8l amerge3_cascade) + bd_fork
* sink -> bd_snk (K.sink); every link stage -> bd_link (K.link)
* environment: bd_src-like sources for a, b, start (K.src); sinks for out0, end.
H_SOURCE_ETERNAL chains (source -> fork -> constant into a join) are not modelled: dropping a
join input weakens the Join gate model, so the real join satisfies the model without it.

Also emits the stream-solution descriptors, oracles, ranks and defaults (see CapstoneNetDef).
"""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "dfimport"))
for k in ["BDC_OP_FUSION", "BDC_CONST_FOLD", "BDC_FORK_FUSION", "BDC_MAX_FUSE_NODES", "BDC_PROBE",
          "BDC_RING_PAD", "BDC_LINK_FASTFALL", "BDC_SELECT_PAD"]:
    os.environ.pop(k, None)
import mlir2lean  # noqa: E402

g = mlir2lean.Graph(mlir2lean.default_mlir())
rules = list(g.rules)
NG = g.N
links_txt = open(os.path.join(ROOT, "formal", "lean", "Formal", "Net", "CapstoneLinks.lean")).read()
m = re.search(r"def links : List \(Nat × Nat\) := \[(.*?)\]\n", links_txt)
links = {int(a): int(b) for a, b in re.findall(r"\((\d+), (\d+)\)", m.group(1))}

# ---------------------------------------------------------------- expression semantics
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
def subst(sig, e): return mlir2lean.e_subst(sig, e)
L = mlir2lean.e_lean

# ---------------------------------------------------------------- classes
ctl = {c for c, v in enumerate(g.chname) if g.is_ctl(v)}
prod_rule, cons_rule = {}, {}
for l, r in enumerate(rules):
    k = r[0]
    ins = mlir2lean.Graph.rule_ins(r)
    outs = {"fork": lambda: list(r[2]), "comp": lambda: [r[2]], "branch": lambda: [r[3], r[4]],
            "mux": lambda: [r[3]], "cm": lambda: [r[2], r[3]], "sink": lambda: []}[k]()
    for c in ins: cons_rule[c] = l
    for c in outs: prod_rule.setdefault(c, []).append(l)
zd = {}   # zero-delay comp rule -> kind
for l, r in enumerate(rules):
    if r[0] == "comp":
        nm = r[4]
        for kind in ("constant", "trunci", "extui"):
            if re.fullmatch(kind + r"\d+", nm): zd[l] = kind
cms = {}  # res -> list of (k, input, rule)
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

# ---------------------------------------------------------------- groups (zero-delay aliasing)
src_of = {c: c for c in range(NG)}    # group representative: the SOURCE channel of the group
hch = {}                               # group rep -> GcdHw channel whose history it carries
members = {c: [c] for c in range(NG)}
fold_prod = {}                         # extui output -> (rule, input)
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

# ---------------------------------------------------------------- circuit channels
chans = []          # names
cid = {}
def newch(name):
    cid[name] = len(chans); chans.append(name); return cid[name]
seg = {}
for rep in sorted(members):
    nl = sum(links.get(c, 0) for c in members[rep])
    seg[rep] = [newch(f"g{rep}.{k}") for k in range(nl + 1)]
def first(c): return seg[src_of[c]][0]
def last(c): return seg[src_of[c]][-1]
desc = {}
ops = []
oms = []
isH = lambda rep: hch[rep] not in ghost

dflt = {}  # circuit channel -> default (H-class)

# operator records: (kind, fields) -> lean text later
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
        acc = newch(f"acc{res}"); z = newch(f"z{res}")
        w1 = len(oms); oms.append(("lo3", idx)); w2 = len(oms); oms.append(("hi3", idx))
        ops.append(("amerge", last(ins[0][1]), last(ins[1][1]), acc, w1))
        ops.append(("amerge", acc, last(ins[2][1]), z, w2))
        desc[acc] = ("cmz", last(ins[0][1]), last(ins[1][1]), w1)
        desc[z] = ("cmz", acc, last(ins[2][1]), w2)
        ops.append(("forkG", z, [first(res), first(idx)]))
# environment
ops.append(("src", first(0), 0)); ops.append(("src", first(1), 1)); ops.append(("src", first(2), 2))
ops.append(("sink", last(3))); ops.append(("sink", last(250)))
# links
for rep in sorted(members):
    sg = seg[rep]
    for a, b in zip(sg, sg[1:]):
        ops.append(("link", a, b))

# ---------------------------------------------------------------- descriptors
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

# defaults: memoised on circuit channels
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
        cd = jdef(bj[3], bj[1], st); dd = jdef(bj[4], bj[1], st)
        b0 = cd % 2 == 1
        v = ev(o[4], [dd]) if (c == o[2]) == b0 else 0
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
        name = chans[c]
        rep = int(name[1:].split(".")[0])
        desc[c] = ("hist", hch[rep])
    elif k == "forkG": desc[c] = ("copy", o[1])
    elif k == "steerC": desc[c] = ("zero",)
    elif k == "src": desc[c] = ("zero",)
    elif k == "bjoin":
        desc[c] = ("bj", jsig(o[3]) if isinstance(o[3], tuple) and o[3][0] in ("direct", "fold", "const") else o[3],
                   jsig(o[4]) if isinstance(o[4], tuple) and o[4][0] in ("direct", "fold", "const") else o[4], o[1])
    else: raise SystemExit(("no desc", k, chans[c]))
# link segments, in order
for rep in sorted(members):
    sg = seg[rep]
    for a, b in zip(sg, sg[1:]):
        desc[b] = desc[a] if desc[a][0] == "hist" else ("copy", a)
for c in range(len(chans)):
    if desc[c][0] == "hist": d_of(c)
def dd(c): return dflt.get(c, 0)

# ranks
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
NF = max(rank.values()) + 3

def chase(c, f=32):
    while f > 0 and desc[c][0] == "copy": c = desc[c][1]; f -= 1
    return c

# ---------------------------------------------------------------- Lean output
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
def omega_of_cmz(zc):
    return desc[zc]
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
        zc = chase(c); _, xa, ya, w = desc[zc]; gi = oms[w][1]
        lf = 0; hs = []
        if gs != gi:
            lf = prod_rule[gs][0]; hs = rules[lf][2]; assert rules[lf][0] == "fork" and rules[lf][1] == gi
        return (f"K.mux {c} {x} {y} {z} ⟨{l}, {gs}, {ds[0]}, {ds[1]}, {go}, {dd(x)}, {dd(y)}, {dd(z)}, "
                f"{zc}, {xa}, {ya}, {w}, {gi}, {lf}, {lst(hs)}⟩")
    if k == "muxn":
        _, c, xs, z, l, gs, ds, go = o
        zc = chase(c); _, acc, in2, w2 = desc[zc]; _, in0, in1, w1 = desc[acc]
        return (f"K.muxn {c} {xs[0]} {xs[1]} {xs[2]} {z} ⟨{l}, {gs}, {ds[0]}, {ds[1]}, {ds[2]}, {go}, "
                f"{dd(xs[0])}, {dd(xs[1])}, {dd(xs[2])}, {dd(z)}, {zc}, {acc}, {in2}, {in0}, {in1}, {w2}, {w1}⟩")
    if k == "amerge": return f"K.amerge {o[1]} {o[2]} {o[3]} {o[4]}"
    if k == "link": return f"K.link {o[1]} {o[2]}"
    if k == "src": return f"K.src {o[1]} {o[2]} {dd(o[1])}"
    if k == "sink": return f"K.sink {o[1]}"
    raise ValueError(k)

NC, NO = len(chans), len(ops)
out0 = last(250)
out = []
w = out.append
w("import Formal.Net.CapstoneNetSound\n")
w("/-!\n# GENERATED by formal/lean/Wip/C8m/netgen.py -- DO NOT EDIT\n")
w("The concrete circuit network of gcd_hw: bdc's gcd_hw graph (C-8i importer, bdc's fusion plan)")
w(f"with bdc's link placement (C-8l `links`): {NC} channels, {NO} operators")
cnt = {}
for o in ops: cnt[o[0]] = cnt.get(o[0], 0) + 1
w("(" + ", ".join(f"{k} {v}" for k, v in sorted(cnt.items())) + ").")
w(f"Zero-delay comps folded (no operator): {', '.join(rules[l][4] for l in sorted(zd))}.")
w(f"out0 = circuit channel {out0} (`{chans[out0]}`).\n")
w("Channel names: `gR.k` = segment k of the group whose source GcdHw channel is R (k = number of")
w("bd_link stages upstream), `jL` = branch rule L's joined (cond, data) channel, `zR`/`accR` =")
w("the arbiter outputs of the control_merge whose result channel is R.\n-/\n")
w("namespace Formal.Net.CapNet.Gcd\nopen Formal.Net Formal.Net.CapNet Formal.Net.GcdHw\n")
w("set_option maxRecDepth 100000\n")
w(f"abbrev NC : Nat := {NC}\nabbrev NO : Nat := {NO}\n")
w("instance : NeZero NC := ⟨by decide⟩\ninstance : NeZero NO := ⟨by decide⟩\n")
w("def chanNames : List String := [" + ", ".join(f'"{c}"' for c in chans) + "]\n")
w("def tab : Tab where")
w("  desc := [" + ", ".join(LD(c) for c in range(NC)) + "]")
w("  om := [" + ", ".join(f".{a} {b}" for a, b in oms) + "]")
w("  rank := " + lst([rank[c] for c in range(NC)]))
w(f"  nf := {NF}\n")
w("def ops : List (K NC) := [")
w(",\n".join("  " + LK(o) for o in ops))
w("]\n")
w("def prodT : List (Fin NO) := " + lst([prod_op[c] for c in range(NC)]))
w("def consT : List (Fin NO) := " + lst([cons_op[c] for c in range(NC)]) + "\n")
w(f"def out0 : Fin NC := {out0}\n")
w("end Formal.Net.CapNet.Gcd")
dst = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "formal", "lean", "Formal", "Net", "CapstoneNet.lean")
open(dst, "w").write("\n".join(out) + "\n")
print(f"wrote {dst}: {NC} channels, {NO} operators, {cnt}", file=sys.stderr)
