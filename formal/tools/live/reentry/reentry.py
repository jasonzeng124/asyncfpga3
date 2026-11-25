#!/usr/bin/env python3
"""reentry.py MLIR -- research's token-floor walk view, plus one PASS-THROUGH view per loop (prototype, shard C).

Why. bdc/emit.py token_graph() sees every loop iterating (or an inner loop skipped by its guard). formal's exhaustive
search (live.py, FOR-RESEARCH C55/C57) found deadlocks (matrix, stencil_2d, default flow) at the moment an inner loop L
has EXITED, the enclosing loop M took its back edge, and L is RE-ENTERED. At that deadlock the token-free cycle is a
fork-join pair:
    fork = L's header control_merge (its result and its index leave together),
    P    = index -> fork -> L's header mux select,
    Q    = result -> L's EXIT steer -> ... -> M's back edge -> M's header -> ... -> L's header mux ENTRY data input,
    join = that mux.
Q crosses one token (M's back edge) that P does not, so by research's condition 2 Q needs >= 2 stages between the fork
and the join; matrix / stencil_2d have 1 (the entry link n26 / n45; M's back edge and the exit path have none).

The view. For every loop L (header basic block B, headers = the muxes / merges / control_merges with a back edge in B):
  - L's back-edge inputs are dropped and its entry inputs are walked with no token (L entered),
  - the steers on L's condition walk their EXIT branch and drop their continue branch (L left in the same trip),
  - every other loop as in research's view (iterating, a token on each back edge; inner loops iterating or skipped).
That is research's "an inner loop passed through in one trip" mode, the one ringfloor.md lists as not covered.
Plus research's rule for mux back edges is replaced by C57's (a mux data input k >= 1 is a back edge iff the control_merge
driving its select has a back edge at input k - 1), which this view needs (it decides which mux inputs are L's entries).
Prints, per view, the shortest walk (or none). Exit 1 if any view is short (iterating or pass-through; with the floor on
the iterating view is clean on every fixture, so there the verdict is the pass-through views').
Untrusted prototype: checked only against live.py's exhaustive verdicts. Research's files are not modified: token_graph's
source is patched in memory.
Env: LIVE_BDC_DIR (research's bdc/, default /home/user/rs/bdc); BDC_* as for emit.py. REENTRY_FIXMUX=0: research's
bb rule for mux back edges.
"""
import inspect, io, contextlib, os, sys
BDC = os.environ.get("LIVE_BDC_DIR", "/home/user/rs/bdc")
sys.path.insert(0, BDC)
sys.dont_write_bytecode = True
import emit  # noqa: E402
from hs import parse  # noqa: E402

PATCH = '''    if FIXMUX[0]:
        cmtok = {}
        for (r, i, c, k, t) in every:
            if nodes[c].op == "control_merge":
                cmtok[(c, k)] = t
        def selroot(v):
            while v in producer and nodes[producer[v]].op in ("fork", "lazy_fork") + passthru and nodes[producer[v]].operands:
                v = nodes[producer[v]].operands[0]
            return producer.get(v)
        _ne = []
        for (r, i, c, k, t) in every:
            cn = nodes[c]
            if cn.op == "mux" and k >= 1:
                cm = selroot(cn.operands[0])
                if cm is not None and nodes[cm].op == "control_merge" and (cm, k - 1) in cmtok:
                    t2 = cmtok[(cm, k - 1)]
                    if t2 != t:
                        FIXED.append((vname(r), instname(cn, c), k, t, t2))
                    t = t2
            _ne.append((r, i, c, k, t))
        every = _ne
    # research's skip / cont, recomputed (identical code) on the possibly reclassified edges
    headers = {c for (_r, _i, c, _k, t) in every if t}
    skip = set()
    cont = collections.defaultdict(set)
    contbb = collections.defaultdict(set)         # header bb -> the roots of the conditions of its back edges
    for (r, i, c, k, t) in every:
        cn = nodes[c]
        if not t and c in headers and ((cn.op == "mux" and k >= 1) or cn.op in ("merge", "control_merge")):
            skip.add((r, c, k))
        if t:
            v, p = r, i
            while nodes[p].op in passthru and nodes[p].operands and nodes[p].operands[0] in producer:
                v = nodes[p].operands[0]
                p = producer[v]
            if nodes[p].op == "cond_br":
                cont[root(nodes[p].operands[0])].add(nodes[p].results.index(v))
                contbb[_bb(cn)].add(root(nodes[p].operands[0]))
    exits = {}                                    # condition root -> [(exit value, continue value)]
    for i, node in enumerate(nodes):
        if node.op != "cond_br":
            continue
        d = cont.get(root(node.operands[0]))
        if d is None or len(d) != 1:
            continue
        ci = next(iter(d))
        other = node.results[1 - ci]
        exits.setdefault(root(node.operands[0]), []).append((other, node.results[ci]))
        for (c2, k2) in func.consumers.get(other, []):
            skip.add((other, c2, k2))
    HDRBB[0] = sorted({_bb(nodes[c]) for c in headers})
    if PASS[0] is not None:
        B = PASS[0]
        mine = {c for c in headers if _bb(nodes[c]) == B}
        _ne = []
        for (r, i, c, k, t) in every:
            cn = nodes[c]
            if c in mine and ((cn.op == "mux" and k >= 1) or cn.op in ("merge", "control_merge")):
                if t:
                    skip.add((r, c, k))           # L's back edges: not taken
                else:
                    skip.discard((r, c, k))       # L's entries: taken, no token
            _ne.append((r, i, c, k, t))
        every = _ne
        for rt in contbb.get(B, ()):
            for (ex, co) in exits.get(rt, ()):
                for (c2, k2) in func.consumers.get(ex, []):
                    skip.discard((ex, c2, k2))    # L's exits: taken
                for (c2, k2) in func.consumers.get(co, []):
                    skip.add((co, c2, k2))        # L's continue branches: not taken
    chans, ins, outs = [], collections.defaultdict(list), collections.defaultdict(list)
'''


def build():
    src = inspect.getsource(emit.token_graph)
    anchor = "    chans, ins, outs = [], collections.defaultdict(list), collections.defaultdict(list)\n"
    assert src.count(anchor) == 1, "token_graph changed: patch anchor not found"
    src = src.replace(anchor, PATCH).replace("def token_graph(", "def token_graph_pass(")
    ns = dict(vars(emit))                         # after Emitter(): BDC_AUTO's per-function knobs are in place
    ns.update(PASS=[None], FIXMUX=[os.environ.get("REENTRY_FIXMUX", "1") != "0"], FIXED=[], HDRBB=[[]])
    exec(compile(src, "token_graph_pass", "exec"), ns)
    return ns


def describe(chans, w):
    cnt, cyc = w
    desc = []
    for s in cyc:
        r, p, c, k, st, tok = chans[s // 2]
        desc.append(("+" if s % 2 == 0 else "-") + f"{emit.vname(r)}[{st}st,{tok}t]")
    return cnt, " ".join(desc)


def check(path, quiet=False):
    func = [f for f in parse.parse_module(open(path).read(), filename=path) if not f.is_declaration][0]
    with contextlib.redirect_stdout(io.StringIO()):
        e = emit.Emitter(func)
    ns = build()
    tg = ns["token_graph_pass"]
    tg(func, e.linked, e.depth, e.mem_absorbed)   # fills HDRBB
    views = [None] + list(ns["HDRBB"][0])
    res = []
    for B in views:
        ns["PASS"][0] = B
        chans, out = tg(func, e.linked, e.depth, e.mem_absorbed)
        w = emit.short_walk(chans, out)
        res.append((B, len(chans), None if w is None else describe(chans, w)))
    return res, ns["FIXED"]


def main():
    path = sys.argv[1]
    name = os.path.basename(os.path.dirname(os.path.dirname(path)))
    res, fixed = check(path)
    flagged = False
    for B, n, w in res:
        tag = "iterating" if B is None else f"pass-through bb{B}"
        if w is None:
            print(f"{name}: view {tag}: every walk holds a token ({n} channels)")
        else:
            flagged = True
            print(f"{name}: view {tag}: SHORT walk, count {w[0]}: {w[1]}")
    for f in sorted(set(fixed)):
        print(f"{name}: reclassified mux input {f[0]} -> {f[1]} operand {f[2]}: tok {f[3]} -> {f[4]}")
    print(f"{name}: {'FLAGGED' if flagged else 'clean'}")
    sys.exit(1 if flagged else 0)


if __name__ == "__main__":
    main()
