#!/usr/bin/env python3
"""entrywalk.py MLIR -- research's token-floor walk view, plus one ENTERING-mode view per loop (prototype, shard C).

bdc/emit.py token_graph() models every loop iterating: it drops each loop's entry channels and counts a token on each back
edge. formal's exhaustive search (formal/tools/live/fixtures/live.py) found deadlocks (matrix, stencil_2d, default flow) whose
token-free walk runs through an inner loop's ENTRY channels while it is re-entered (FOR-RESEARCH C55). This tool rebuilds
token_graph from research's own source with one change per header basic block B: for the loop headers in B (muxes / merges /
control_merges fed by a back edge), the entry inputs are walked and carry the token, the back-edge inputs are dropped. Every
other loop is as in research's view. Prints, per view, the shortest walk found (or none). Exit 1 if any view is short.
Untrusted prototype: the claim is only what it prints, checked against live.py's exhaustive verdicts.
Env: LIVE_BDC_DIR (research's bdc/, default /home/user/rs/bdc); BDC_* as for emit.py.
"""
import inspect, os, sys
BDC = os.environ.get("LIVE_BDC_DIR", "/home/user/rs/bdc")
sys.path.insert(0, BDC)
sys.dont_write_bytecode = True
import emit  # noqa: E402
from hs import parse  # noqa: E402

PATCH = '''    if FIXMUX[0]:
        # a mux data input k >= 1 is a back edge iff the control_merge whose index drives the select (through forks /
        # pass-throughs) has a back edge at input k - 1; research's rule reads it off basic-block numbers instead
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
        headers = {c for (_r, _i, c, _k, t) in every if t}
        skip = set()
        cont = collections.defaultdict(set)
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
        for i, node in enumerate(nodes):
            if node.op != "cond_br":
                continue
            d = cont.get(root(node.operands[0]))
            if d is None or len(d) != 1:
                continue
            other = node.results[1 - next(iter(d))]
            for (c2, k2) in func.consumers.get(other, []):
                skip.add((other, c2, k2))
    if ENTER[0] is not None:
        _ne = []
        for (r, i, c, k, t) in every:
            cn = nodes[c]
            if c in headers and _bb(cn) == ENTER[0] and ((cn.op == "mux" and k >= 1) or cn.op in ("merge", "control_merge")):
                if t:
                    skip.add((r, c, k))
                else:
                    skip.discard((r, c, k))
                    t = 1
            _ne.append((r, i, c, k, t))
        every = _ne
    chans, ins, outs = [], collections.defaultdict(list), collections.defaultdict(list)
'''

def build():
    src = inspect.getsource(emit.token_graph)
    anchor = "    chans, ins, outs = [], collections.defaultdict(list), collections.defaultdict(list)\n"
    assert src.count(anchor) == 1, "token_graph changed: patch anchor not found"
    src = src.replace(anchor, PATCH).replace("def token_graph(", "def token_graph_enter(")
    ns = dict(vars(emit))
    ns["ENTER"] = [None]
    ns["FIXMUX"] = [False]
    ns["FIXED"] = []
    exec(compile(src, "token_graph_enter", "exec"), ns)
    return ns

def main():
    path = sys.argv[1]
    func = [f for f in parse.parse_module(open(path).read(), filename=path) if not f.is_declaration][0]
    e = emit.Emitter(func)
    ns = build()
    tg = ns["token_graph_enter"]
    nodes = func.nodes
    hdr_bbs = sorted({emit._bb(n) for n in nodes if n.op in ("mux", "merge", "control_merge")})
    short = False
    if os.environ.get("FIXMUX"):
        ns["FIXMUX"][0] = True
        views = [None]
    else:
        views = [None] + hdr_bbs
    name = os.path.basename(os.path.dirname(os.path.dirname(path)))
    for B in views:
        ns["ENTER"][0] = B
        chans, out = tg(func, e.linked, e.depth, e.mem_absorbed)
        w = emit.short_walk(chans, out)
        tag = "iterating" if B is None else f"enter bb{B}"
        if w is None:
            print(f"{name}: view {tag}: every walk holds a token ({len(chans)} channels)")
        else:
            short = True
            cnt, cyc = w
            desc = []
            for s in cyc:
                r, p, c, k, st, tok = chans[s // 2]
                desc.append(("+" if s % 2 == 0 else "-") + f"{emit.vname(r)}[{st}st,{tok}t]")
            print(f"{name}: view {tag}: SHORT walk, count {cnt}: " + " ".join(desc))
    for f in ns["FIXED"]:
        print(f"{name}: reclassified mux input {f[0]} -> {f[1]} operand {f[2]}: tok {f[3]} -> {f[4]}")
    sys.exit(1 if short else 0)

if __name__ == "__main__":
    main()
