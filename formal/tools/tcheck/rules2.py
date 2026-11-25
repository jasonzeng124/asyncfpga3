#!/usr/bin/env python3
"""Probe C-10g front end, part 2 (UNTRUSTED): rules A, E, F, J as race instances for
the proved checker `tcheck`.  Called from extract.py (`--rules2 AEFJ`), which owns the
graph, the per-variant arc intervals (`ivl`) and the all-paths segment builder.

Every instance is one 10a race: launch = node 0, `req` must be LATE (its earliest
change is used), every `data` node must be EARLY (its latest change is used),
PASS iff latest data <= earliest req in every run of the instance's netlist
(`Tcheck.verdict_sound`).  What follows says, per rule, which netlist is emitted and
which hand-argued hypothesis links it to the routed circuit.

A  (tighten.py rule A, `check` / `check_bundled`).  Per request site (`request_sites`)
   with tighten's own peers, cell boundary and confinement:
     common source:  one instance per start s that reaches both the request tail
       (fast-fall-side arcs dropped, as Timing.early) and a peer (all arcs, as
       Timing.late), all paths confined like tighten.walk.  label `A <cell> src=<s>`.
     bundled channel: one instance per cell.  A virtual launch V drives every start
       at [0,0] (H_BUNDLED_T0: every boundary net of the cell launches together; the
       assume-guarantee tighten's check_bundled docstring argues).  The data side is
       entered through a "lag" node that is the hull of the upstream links'
       controller -> latch-output segments (tighten's upstream_data_lag, per variant).
       label `A <cell> bundled`.
     C-10m: the packer's constant tie-off drivers ($PACKER_GND_DRV/$PACKER_VCC_DRV) are
     removed from the start set (they never switch: false path).  tighten keeps them, so
     a project rule-A row may differ from tcheck's for that reason alone (C-10n).
E  (skew.py rule E).  Per select gate and per launch skew.py would pick (cand[:4] plus
   the (3) C nodes; ported verbatim), the LEVEL-UNROLLED DAG: node (k, pin) = pin
   reached after exactly k storage crossings, crossings by any non-feedback input
   (skew.walk's seeding).  The request side uses the fast-fall-pruned arcs, the select
   side all arcs; each side is unrolled to the first level its pin is reached at
   (skew's `at`, the lap rule, kept as H_LEVEL: a protocol fact, 10b).
     E0  launch at the launch node, no credit.  Needs only H_LAUNCH at a storage node.
     E   launch at X, the deepest node that DOMINATES both pins in their DAGs: the
         exact shared prefix (10b's race_sound + H_CLEAN_EDGE at X).  skew.py credits
         t_c at the divergence of the two MEASURED paths, which need not dominate.
F  (tighten.py rule F, audit_fastfall).  Per FASTFALL line: launch = the fall of its
   input net src.  Data: every stage's fall, each stage bounded by its side tap alone
   (H_CONTROLLING: a 0 on either input of the AND forces the stage low, so its fall is
   no later than that input's fall plus the arc; the 10a hull over both inputs would
   take the later one).  The head has no side tap: src -> head input (all paths).
   Request: the next RISE of src = tail's earliest fall (fall arcs) + the shortest
   path tail -> src crossing anything (tighten's shortest_to), chosen per variant by
   Dijkstra on lower bounds (sdf, fast, slow), the chains merged (min over them).
J  (arb_fork.py rule J).  Per arbiter and client k:
     J0  launch at A0's driver, no shared credit (sound with no H_CLEAN_EDGE at all).
     Jx  launch at the BRANCH POINT of A0's route: the exact shared delay from the
         prjxray RC tree (Prjx.split; identical elements, Elmore terms equal), and in
         the sdf/sdfband columns the SDF number minus that same fraction.
     Jp  the project's pip-count estimate c in the sdf/sdfband columns only (it exists
         to show the algorithm reproduces arb_fork's numbers; prjxray columns = J0).
"""
import heapq
import math
import os
import re
from collections import defaultdict

KEEP_CONST = bool(os.environ.get("TCHECK_KEEP_CONST"))   # C-10m: before/after only
ZERO = None   # set in emit_all: {variant: (0, 0)}


def emit_all(c, which):
    global ZERO
    ZERO = {v: (0, 0) for v in c["VARIANTS"]}
    if "A" in which:
        rule_A(c)
    if "E" in which:
        rule_E(c)
    if "F" in which:
        rule_F(c)
    if "J" in which:
        rule_J(c)
    if "W" in which or "R" in which:
        import rules3                     # noqa: E402  (8e open width, RT_FB)
        rules3.emit_all(c, which, ZERO, _emit)


def _emit(c, I, L, meta):
    if I.req is None or not I.data:
        meta["skip"] = "no request or no data node"
        c["meta"].append(meta)
        return False
    I.emit(c["out"], L)
    meta["label"] = I.label
    c["meta"].append(meta)
    return True


# ------------------------------------------------------------------------- A

def rule_A(c):
    T, edges, back, stops, timing = c["T"], c["edges"], c["back"], c["stops"], c["timing"]
    seg, Inst, ff = c["segment"], c["Inst"], c["ff"]
    chains = T.find_chains(edges)
    sites = T.request_sites(edges, back, chains)
    for parent, head, tail, links in sites:
        downstream = T.reaches(edges, tail, stops)
        # tighten: {p output : head in reaches(edges, p, stops)}, by one backward walk
        up, work = {head}, [head]
        while work:
            x = work.pop()
            for s in back.get(x, ()):
                if s not in up:
                    up.add(s)
                    if s not in stops:
                        work.append(s)
        upstream = {p for p in up if T.is_output(p) and p in edges}
        own = set(links)
        peers = sorted({p for p in edges if T.is_output(p)
                        and T.pin_split(p)[0].startswith(parent + ".")
                        and T.pin_split(p)[0] not in own
                        and p not in downstream and p not in upstream})
        if not peers:
            c["meta"].append({"rule": "A", "ctl": parent, "skip": "no peers"})
            continue
        parent_srcs = T.cell_boundary(edges, back, stops, parent)
        upstream_links = T.upstream_bd_links(parent_srcs)
        region = (parent,) + upstream_links
        srcs = T.cell_boundary(edges, back, stops, region)
        # C-10m: FALSE PATH.  tighten.cell_boundary() keeps the packer's constant tie-off
        # drivers ($PACKER_GND_DRV / $PACKER_VCC_DRV) as boundary starts (C-10n finding).
        # A constant never switches, so no run of the circuit launches a transition from
        # it: a path that starts there is false, whether it would set the latest data
        # (the 3-5 ns tie-off routes C-10n saw) or the earliest request.  Under 10a's Run
        # semantics a node with no changing input never changes (H_QUIESCENT), so dropping
        # these starts is exactly the circuit's behaviour, not a weakening; the starts are
        # dropped BEFORE the common/bundled decision, so a constant can never be the
        # "common source" either.  TCHECK_KEEP_CONST=1 restores the old (project-equal)
        # start set, for before/after tables only.
        nconst = sum(1 for s in srcs if T.is_const(s))
        if not KEEP_CONST:
            srcs = {s for s in srcs if not T.is_const(s)}
        confine = region if upstream_links else parent
        prefixes = (confine,) if isinstance(confine, str) else confine

        def inside(pin, prefixes=prefixes):
            i = T.pin_split(pin)[0]
            return any(i == q or i.startswith(q + ".") for q in prefixes)
        res = T.check(timing, srcs, peers, tail, T.req_guard, confine=confine)
        if res is not None:
            n = 0
            for s in sorted(srcs):
                e_tab, l_tab = timing.early(s, confine), timing.late(s, confine)
                if tail not in e_tab or not any(p in l_tab for p in peers):
                    continue
                I = Inst(f"A {parent} src={s}")
                L = ("launch", s)
                rr = seg(I, "r", L, s, {tail}, ff, inside)
                rd = seg(I, "d", L, s, set(peers), set(), inside)
                if tail not in rr:
                    continue
                I.req = rr[tail]
                I.data = set(rd.values())
                n += _emit(c, I, L, {"rule": "A", "ctl": parent, "pairing": "common", "src": s,
                                     "const_dropped": 0 if KEEP_CONST else nconst})
            continue
        # bundled channel
        I = Inst(f"A {parent} bundled")
        V = ("launch", "V")
        for s in sorted(srcs):
            if tail not in timing.early(s, confine):
                continue
            I.add(V, ("rs", s), ZERO, False)
            rr = seg(I, ("r", s), ("rs", s), s, {tail}, ff, inside)
            if tail in rr:
                I.add(rr[tail], ("req",), ZERO, False)
                I.req = ("req",)
        lagkey = V
        for link in upstream_links:
            for lp in srcs:
                inst = T.pin_split(lp)[0]
                if not (inst.startswith(link + ".") and
                        T.RE_LATCH_STOP.match(inst.rsplit(link + ".", 1)[-1])):
                    continue
                ins = [p for p in edges if T.pin_split(p)[0] == inst and not T.is_output(p)]
                ctls = {s for p in ins for s in back.get(p, ())
                        if s in stops and T.pin_split(s)[0].startswith(link + ".")
                        and ".lat." not in T.pin_split(s)[0]}
                for ctl in ctls:
                    if lp not in timing.late(ctl, confine):
                        continue
                    I.add(V, ("lc", ctl), ZERO, False)
                    rl = seg(I, ("l", ctl), ("lc", ctl), ctl, {lp}, set(), inside)
                    if lp in rl:
                        I.add(rl[lp], ("lag",), ZERO, False)
                        lagkey = ("lag",)
        for s in sorted(srcs):
            l_tab = timing.late(s, confine)
            if not any(p in l_tab for p in peers):
                continue
            I.add(lagkey, ("ds", s), ZERO, False)
            rd = seg(I, ("d", s), ("ds", s), s, set(peers), set(), inside)
            I.data |= set(rd.values())
        _emit(c, I, V, {"rule": "A", "ctl": parent, "pairing": "bundled",
                        "lag": lagkey != V, "const_dropped": 0 if KEEP_CONST else nconst})


# ------------------------------------------------------------------------- E

K = 6
RE_LATCH_OUT = re.compile(r"^(.*?)\.lat\.")


def rule_E(c):
    T, edges, stops, ivl, Inst = c["T"], c["edges"], c["stops"], c["ivl"], c["Inst"]
    import pathlib
    jpath = pathlib.Path(c["routed"])
    sites = T.select_consumers(jpath)
    ffs = T.fastfall_side_arcs(edges)
    early_edges = {s: [(d, w) for d, w in lst if (s, d) not in ffs] for s, lst in edges.items()}
    binc, srcs_of = defaultdict(list), defaultdict(set)
    for s, lst in edges.items():
        for d, w in lst:
            binc[d].append((s, w))
            srcs_of[d].add(s)
    feed = {(o, ip) for o in stops for ip, _ in binc.get(o, ()) if o in srcs_of[ip]}
    rev = {}
    for name, ES in (("req", early_edges), ("sel", edges)):
        r = defaultdict(list)
        for s, lst in ES.items():
            for d, w in lst:
                r[d].append(s)
        rev[name] = r

    def skew_back(pin):          # skew.py main().back, verbatim
        seen, cur = {pin: 0}, {pin}
        for k in range(K + 1):
            frontier, lvl = list(cur), set(cur)
            while frontier:
                nxt = []
                for pn in frontier:
                    for s in srcs_of.get(pn, ()):
                        if (s, pn) in feed or s in seen:
                            continue
                        seen[s] = k
                        lvl.add(s)
                        if s not in stops:
                            nxt.append(s)
                frontier = nxt
            cur = set()
            for o in [x for x in lvl if x in stops]:
                for ip, _ in binc.get(o, ()):
                    if (o, ip) in feed or ip in seen:
                        continue
                    seen[ip] = k + 1
                    cur.add(ip)
            if not cur:
                break
        return seen

    def bwd(target, side):
        """States (d, p): p reached d storage crossings BEFORE the target's level,
        on the side's arc set (skew.walk's seeding rule, backwards)."""
        r = rev[side]
        B = {(0, target)}
        work = [(0, target)]
        while work:
            d, p = work.pop()
            if p in stops:
                if d + 1 > K:
                    continue
                for ip in r.get(p, ()):
                    if (p, ip) in feed:
                        continue
                    st = (d + 1, ip)
                    if st not in B:
                        B.add(st); work.append(st)
            else:
                for s in r.get(p, ()):
                    if (s, p) in feed:
                        continue
                    st = (d, s)
                    if st not in B:
                        B.add(st); work.append(st)
        return B

    def dag(B, launch, side):
        """Forward from the launch at level 0 inside B; -> (kt, arcs[((d,p),(d',q),w)])
        or None when the launch does not reach the pin within K crossings."""
        ds = [d for (d, p) in B if p == launch]
        if not ds:
            return None
        kt = min(ds)
        ES = early_edges if side == "req" else edges
        arcs, seen, work = [], {(kt, launch)}, [(kt, launch)]
        while work:
            d, p = work.pop()
            for q, w in ES.get(p, ()):
                if q == launch:
                    continue
                if q in stops:
                    if (q, p) in feed:
                        continue
                    st = (d - 1, q)
                else:
                    if (p, q) in feed:
                        continue
                    st = (d, q)
                if st not in B or st[0] < 0:
                    continue
                arcs.append(((d, p), st, w))
                if st not in seen:
                    seen.add(st); work.append(st)
        if (0, None) in seen:
            pass
        return kt, arcs

    def doms(root, arcs, target):
        """Dominator chain of target in a DAG (root first)."""
        preds, succ, indeg, nodes = defaultdict(list), defaultdict(list), defaultdict(int), {root}
        for a, b, _ in arcs:
            preds[b].append(a); succ[a].append(b); indeg[b] += 1; nodes |= {a, b}
        order, ready = [], [root]
        while ready:
            n = ready.pop(); order.append(n)
            for m in succ[n]:
                indeg[m] -= 1
                if indeg[m] == 0:
                    ready.append(m)
        pos = {n: i for i, n in enumerate(order)}
        idom = {root: root}
        for n in order[1:]:
            ps = [p for p in preds[n] if p in idom]
            x = ps[0]
            for y in ps[1:]:
                a, b = x, y
                while a != b:
                    while pos[a] > pos[b]:
                        a = idom[a]
                    while pos[b] > pos[a]:
                        b = idom[b]
                x = a
            idom[n] = x
        chain, n = [target], target
        while n != root:
            n = idom[n]; chain.append(n)
        return chain[::-1]

    checks = []
    for kind, parent, reqs, sels in sites:
        by_cell = defaultdict(dict)
        for q in reqs:
            by_cell[T.pin_split(q)[0]]["req"] = q
        for q in sels:
            by_cell[T.pin_split(q)[0]]["sel"] = q
        for cell, d in sorted(by_cell.items()):
            if "req" in d and "sel" in d:
                checks.append((kind, parent, cell, d["req"], d["sel"]))
    for kind, parent, cell, rp, sp in checks:
        br, bs = skew_back(rp), skew_back(sp)
        cand = sorted((bs[q], br[q], q) for q in set(br) & set(bs)
                      if q in stops and not T.is_const(q))
        names = {q for _, _, q in cand}
        launches = [q for _, _, q in cand[:4]]
        if cand:
            k0 = cand[0][0]
            for ks, _, q in cand:
                if ks != k0:
                    break
                m = RE_LATCH_OUT.match(T.pin_split(q)[0])
                cnode = m and m.group(1) + ".ctl.u.u/O6"
                if cnode and cnode in names and cnode not in launches:
                    launches.append(cnode)
        Br, Bs = bwd(rp, "req"), bwd(sp, "sel")
        any_ok = False
        for launch in launches:
            gr, gs = dag(Br, launch, "req"), dag(Bs, launch, "sel")
            if gr is None or gs is None:
                continue
            (ktr, ar), (kts, as_) = gr, gs
            # absolute level k = kt - d
            A_r = [((ktr - a[0], a[1]), (ktr - b[0], b[1]), w) for a, b, w in ar]
            A_s = [((kts - a[0], a[1]), (kts - b[0], b[1]), w) for a, b, w in as_]
            root = (0, launch)
            tr, ts = (ktr, rp), (kts, sp)
            ch_r = doms(root, A_r, tr)
            ch_s = set(doms(root, A_s, ts))
            X = next(x for x in reversed(ch_r) if x in ch_s)
            xkind = ("launch" if X == root else "storage" if X[1] in stops else
                     "LUT output" if T.is_output(X[1]) else "pin (net from a single driver)")
            for credit in (False, True):
                if credit and X == root:
                    continue
                start = X if credit else root
                tag = "E" if credit else "E0"
                I = Inst(f"{tag} {cell} launch={launch} levels={ktr}/{kts}"
                         + (f" X={X[0]}:{X[1]}" if credit else ""))
                L = ("launch",)
                for side, arcs, tgt in (("er", A_r, tr), ("es", A_s, ts)):
                    if credit:   # descendants of X only
                        succ = defaultdict(list)
                        for a, b, w in arcs:
                            succ[a].append(b)
                        keep, work = {X}, [X]
                        while work:
                            n = work.pop()
                            for m in succ[n]:
                                if m not in keep:
                                    keep.add(m); work.append(m)
                        arcs = [x for x in arcs if x[0] in keep]
                    key = lambda n, side=side: L if n == start else (side,) + n  # noqa: E731
                    for a, b, w in arcs:
                        iv, fb = ivl(a[1], b[1], w)
                        I.add(key(a), key(b), iv, fb)
                    if side == "er":
                        I.req = key(tgt)
                    else:
                        I.data = {key(tgt)}
                any_ok |= _emit(c, I, L, {"rule": tag, "ctl": cell, "launch": launch,
                                          "levels": [ktr, kts], "X": list(X), "X_kind": xkind,
                                          "parent": parent, "kind": kind})
        if not any_ok:
            c["meta"].append({"rule": "E", "ctl": cell, "skip": "no launch reaches both pins"})


# ------------------------------------------------------------------------- F

def rule_F(c):
    T, edges, back, stops, timing = c["T"], c["edges"], c["back"], c["stops"], c["timing"]
    seg, Inst, ivl, fr = c["segment"], c["Inst"], c["ivl"], c["fr"]
    chains = T.find_chains(edges)
    proj = {r[0]: r for r in T.audit_fastfall(edges, back, chains, timing)}
    ffside = T.fastfall_side_arcs(edges)
    side_by_base = defaultdict(list)
    for (src, dst) in ffside:
        side_by_base[T.RE_LINK.match(T.pin_split(dst)[0]).group("base")].append((src, dst))
    inputs_of, output_of = defaultdict(list), {}
    for p in set(edges) | set(back):
        inst = T.pin_split(p)[0]
        if not T.RE_LINK.match(inst):
            continue
        if T.is_output(p):
            output_of[inst] = p
        else:
            inputs_of[inst].append(p)
    W = lambda a, b: next((w for d, w in edges.get(a, ()) if d == b), None)  # noqa: E731
    for base in sorted(side_by_base):
        pr = proj.get(base)
        pmeta = {"rule": "F", "ctl": base, "project": list(pr[1:]) if pr else None}
        links = chains.get(base, [])
        head, tail = T.chain_endpoints(edges, back, links)
        srcs = {s for s, _ in side_by_base[base]}
        if len(srcs) != 1 or tail is None:
            pmeta["skip"] = "side taps from several nets or no tail"
            c["meta"].append(pmeta)
            continue
        src = next(iter(srcs))
        I = Inst(f"F {base} n={len(links)}")
        L = ("launch", src)
        prev = None
        ok = True
        for i, inst in enumerate(links):
            out = output_of.get(inst)
            if out is None:
                ok = False
                break
            n_in = 0
            for ip in inputs_of.get(inst, ()):
                arc = W(ip, out)
                if arc is None:
                    continue
                if (src, ip) in ffside:               # the side tap: controlling 0
                    iv, fb = ivl(src, ip, W(src, ip)); I.add(L, ("f", ip), iv, fb)
                    iv, fb = ivl(ip, out, arc); I.add(("f", ip), ("fo", out), iv, fb)
                    n_in += 1
            if n_in == 0 and i == 0:                  # the head: src -> its input(s)
                ins = [ip for ip in inputs_of.get(inst, ()) if W(ip, out) is not None]
                rh = seg(I, "h", L, src, set(ins), set())
                for ip, k in rh.items():
                    iv, fb = ivl(ip, out, W(ip, out)); I.add(k, ("fo", out), iv, fb)
                    n_in += 1
            if n_in == 0 and prev is not None:        # no side tap: the ripple
                for ip in inputs_of.get(inst, ()):
                    if prev in {s for s in back.get(ip, ())} and W(ip, out) is not None:
                        iv, fb = ivl(prev, ip, W(prev, ip)); I.add(("fo", prev), ("f", ip), iv, fb)
                        iv, fb = ivl(ip, out, W(ip, out)); I.add(("f", ip), ("fo", out), iv, fb)
                        n_in += 1
            if n_in == 0:
                ok = False
                break
            I.data.add(("fo", out))
            prev = out
        if not ok:
            pmeta["skip"] = "stage not traceable"
            c["meta"].append(pmeta)
            continue
        if c.get("cert") and "Fc" in c["want"]:
            # C-10h: data side = the stage falls built above; late side = src's next
            # change over the whole graph: phase 0 = the falling wave (no FASTRISE taps,
            # storage not left) up to the tail, switch at the tail, phase 1 = anything
            # back to src (tighten's shortest_to), bounded by a checked potential.
            Ic = Inst(f"Fc {base} n={len(links)}")
            Ic.arcs, Ic.data = list(I.arcs), set(I.data)
            sp = c["certs"].spec(src, [(src, 1)], two=1, noFr0=1, stop0=1, sw={tail})
            c["certs"].emit_cert(c["cctx"], Ic, L, sp, dict(pmeta, rule="Fc"))
        if "F" not in c["want"]:
            continue
        rx = seg(I, "x", L, src, {tail}, fr)
        if tail not in rx:
            pmeta["skip"] = "no fall path to the tail"
            c["meta"].append(pmeta)
            continue
        chains_used = set()
        for j, v in enumerate(("sdf", "fast", "slow")):
            path = _dijkstra(edges, tail, src, lambda a, b, w, v=v: ivl(a, b, w)[0][v][0])
            if path is None or tuple(path) in chains_used:
                continue
            chains_used.add(tuple(path))
            for x, y in zip(path, path[1:]):
                iv, fb = ivl(x, y, W(x, y))
                I.add(rx[tail] if x == tail else ("b", j, x), ("b", j, y), iv, fb)
            I.add(("b", j, src), ("ret",), ZERO, False)
            I.req = ("ret",)
        pmeta["back_chains"] = len(chains_used)
        _emit(c, I, L, pmeta)


def _dijkstra(edges, start, target, wfun, limit=200000):
    best, prev, heap, n = {start: 0}, {}, [(0, start)], 0
    while heap:
        t, p = heapq.heappop(heap)
        if p == target:
            path = [p]
            while path[-1] != start:
                path.append(prev[path[-1]])
            return path[::-1]
        if t > best.get(p, math.inf):
            continue
        n += 1
        if n > limit:
            return None
        for d, w in edges.get(p, ()):
            if d == start:
                continue
            nt = t + wfun(p, d, w)
            if nt < best.get(d, math.inf):
                best[d] = nt; prev[d] = p
                heapq.heappush(heap, (nt, d))
    return None


# ------------------------------------------------------------------------- J

def rule_J(c):
    import json
    T, edges, ivl, Inst, P, intervals = c["T"], c["edges"], c["ivl"], c["Inst"], c["P"], c["intervals"]
    j = json.load(open(c["routed"]))
    top = [m for m in j["modules"].values() if m.get("attributes", {}).get("top")][0]
    cells = top["cells"]
    routes = {}
    for nn in top["netnames"].values():
        r = nn.get("attributes", {}).get("ROUTING")
        if r and nn["bits"]:
            routes.setdefault(nn["bits"][0], r)
    driver, fanout = {}, defaultdict(int)
    for cn, cc in cells.items():
        for p, d in cc.get("port_directions", {}).items():
            for b in cc["connections"].get(p, []):
                if d == "output":
                    driver[b] = (cn, p)
                else:
                    fanout[b] += 1

    def pins(cn):
        cc = cells[cn]
        return {p: cc["connections"][p][0] for p, d in cc["port_directions"].items()
                if d == "input" and cc["connections"].get(p)}

    def out_bit(cn):
        cc = cells[cn]
        for p in ("O6", "O5", "O"):
            if p in cc["connections"] and cc["port_directions"].get(p) == "output":
                return p, cc["connections"][p][0]
        return None, None

    def path_to(bit, cn):          # arb_fork.py, verbatim
        r = routes.get(bit)
        bel = cells[cn]["attributes"].get("NEXTPNR_BEL", "")
        if r is None or "/" not in bel:
            return None
        site, lut = bel.split("/")
        sink = re.compile(r"^SITEWIRE/%s/%s[1-6]$" % (re.escape(site), lut[0]))
        f = r.split(";")
        parent = {}
        for i in range(0, len(f) - 2, 3):
            w, pip = f[i], f[i + 1]
            parent[w] = pip.split("->")[0] if "->" in pip else None
        hits = [w for w in parent if sink.match(w)]
        if len(hits) != 1:
            return None
        out, w, seen = [], hits[0], set()
        while w is not None and w not in seen:
            seen.add(w); out.append(w); w = parent.get(w)
        return out[::-1]

    def shared_ps(bit, sa, d_a, sb, d_b):   # arb_fork.py, verbatim
        pa, pb = path_to(bit, sa), path_to(bit, sb)
        if not pa or not pb:
            return 0
        n = 0
        for x, y in zip(pa, pb):
            if x != y:
                break
            n += 1
        hops_a, hops_b = max(len(pa) - 1, 1), max(len(pb) - 1, 1)
        shared = max(n - 1, 0)
        return int(min(d_a * shared / hops_a, d_b * shared / hops_b))

    def W(a, b):
        return next((w for d, w in edges.get(a, ()) if d == b), None)

    arbs = sorted(cn[:-len(".ustate$LUT6")] for cn in cells if cn.endswith(".ustate$LUT6"))
    for a in arbs:
        st = a + ".ustate$LUT6"
        _, q = out_bit(st)
        for k, gcell in ((1, a + ".ugrant$LUT5"), (2, a + ".ugrant$LUT6")):
            ua = a + f".ua{k}.u"
            meta = {"rule": "J", "ctl": f"{a}#{k}"}
            try:
                gport, g = out_bit(gcell)
                if gcell.endswith("$LUT5") and "O5" in cells[gcell]["connections"]:
                    gport, g = "O5", cells[gcell]["connections"]["O5"][0]
                pu, ps, pg = pins(ua), pins(st), pins(gcell)
                common = (set(pu.values()) & set(ps.values())) - {q, g}
                ext = [b for b in common if driver.get(b, ("", ""))[0].startswith(a + ".") is False]
                a0 = min(ext, key=lambda b: fanout[b])
                src = "/".join(driver[a0])
                ua_a0 = next(p for p, b in pu.items() if b == a0)
                ua_g = next(p for p, b in pu.items() if b == g)
                st_a0 = next(p for p, b in ps.items() if b == a0)
                g_q = next(p for p, b in pg.items() if b == q)
            except (KeyError, StopIteration, ValueError) as e:
                meta["skip"] = f"not resolved {type(e).__name__}"
                c["meta"].append(meta)
                continue
            n_ua, n_st = f"{ua}/{ua_a0}", f"{st}/{st_a0}"
            hops = [(f"{st}/{st_a0}", f"{st}/O6"), (f"{st}/O6", f"{gcell}/{g_q}"),
                    (f"{gcell}/{g_q}", f"{gcell}/{gport}"), (f"{gcell}/{gport}", f"{ua}/{ua_g}"),
                    (f"{ua}/{ua_g}", f"{ua}/O6")]
            d_ua, d_st = W(src, n_ua), W(src, n_st)
            if d_ua is None or d_st is None or any(W(x, y) is None for x, y in hops) \
                    or W(n_ua, f"{ua}/O6") is None:
                meta["skip"] = "an arc is missing from the SDF graph"
                c["meta"].append(meta)
                continue
            c_proj = shared_ps(a0, ua, d_ua, st, d_st)
            sp = P.split(src, n_ua, n_st)
            meta.update(src=src, c_proj=c_proj, d_ua=d_ua, d_st=d_st)
            if sp is not None:
                sh, sa, sb = sp
                fa, fb_ = sh[3] / (sh[3] + sa[3]), sh[3] / (sh[3] + sb[3])
                c_x = int(min(d_ua * fa, d_st * fb_))
                meta.update(shared_prjx=[round(x) for x in sh], c_x_sdf=c_x)
            for tag in ("J0", "Jx", "Jp"):
                if tag == "Jx" and sp is None:
                    continue
                I = Inst(f"{tag} {a}#{k}")
                L = ("launch",)
                if tag == "J0":
                    iva, fa_ = ivl(src, n_ua, d_ua)
                    ivb, fb2 = ivl(src, n_st, d_st)
                elif tag == "Jx":
                    iva, fa_ = intervals(d_ua - c_x, sa), False
                    ivb, fb2 = intervals(d_st - c_x, sb), False
                else:
                    iva0, fa_ = ivl(src, n_ua, d_ua)
                    ivb0, fb2 = ivl(src, n_st, d_st)
                    pa_, pb_ = intervals(d_ua - c_proj, None), intervals(d_st - c_proj, None)
                    iva = dict(iva0, sdf=pa_["sdf"], sdfband=pa_["sdfband"])
                    ivb = dict(ivb0, sdf=pb_["sdf"], sdfband=pb_["sdfband"])
                I.add(L, ("a", n_ua), iva, fa_)
                iv, fb = ivl(n_ua, f"{ua}/O6", W(n_ua, f"{ua}/O6"))
                I.add(("a", n_ua), ("a", f"{ua}/O6"), iv, fb)
                I.add(L, ("g", n_st), ivb, fb2)
                for x, y in hops:
                    iv, fb = ivl(x, y, W(x, y))
                    I.add(("g", x), ("g", y), iv, fb)
                I.req = ("g", f"{ua}/O6")
                I.data = {("a", f"{ua}/O6")}
                _emit(c, I, L, dict(meta, rule=tag))
