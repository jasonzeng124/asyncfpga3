#!/usr/bin/env python3
"""Probe C-10l front end (UNTRUSTED for the shapes and the choices; every potential is
checked by tcheck's `Tcheck.xverdict`, proved in `xverdict_sound`).  Called from
extract.py (`--rules10l LETTERS`).

Every instance here is CREDITED (Formal/Timing/SharedPrefix.lean): per corner variant
the front end picks a node X of the data DAG that
  (1) dominates every paired data node (all data paths from the launch D pass X), and
  (2) lies, in phase 0, on the critical late path of the uncredited row,
taking the deepest such node (the longest shared prefix).  It then writes
  * dagD = the whole data DAG (from D) and dagA = its suffix from X (node 0 = X);
  * potB = distances from D with X's phase-0 out-arcs dropped (cap = target distance
    or latest data from D + 20 ns, whichever is smaller);
  * potA = distances from (X, 0) (arcs out of D's launch dropped), same cap rule;
  * max nodes (`maxn`): C-elements whose next edge needs EVERY listed pin
    (Formal/Timing/MaxNode.lean `cel_needs_pin`); potA's arg-max arc is reused for potB
    so one arc satisfies both certificates, as `Pot2OK` requires.
Any choice is sound if tcheck accepts it (a wrong X only weakens or refutes the bound);
what the choice rests on is the identification (H_ONE_SAMPLE_PER_WIRE: X's one edge
drives both sides) and H_CLEAN_EDGE(X), recorded per row in the JSON (`x_kind`,
`x_reconv`: LUTs on the D->X prefix with two or more inputs driven from D).

Rules (letters):
  C  rule X / Xi with credit: rows Xc (rule X's phase rule), Xic (Xi's: + H_OR_IDLE),
     Xm (max nodes: D over ALL its handshake inputs; each other root r of an OR'ed
     z over its REQUEST pin only, under H_REQ_AGREE -- r's request pin is low with r
     at the launch, a protocol fact -- instead of H_OR_IDLE).
  K  B's X4 second half, ctl_req -> {uj0, uj1(, uj2)} weak isochrony: launch = the
     control channel's request driver C (common storage root of every join's ctl pin);
     data = C -> one join's ctl pin (any change the edge causes there; one instance per
     join); target = (that join's select pin s, phase 1); phase 1 entered at C's
     handshake inputs, (C, 1) a max node over them (C's next edge), and the select
     latch's output a phase-1 max node over its enable pins (H_LATCH_CLOSED: C's edge
     closed it with D = Q, which rule H checks, so it moves only after its enable
     reopens, i.e. after C's next edge).  PASS: the ctl pulse at the join has ended
     before s can change there, so no stale pulse can fire the newly selected join
     (B's `mux_needs_iso_cr`).
  D  diagnostics only (no instances): Fd's least-margin pairs on cm12 / ushrsi3 with
     the arcs shared by the data and late critical paths (rule_FdDiag).
"""
import heapq
import math
import re
from collections import defaultdict

import rules10k as K
from rules10k import _roots, _fb_pins, _in_pins, _W, _graph

INF = 10 ** 12
SLACK = 20000


def emit_all(c, which):
    c.setdefault("_root_cache", {})
    if "C" in which:
        rule_XC(c)
    if "K" in which:
        rule_K(c)
    if "D" in which:
        rule_FdDiag(c)


# ---------------------------------------------------------------- product-graph Dijkstra

def _maxsrc(G, spec, maxn, v):
    """maxn: {(pin, ph): [(src pin, src ph)]} -> {src node: [(max node, lo)]}, and group sizes."""
    ms, size = defaultdict(list), {}
    for m, srcs in maxn.items():
        n = 0
        for sn in srcs:
            lo = None
            for (q, qh), l in G.out_arcs(spec, sn[0], sn[1], v):
                if (q, qh) == m:
                    lo = l if lo is None else max(lo, l)
            if lo is not None:
                ms[sn].append((m, lo)); n += 1
        size[m] = n
    return ms, size


def dij(G, spec, v, src, targets, block=None, maxn=None, fixed=None, bound=INF, prev=None):
    """Distances on the product graph (Tcheck.expand), from `src` (a (pin, ph) node), never
    entering the launch (spec s, 0), with `block`'s out-arcs dropped and max nodes.
    Stops once every target is settled or the popped distance reaches `bound`.
    -> (best, cap, argmax) with cap = min(largest target distance, bound)."""
    s0 = (spec["s"], 0)
    maxn = maxn or {}
    ms, size = _maxsrc(G, spec, maxn, v)
    rem = dict(size)
    acc, arg = {}, {}
    best = {src: 0}
    heap = [(0, 0, src)]
    cnt, left, seen_t, done = 0, set(targets) - {src}, [], set()
    stopped = None
    while heap and left:
        t, _, n = heapq.heappop(heap)
        if n in done or t > best.get(n, math.inf):
            continue
        if t >= bound:
            stopped = bound
            break
        done.add(n)
        if n in left:
            left.discard(n); seen_t.append(t)
            if not left:
                break

        def relax(q, nt, frm):
            nonlocal cnt
            if nt < best.get(q, math.inf):
                best[q] = nt
                if prev is not None:
                    prev[q] = frm
                cnt += 1
                heapq.heappush(heap, (nt, cnt, q))
        if n != block:
            for q, lo in G.out_arcs(spec, n[0], n[1], v):
                if q == s0 or q in maxn:
                    continue
                relax(q, t + lo, n)
        for m, lo in ms.get(n, ()):
            if fixed is not None:
                if fixed.get(m) == n:
                    relax(m, t + lo, n)
                continue
            rem[m] -= 1
            if t + lo >= acc.get(m, -1):
                acc[m], arg[m] = t + lo, n
            if rem[m] == 0:
                relax(m, acc[m], arg[m])
    if not left:
        cap = min(max(seen_t), bound) if seen_t else 0
    elif stopped is not None:
        cap = bound
    else:
        cap = bound if bound < INF else INF
    # max nodes not completed: choose an unsettled source (its potential is the cap)
    for m, srcs in maxn.items():
        if m not in arg or rem.get(m, 0) > 0:
            uns = [sn for sn in srcs if best.get(sn, math.inf) >= cap
                   and any(mm == m for mm, _ in ms.get(sn, ()))]
            if uns:
                arg[m] = uns[0]
            elif m not in arg and srcs:
                arg[m] = srcs[0]
    return best, cap, arg


def _late_hi(I, L, v):
    """Latest arrival (sum of hi) at every node of the data DAG from L."""
    succ = defaultdict(list)
    indeg = defaultdict(int)
    nodes = {L}
    for a, b, iv, _ in I.arcs:
        succ[a].append((b, iv[v][1])); indeg[b] += 1; nodes |= {a, b}
    late = {L: 0}
    ready = [L]
    while ready:
        n = ready.pop()
        for m, hi in succ[n]:
            late[m] = max(late.get(m, -1), late[n] + hi)
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
    return late


def _pin_of(key, L, D):
    if key == L:
        return D
    return key[-1] if isinstance(key, tuple) and isinstance(key[-1], str) else None


def _dominators(I, L, datas):
    """Data-DAG nodes (other than L) through which every path from L to every node in
    `datas` passes."""
    succ = defaultdict(list)
    nodes = {L}
    for a, b, _, _ in I.arcs:
        succ[a].append(b); nodes |= {a, b}
    datas = set(datas)
    doms = set()
    for n in nodes:
        if n == L:
            continue
        seen, work = {L}, [L]
        hit = False
        while work and not hit:
            p = work.pop()
            for q in succ[p]:
                if q == n or q in seen:
                    continue
                if q in datas:
                    hit = True
                    break
                seen.add(q); work.append(q)
        if not hit:
            doms.add(n)
    return doms


def _sub_dag(I, X):
    """Arcs of I reachable from key X."""
    succ = defaultdict(list)
    for a in I.arcs:
        succ[a[0]].append(a)
    seen, work, arcs = {X}, [X], []
    while work:
        p = work.pop()
        for a in succ[p]:
            arcs.append(a)
            if a[1] not in seen:
                seen.add(a[1]); work.append(a[1])
    return arcs, seen


def _topo(arcs, L):
    succ, indeg, nodes = defaultdict(list), defaultdict(int), {L}
    for a, b, _, _ in arcs:
        succ[a].append(b); indeg[b] += 1; nodes |= {a, b}
    order, ready = [], [L]
    while ready:
        n = ready.pop(); order.append(n)
        for m in succ[n]:
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
    if len(order) != len(nodes):
        raise RuntimeError("data side not a DAG")
    return {n: i for i, n in enumerate(order)}


def emit_credited(c, I, L, D, pairs, spec_of, meta):
    """pairs: [(data key, target pin, phase)]; spec_of(v) -> (spec, maxn, pick-info)."""
    G = _graph(c)
    T = c["T"]
    f = c["cctx"]["out"]
    pairs = [(d, p, ph) for d, p, ph in pairs if p in G.id]
    if not pairs or not I.arcs:
        meta["skip"] = "no pair"
        c["meta"].append(meta)
        return False
    idxD = _topo(I.arcs, L)
    pairs = [(d, p, ph) for d, p, ph in pairs if d in idxD]
    datas = {d for d, _, _ in pairs}
    doms = _dominators(I, L, datas)
    pin2key = {}
    for k in idxD:
        if k in doms:
            pp = _pin_of(k, L, D)
            if pp is not None and pp in G.id:
                pin2key.setdefault(pp, k)
    tg = {(p, ph) for _, p, ph in pairs}
    nfb = sum(fb for *_, fb in I.arcs)
    meta["label"] = I.label
    meta["pairs"] = len(pairs)
    meta.setdefault("x", {})
    for vi, v in enumerate(c["VARIANTS"]):
        spec, maxn, info = spec_of(v)
        lateD = _late_hi(I, L, v)
        lD = max(lateD.get(d, 0) for d in datas)
        # 1. the uncredited critical late path (to the first pair's target)
        prev = {}
        best0, cap0, _ = dij(G, spec, v, (spec["s"], 0), tg, maxn=maxn, prev=prev,
                             bound=lD + SLACK)
        x = (pairs[0][1], pairs[0][2])
        path = []
        while x in prev:
            path.append(x); x = prev[x]
        path.append(x)
        path.reverse()
        # 2. X candidates: phase-0 nodes of that path that dominate the data, shallow first
        onp = [p for (p, ph) in path if ph == 0 and p in pin2key and p != D]
        cands = sorted(set(onp), key=lambda p: idxD[pin2key[p]])
        if not cands:
            # no shared node on the path: credit the deepest dominator anyway (sound,
            # it only splits the certificate)
            allc = sorted((idxD[pin2key[p]], p) for p in pin2key if p != D)
            cands = [allc[-1][1]] if allc else []
        if not cands:
            meta["skip"] = "no dominator"
            break
        tmin = lambda b, cp: min(min(b.get(t_, cp), cp) for t_ in tg)   # noqa: E731

        def evaluate(X):
            XK = pin2key[X]
            arcsA, _reach = _sub_dag(I, XK)
            lateA = {}
            if arcsA:
                class _I:
                    pass
                IA = _I(); IA.arcs = arcsA
                lateA = _late_hi(IA, XK, v)
            lA = max(lateA.get(d, 0) for d in datas)
            idxA = _topo(arcsA, XK) if arcsA else {XK: 0}
            # potA (from (X,0)) and potB (X blocked); one arc per max node must serve both
            # certificates (Pot2OK): try A's arg-max and B's arg-max, keep the better
            bestA, capA, argA = dij(G, spec, v, (X, 0), tg, maxn=maxn, bound=lA + SLACK)
            bestB, capB, _ = dij(G, spec, v, (spec["s"], 0), tg, block=(X, 0), maxn=maxn,
                                 fixed=argA, bound=lD + SLACK)
            if maxn:
                bB2, cB2, argB = dij(G, spec, v, (spec["s"], 0), tg, block=(X, 0), maxn=maxn,
                                     bound=lD + SLACK)
                if argB != argA:
                    bA2, cA2, _ = dij(G, spec, v, (X, 0), tg, maxn=maxn, fixed=argB, bound=lA + SLACK)
                    m1 = min(tmin(bestB, capB) - lD, tmin(bestA, capA) - lA)
                    m2 = min(tmin(bB2, cB2) - lD, tmin(bA2, cA2) - lA)
                    if m2 > m1:
                        bestA, capA, bestB, capB = bA2, cA2, bB2, cB2
            marg = min(tmin(bestB, capB) - lD, tmin(bestA, capA) - lA)
            return marg, (X, arcsA, idxA, lA, bestA, capA, bestB, capB)
        tried = {}
        best_m, sol = evaluate(cands[0])
        tried[cands[0]] = best_m
        if best_m < 0:
            for X2 in cands[1:]:
                m2, sol2 = evaluate(X2)
                tried[X2] = m2
                if m2 > best_m:
                    best_m, sol = m2, sol2
        X, arcsA, idxA, lA, bestA, capA, bestB, capB = sol
        mB = tmin(bestB, capB)
        mA = tmin(bestA, capA)
        meta.setdefault("tried", {})[v] = {k.replace("urig.udut.", ""): m_ for k, m_ in tried.items()}
        meta["x"][v] = dict(X=X.replace("urig.udut.", ""), x_kind="out" if T.is_output(X) else "pin",
                            lD=lD, lA=lA, potB=min(mB, capB), potA=min(mA, capA),
                            uncredited=min(best0.get(t_, cap0) for t_ in tg) - lD,
                            path0=[p.rsplit("/", 1)[0].replace("urig.udut.", "") for p, ph in path if ph == 0][:40])
        if meta.get("rule") == "K":     # C-10l2: the whole uncredited late path, both phases
            meta["x"][v]["pathK"] = [(p.replace("urig.udut.", ""), ph, best0.get((p, ph)))
                                     for p, ph in path]
        if info is not None:
            meta.setdefault("pick", {})[v] = info
        # write
        f.write(f"inst {I.label} {v} fallback={nfb}/{len(I.arcs)}\n")
        f.write("setup 0\n")
        for a, b, ivd, _ in sorted(I.arcs, key=lambda q: (idxD[q[0]], idxD[q[1]])):
            lo, hi = ivd[v]
            f.write(f"arc {idxD[a]} {idxD[b]} {lo} {hi}\n")
        f.write("late %d %d %d %d %d %d\n" % (vi, G.id[spec["s"]], spec["two"], spec["noFr0"],
                                              spec["stop0"], spec["swStor"]))
        if spec["sw"]:
            f.write("sw " + " ".join(str(G.id[p]) for p in sorted(spec["sw"]) if p in G.id) + "\n")
        if spec["blocked"]:
            f.write("blocked " + " ".join(str(G.id[p]) for p in sorted(spec["blocked"])) + "\n")
        if spec.get("blocked0"):
            f.write("blocked0 " + " ".join(str(G.id[p]) for p in sorted(spec["blocked0"]) if p in G.id) + "\n")
        cut = sorted((G.id[a], G.id[b]) for a, b in spec.get("cut", ()) if a in G.id and b in G.id)
        for i in range(0, len(cut), 32):
            f.write("cut " + " ".join(f"{a} {b}" for a, b in cut[i:i + 32]) + "\n")
        f.write(f"credit {G.id[X]}\n")
        for a, b, ivd, _ in sorted(arcsA, key=lambda q: (idxA[q[0]], idxA[q[1]])):
            lo, hi = ivd[v]
            f.write(f"aarc {idxA[a]} {idxA[b]} {lo} {hi}\n")
        for d, p, ph in pairs:
            dA = idxA.get(d)
            if dA is None:          # cannot happen for a dominator; keep the row honest
                raise RuntimeError(f"{I.label}: data node not below X")
            f.write(f"xpair {idxD[d]} {dA} {G.id[p]} {ph}\n")
        for m, srcs in sorted(maxn.items()):
            if m[0] in G.id:
                f.write(f"maxn {G.id[m[0]]} {m[1]} " +
                        " ".join(f"{G.id[sp]} {sph}" for sp, sph in srcs if sp in G.id) + "\n")
        f.write(f"cap {capB}\n")
        lst = [(G.id[p], ph, d) for (p, ph), d in bestB.items() if d < capB and (p, ph) != (spec["s"], 0)]
        for i in range(0, len(lst), 40):
            f.write("pot " + " ".join(f"{a} {b} {d}" for a, b, d in lst[i:i + 40]) + "\n")
        f.write(f"acap {capA}\n")
        lst = [(G.id[p], ph, d) for (p, ph), d in bestA.items() if d < capA and (p, ph) != (spec["s"], 0)]
        for i in range(0, len(lst), 40):
            f.write("apot " + " ".join(f"{a} {b} {d}" for a, b, d in lst[i:i + 40]) + "\n")
        f.write("end\n")
    c["meta"].append(meta)
    return True


# ---------------------------------------------------------------- C: X / Xi / Xm credited

def _own_latch_outs(c, ctl):
    """Output pins of the latch bits whose enable controller is `ctl` (a pin)."""
    T = c["T"]
    lc = K._latch_ctl(c)
    lis = {li for li, (cc, _) in lc.items() if cc == ctl}
    return {q for q in c["edges"] if T.is_output(q) and T.pin_split(q)[0] in lis}


def _cell(inst):
    return inst.rsplit(".", 1)[0]


def rule_XC(c):
    T, stops = c["T"], c["stops"]
    seg, Inst, ivl = c["segment"], c["Inst"], c["ivl"]
    G = _graph(c)
    for o in sorted(stops):
        ui = T.pin_split(o)[0]
        m = K.RE_X.match(ui)
        if not m or not (".umux" in "." + ui or ".uarb" in ui):
            continue
        cell = m.group(1)
        fbs = _fb_pins(c, o)
        zp, zd = [], set()
        for p in _in_pins(c, ui):
            if p in fbs or _W(c, p, o) is None:
                continue
            roots, _free = _roots(c, p)
            if roots and not any(T.pin_split(r)[0].startswith(cell + ".") for r in roots):
                zp.append(p); zd |= roots
        if len(zp) != 1 or not zd:
            continue
        p0 = zp[0]

        def hs_inputs(r):
            rf = _fb_pins(c, r)
            return [p for p in _in_pins(c, T.pin_split(r)[0])
                    if p not in rf and _W(c, p, r) is not None and _roots(c, p)[0]]
        for D in sorted(zd):
            I = Inst(f"X {ui} z={T.pin_split(D)[0]}")
            L = ("launch", D)
            r0 = seg(I, "x0", L, D, {p0}, set())
            if p0 not in r0:
                continue
            iv, fb = ivl(p0, o, _W(c, p0, o)); I.add(r0[p0], ("xo", o), iv, fb)
            pairs = []
            for fp in sorted(fbs):
                iv, fb = ivl(o, fp, _W(c, o, fp)); I.add(("xo", o), ("xfb", fp), iv, fb)
                pairs.append((("xfb", fp), p0, 1))
            cand = hs_inputs(D)
            if not cand:
                continue
            others = sorted(r for r in zd if r != D)
            ocand = {r: hs_inputs(r) for r in others}
            base = c["certs"].spec(D, [], two=1)
            base["cut"] = set()
            # the OR cells on z's route (steers' uack): an other root's REQUEST pin is the
            # one driven from one of those cells (the steer's branch LUT)
            zcells = set()
            for r in zd:
                Ir = Inst("tmp")
                rr = seg(Ir, "t", ("launch", r), r, {p0}, set())
                for a, b, _, _ in Ir.arcs:
                    pb = b[-1] if isinstance(b, tuple) else None
                    if pb and not T.is_output(pb) and pb != p0:
                        zcells.add(_cell(T.pin_split(pb)[0]))
            req_pin = {}
            for r in others:
                rq = [p for p in ocand[r]
                      if any(_cell(T.pin_split(s_)[0]) in zcells for s_ in c["back"].get(p, ()))]
                req_pin[r] = rq

            def latest(v, pins):
                d0, _cap = K._dists(G, dict(base, sw=set()), v, {(p, 0) for p in pins})
                fin = [(d0[(p, 0)], p) for p in pins if (p, 0) in d0]
                return max(fin)[1] if fin else pins[0]

            def spec_X(v, idle):
                pick = latest(v, cand)
                sw = {pick}
                for r in others:
                    if idle and ocand[r]:
                        sw.add(latest(v, ocand[r]))
                    else:
                        sw.add(r)
                return dict(base, sw=sw), {}, pick.rsplit("/", 1)[1]

            own = _own_latch_outs(c, D)

            def spec_M(v):
                sw = set(cand)
                maxn = {(D, 1): [(p, 1) for p in cand]}
                for r in others:
                    rq = req_pin[r]
                    if len(rq) == 1:
                        sw.add(rq[0])
                        maxn[(r, 1)] = [(rq[0], 1)]
                        # the steer's branch LUT driving r's request: held at 0 by the
                        # steer's own (low) request pin (MaxNode.ctl_needs_pin, H_REQ_AGREE)
                        drv = sorted(c["back"].get(rq[0], ()))
                        if len(drv) == 1 and T.is_output(drv[0]):
                            sinst = T.pin_split(drv[0])[0]
                            sreq = [q for q in _in_pins(c, sinst) if _W(c, q, drv[0]) is not None
                                    and _roots(c, q)[0]
                                    and not any(T.RE_BD_LATCH.search(T.pin_split(x)[0]) for x in _roots(c, q)[0])]
                            if len(sreq) == 1:
                                maxn[(drv[0], 0)] = [(sreq[0], 0)]
                    else:                       # request pin not identified: rule X's switch
                        sw.add(r)
                return dict(base, sw=sw, blocked0=own), maxn, {"cand": [q.rsplit("/", 1)[1] for q in cand], "own_latch_bits": len(own),
                                                 "max": [f"{m[0].replace('urig.udut.', '')}:{m[1]}<-" + ",".join(q[0].rsplit('/', 1)[1] for q in g) for m, g in maxn.items()],
                                                 "req_pins": {r.replace("urig.udut.", ""): [q.rsplit("/", 1)[1] for q in req_pin[r]] for r in others}}
            meta0 = {"ctl": ui, "z": D, "roots": len(zd), "z_pin": p0}
            emit_credited(c, _relabel(I, "Xc"), L, D, pairs, lambda v: spec_X(v, False),
                          dict(meta0, rule="Xc"))
            if others:
                emit_credited(c, _relabel(I, "Xic"), L, D, pairs, lambda v: spec_X(v, True),
                              dict(meta0, rule="Xic"))
            emit_credited(c, _relabel(I, "Xm"), L, D, pairs, spec_M, dict(meta0, rule="Xm"))


def _relabel(I, tag):
    J = type(I)(tag + I.label[1:])
    J.arcs, J.data = list(I.arcs), set(I.data)
    return J


# ---------------------------------------------------------------- K: ctl_req -> joins

RE_J = re.compile(r"^(.*\.umux\d+)\.uj(\d)$")


def rule_K(c):
    T, stops = c["T"], c["stops"]
    seg, Inst, ivl = c["segment"], c["Inst"], c["ivl"]
    joins = defaultdict(list)
    for p in c["back"]:
        if T.is_output(p):
            continue
        inst = T.pin_split(p)[0]
        mm = RE_J.match(inst)
        if mm:
            joins[mm.group(1)].append(p)
    for mux in sorted(joins):
        jinst = sorted({T.pin_split(p)[0] for p in joins[mux]})
        # per join: pins rooted only in controllers (C-elements) vs in latches
        ctl_pins, sel_pins = defaultdict(list), defaultdict(list)
        ctl_root = defaultdict(set)
        for ji in jinst:
            jo = f"{ji}/O6" if f"{ji}/O6" in c["edges"] else next(
                (q for q in c["edges"] if T.pin_split(q)[0] == ji and T.is_output(q)), None)
            fbs = _fb_pins(c, jo) if jo else set()
            for p in _in_pins(c, ji):
                if p in fbs:
                    continue
                roots, _ = _roots(c, p)
                if not roots:
                    continue
                if all(T.RE_BD_LATCH.search(T.pin_split(r)[0]) for r in roots):
                    sel_pins[ji].append(p)
                elif len(roots) == 1 and not T.RE_BD_LATCH.search(T.pin_split(next(iter(roots)))[0]):
                    ctl_pins[ji].append(p); ctl_root[ji] |= roots
        common = set.intersection(*[ctl_root[j] for j in jinst]) if all(ctl_root[j] for j in jinst) else set()
        meta = {"rule": "K", "ctl": mux}
        if len(common) != 1 or not all(sel_pins[j] for j in jinst):
            meta["skip"] = f"ctl root / select pins not resolved (common {sorted(common)}, sel {dict(sel_pins)})"
            c["meta"].append(meta)
            continue
        C = next(iter(common))
        # the select latch: closed by C's edge with D = Q (rule H), its output is a max node
        # over its enable pins in phase 1 (it moves only once the enable reopens, which needs
        # C's next edge: MaxNode.cel_needs_pin with the enable as the agreeing pin)
        lc = K._latch_ctl(c)
        cf = _fb_pins(c, C)
        cand = [p for p in _in_pins(c, T.pin_split(C)[0])
                if p not in cf and _W(c, p, C) is not None and _roots(c, p)[0]]
        if not cand:
            meta["skip"] = "C has no handshake input"
            c["meta"].append(meta)
            continue
        maxn = {(C, 1): [(p, 1) for p in cand]}
        nlat = 0
        for ji in jinst:
            for sp in sel_pins[ji]:
                for r_ in _roots(c, sp)[0]:
                    li = T.pin_split(r_)[0]
                    if li in lc and lc[li][0] == C:
                        ens = [en for en in lc[li][1] if T.pin_split(en)[0] == li and _W(c, en, r_) is not None]
                        if ens:
                            maxn[(r_, 1)] = [(en, 1) for en in ens]
                            nlat += 1
        base = c["certs"].spec(C, [], two=1, sw=set(cand))
        base["cut"] = set()
        base["blocked0"] = _own_latch_outs(c, C)
        meta.update(latches=nlat, own_latch_bits=len(base["blocked0"]))
        n_ok = 0
        for ji in jinst:
            cps = [p for p in ctl_pins[ji] if C in _roots(c, p)[0]]
            for p in cps:
                I = Inst(f"K {ji} {T.pin_split(p)[1]} C={T.pin_split(C)[0]}")
                L = ("launch", C)
                r = seg(I, "k", L, C, {p}, set())
                if p not in r:
                    continue
                pairs = [(r[p], sp, 1) for sp in sel_pins[ji]]
                m2 = dict(meta, C=C, join=ji, cand=[q.rsplit("/", 1)[1] for q in cand],
                          sel=[q.rsplit("/", 1)[1] for q in sel_pins[ji]])
                emit_credited(c, I, L, C, pairs, lambda v: (base, maxn, None), m2)
                n_ok += 1
        if not n_ok:
            meta["skip"] = "ctl route not walkable"
            c["meta"].append(meta)


# ---------------------------------------------------------------- D: diagnostics for Fd (no instances)

def rule_FdDiag(c, only=("ucontrol_merge12", "ushrsi3")):
    """Evidence only (writes JSON meta, no obligations): for the Fd lines named in
    `only`, per corner variant and per pair, the data-side critical path, the late
    critical path, and the arcs the two share.  A shared arc is the SAME routed element
    carrying the fall (data, at hi) and the next rise (late, at lo): under a fixed delay
    per element and rise = fall (H_FIXED_DELAY + no H_RF_ASYM) the two charges cancel,
    so sum(hi - lo) over shared arcs is how much of a failure is the band's two-edge
    charge on one element rather than a real race."""
    G = _graph(c)
    real = K.emit_pairs

    def diag(c_, I, L, spec, pairs, meta, spec_v=None):
        if not any(o in I.label for o in only):
            return False
        pin = lambda k: k[1] if k[0] == "launch" else k[-1]   # noqa: E731
        out = {}
        for v in c_["VARIANTS"]:
            # data: longest hi path to each paired node, with its arcs
            succ = defaultdict(list)
            for a, b, iv, _ in I.arcs:
                succ[a].append((b, iv[v]))
            late, how = {L: 0}, {}
            order = _topo(I.arcs, L)
            for n in sorted(order, key=order.get):
                for b, (lo, hi) in succ.get(n, ()):
                    if late[n] + hi > late.get(b, -1):
                        late[b] = late[n] + hi; how[b] = (n, lo, hi)
            tg = {(p, ph) for _, p, ph in pairs}
            prev = {}
            best, cap, _ = dij(G, spec, v, (spec["s"], 0), tg, prev=prev)
            rows = []
            for d, p, ph in pairs:
                if d not in late or (p, ph) not in best:
                    continue
                darcs, x = {}, d
                while x in how:
                    n, lo, hi = how[x]; darcs[(pin(n), pin(x))] = (lo, hi); x = n
                larcs, y = set(), (p, ph)
                while y in prev:
                    z = prev[y]
                    if z[0] != y[0]:
                        larcs.add((z[0], y[0]))
                    y = z
                common = [a for a in darcs if a in larcs]
                credit = 0
                for a in common:
                    lo_ = next((iv[v][0] for dd, iv in G.succ.get(a[0], ()) if dd == a[1]), 0)
                    credit += darcs[a][1] - lo_
                rows.append(dict(stage=p.rsplit("/", 1)[0].rsplit(".", 2)[-2] if "." in p else p,
                                 margin=best[(p, ph)] - late[d], data=late[d], late=best[(p, ph)],
                                 shared=len(common), shared_credit=credit,
                                 shared_arcs=[f"{a[0].replace('urig.udut.', '')}->{a[1].replace('urig.udut.', '')}" for a in common][:6]))
            rows.sort(key=lambda r: r["margin"])
            out[v] = rows[:4]
        meta["diag"] = out
        meta["label"] = I.label
        c_["meta"].append(meta)
        return True
    K.emit_pairs = diag
    try:
        K.rule_Fd(c)
    finally:
        K.emit_pairs = real
