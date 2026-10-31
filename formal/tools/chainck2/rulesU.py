#!/usr/bin/env python3
"""Probe C-10o front end (UNTRUSTED for the shapes): H_CHAIN_SETTLED on routed delay chains.

Loaded by chainck.py into tcheck's extract.py (as its `rules10l` hook; tcheck itself is
not edited).  Two products per side-tapped chain (bd_delay FASTFALL / gated: AND stages;
bd_link `uack` FASTRISE: OR stages):

1. EXACT rows (`exact` in the TSV; Python mirror of Formal/Timing/ChainSettle.lean).
   The chain is the AND (resp. OR) network of every routed arc between the side-tap
   source `src` and the tail (head segment src -> g[0] input through LUT1 buffers, every
   stage's ripple pin AND tap pin, all routes and LUT pin arcs), one [lo, hi] per arc and
   variant (extract.ivl: sdf, sdfband, fast, slow, fastG, slowG).  Input: src moves at 0
   and moves back at T (H_PULSE).  The forced-low (FASTRISE: forced-high) set of every node
   is computed with lowPin_Ico / lowPin_union_gap ([x, y) with y > x + hi -> [x+hi, y+lo);
   maximal intervals map one by one); that IS `Lc` (ChainSettle.low_iff: exact for every
   run of the per-arc BoundedDelay model).  PASS iff the tail's set is ONE interval
   [A, B) with B >= T + Lrip (Lrip = lo-sum of the ripple path src -> head -> every chain
   pin -> tail, the matched length): `Settled z A (T + Lrip)`.  Then (settled_sound) the
   tail cannot re-rise (FASTRISE: re-fall) before the full matched delay after the input
   returned; by low_iff / runt_of_gap a FAIL is a run of the model with the tail high
   (FASTRISE: low) at a point of [A, T + Lrip): a runt or an early request (early ack
   fall).
   T is the late side of rule Fd / Fc: src's next change >= the tail's earliest change
   (phase 0: no storage crossed; FASTFALL rows: no FASTRISE tap) + the shortest routed
   path from the tail back to src (any arc; H_REUSE_CAUSAL).  PASS at the lower bound T
   is PASS for every later return (ChainSettleChain.settled_mono_T).  `T*` = least T that passes
   (binary search), `margin_exact = T - T*`.
   `margin_stage` = min over side-tapped stages of the per-stage overlap (B's H_GFLUSH,
   C-10k Fd in this calculus): T + lo(src->tap pin->out) - (start(prev) + hi(prev->chain
   pin->out)).  Sufficient; the exact row can pass with a negative stage margin when a
   later, slower tap covers the hole (B's `rescue_flushed`).

2. tcheck rows `Fu` (FASTRISE only; the FASTFALL lines already have C-10k's `Fd`, which
   chainck emits in the same run): rule Fd mirrored: data = each stage's RISE bounded by
   its side tap alone (an OR with a 1 on an input is 1: H_CONTROLLING), plus the hop
   out(j-1) -> chain pin(j); late = src's next change (phase 0: the rising wave to the
   tail, every arc allowed -- the FASTFALL-tap credit is not taken -- no storage crossed;
   switch at the tail; phase 1: anything back to src), target (side pin j, phase 1).
   Decided by tcheck's proved pverdict (`pverdict_sound`), potentials checked.
"""
import json
from collections import defaultdict

import rules10k as K           # tcheck's C-10k module: emit_pairs, _graph, _dists, _W

ROWS = []                      # exact rows, written by chainck.py
DUMP = []                      # C-10o2: per row and variant, the chain network as data for Lean


def dump_net(I, L, sides, tail_key, v):
    """Topological renumbering (launch = 0), arcs [src, dst, lo, hi], tap arc indices."""
    succ, indeg, nodes = defaultdict(list), defaultdict(int), {L}
    for a, b, ivd, _ in I.arcs:
        succ[a].append(b); indeg[b] += 1; nodes |= {a, b}
    order, ready = [], [L]
    while ready:
        n = ready.pop(); order.append(n)
        for m in succ[n]:
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
    idx = {n: i for i, n in enumerate(order)}
    arcs, taps = [], []
    for a, b, ivd, _ in I.arcs:
        if a == L and b in sides:
            taps.append(len(arcs))
        arcs.append([idx[a], idx[b], ivd[v][0], ivd[v][1]])
    return {"N": len(order) - 1, "z": idx[tail_key], "arcs": arcs, "taps": taps}


def norm(iv):
    out = []
    for x, y in sorted(iv):
        if x >= y:
            continue
        if out and x <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], y))
        else:
            out.append((x, y))
    return out


def shift(iv, lo, hi):
    # lowPin_Ico: [x, y) -> [x + hi, y + lo) when x + hi < y, else nothing
    return [(x + hi, y + lo) for x, y in iv if x + hi < y]


def propagate(arcs, L, v, T):
    """arcs: [(a, b, ivd, fb)] DAG from launch L.  -> {node: maximal intervals}."""
    succ, indeg, nodes = defaultdict(list), defaultdict(int), {L}
    ins = defaultdict(list)
    for a, b, ivd, _ in arcs:
        succ[a].append(b); indeg[b] += 1; nodes |= {a, b}
        ins[b].append((a, ivd[v]))
    order, ready = [], [L]
    while ready:
        n = ready.pop(); order.append(n)
        for m in succ[n]:
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
    if len(order) != len(nodes):
        raise RuntimeError("chain DAG has a cycle")
    S = {L: [(0, T)]}
    for n in order[1:]:
        acc = []
        for a, (lo, hi) in ins[n]:
            acc += shift(S[a], lo, hi)
        S[n] = norm(acc)
    return S


def chain_dag(c, base, src, links, ff):
    """All arcs of the chain network.  -> (I, stages, head_ok) or (None, reason, _)."""
    T, edges, back = c["T"], c["edges"], c["back"]
    seg, Inst, ivl = c["segment"], c["Inst"], c["ivl"]
    W = lambda a, b: K._W(c, a, b)  # noqa: E731
    inputs_of, output_of = defaultdict(list), {}
    for inst in links:
        for p in back:
            if T.pin_split(p)[0] == inst and not T.is_output(p):
                inputs_of[inst].append(p)
        for o in (inst + "/O6", inst + "/O5", inst + "/O"):
            if o in edges:
                output_of[inst] = o
                break
    I = Inst(f"X {base}")
    L = ("launch", src)
    prev, stages = None, []
    extra_in = 0
    for i, inst in enumerate(links):
        out = output_of.get(inst)
        if out is None:
            return None, "stage without output", None
        side_pin = chain_pin = None
        n_in = 0
        for ip in inputs_of.get(inst, ()):
            arc = W(ip, out)
            if arc is None:
                continue
            drv = back.get(ip, set())
            if src in drv and (src, ip) in ff:
                iv, fb = ivl(src, ip, W(src, ip)); I.add(L, ("p", ip), iv, fb)
                iv, fb = ivl(ip, out, arc); I.add(("p", ip), ("o", out), iv, fb)
                side_pin = ip; n_in += 1
            elif prev is not None and prev in drv:
                iv, fb = ivl(prev, ip, W(prev, ip)); I.add(("o", prev), ("p", ip), iv, fb)
                iv, fb = ivl(ip, out, arc); I.add(("p", ip), ("o", out), iv, fb)
                chain_pin = ip; n_in += 1
            elif i == 0:
                rh = seg(I, "h", L, src, {ip}, set())
                if ip not in rh:
                    return None, "head input not reached from src", None
                iv, fb = ivl(ip, out, arc); I.add(rh[ip], ("o", out), iv, fb)
                chain_pin = ip; n_in += 1
            else:
                extra_in += 1
        if n_in == 0:
            return None, "stage not traceable", None
        stages.append((inst, out, chain_pin, side_pin, prev))
        prev = out
    # head segment sanity: every node of the segment that is a cell OUTPUT must have a
    # single input in the routed graph (a LUT1 buffer), else the AND/OR model is wrong
    bad = []
    for a, b, _, _ in I.arcs:
        if isinstance(b, tuple) and b[0] == "h" and T.is_output(b[1]):
            inst = T.pin_split(b[1])[0]
            n = sum(1 for p in back if T.pin_split(p)[0] == inst and not T.is_output(p)
                    and W(p, b[1]) is not None and not all(T.is_const(q) for q in back[p]))
            if n != 1:
                bad.append(inst)
    return I, stages, (sorted(set(bad)), extra_in)


def late_T(c, src, tail, v, fr_row):
    G = K._graph(c)
    sp = c["certs"].spec(src, [(src, 1)], two=1, noFr0=0 if fr_row else 1, stop0=1, sw={tail})
    sp["cut"] = set()
    best, cap = K._dists(G, sp, v, {(src, 1)})
    return best.get((src, 1))


def single(iv):
    return len(iv) == 1


def lrip(I, L, sides, v):
    """lo-sum of the shortest src -> node path that avoids the side taps (the matched
    ripple: head segment + every chain pin)."""
    succ, indeg, nodes = defaultdict(list), defaultdict(int), {L}
    for a, b, ivd, _ in I.arcs:
        succ[a].append((b, ivd[v][0])); indeg[b] += 1; nodes |= {a, b}
    order, ready = [], [L]
    while ready:
        n = ready.pop(); order.append(n)
        for m, _ in succ[n]:
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
    d = {L: 0}
    for n in order:
        if n not in d:
            continue
        for m, lo in succ[n]:
            if n == L and m in sides:
                continue
            if d[n] + lo < d.get(m, 10 ** 12):
                d[m] = d[n] + lo
    return d


def settled(tz, T, Lr):
    """Settled on [A, T + Lr): ONE interval reaching the matched rise."""
    return len(tz) == 1 and tz[0][1] >= T + Lr


def exact_row(I, L, v, T, tail_key):
    S = propagate(I.arcs, L, v, T)
    return S, S.get(tail_key, [])


def stage_margin(I, L, stages, S, v, T):
    ivd = {(a, b): iv[v] for a, b, iv, _ in I.arcs}
    best = None
    for inst, out, cp, sp_, prev in stages:
        if sp_ is None or prev is None or cp is None:
            continue
        prevS = S.get(("o", prev), [])
        if not prevS:
            continue
        tap = ivd.get((L, ("p", sp_)))
        tap2 = ivd.get((("p", sp_), ("o", out)))
        r1 = ivd.get((("o", prev), ("p", cp)))
        r2 = ivd.get((("p", cp), ("o", out)))
        if None in (tap, tap2, r1, r2):
            continue
        m = (T + tap[0] + tap2[0]) - (prevS[0][0] + r1[1] + r2[1])
        best = m if best is None else min(best, m)
    return best


def emit_all(c, which):
    T, edges, back = c["T"], c["edges"], c["back"]
    chains = T.find_chains(edges)
    side = T.chain_side_arcs(edges)
    ffside, frside = T.fastfall_side_arcs(edges), T.fastrise_side_arcs(edges)
    by_base = defaultdict(set)
    for (s_, d_), base in side.items():
        by_base[base].add(s_)
    proj = {r[0]: r for r in T.audit_fastfall(edges, back, chains, c["timing"])}
    for base in sorted(by_base):
        fr_row = base.endswith(".uack")
        links = chains.get(base, [])
        head, tail = T.chain_endpoints(edges, back, links)
        srcs = by_base[base]
        row = {"base": base, "kind": "FR" if fr_row else "FF", "n": len(links)}
        pr = proj.get(base)
        if pr is not None and pr[5] is not None:
            row["ruleF"] = {"t_flush": pr[2], "t_reuse": pr[3], "guard": pr[4], "margin": pr[5]}
        if len(srcs) != 1 or tail is None:
            row["skip"] = f"side taps from {len(srcs)} nets / no tail"
            ROWS.append(row)
            continue
        src = next(iter(srcs))
        sideset = frside if fr_row else ffside
        I, stages, info = chain_dag(c, base, src, links, sideset)
        if I is None:
            row["skip"] = stages
            ROWS.append(row)
            continue
        row["head_multi_input"], row["extra_in"] = info
        L = ("launch", src)
        tail_key = ("o", tail)
        row["v"] = {}
        sides = {("p", sp_) for _, _, _, sp_, _ in stages if sp_ is not None}
        for v in c["VARIANTS"]:
            Lr = lrip(I, L, sides, v).get(tail_key)
            Tv = late_T(c, src, tail, v, fr_row)
            if Tv is None:
                row["v"][v] = {"skip": "no path back to src"}
                continue
            S, tz = exact_row(I, L, v, Tv, tail_key)
            ok = settled(tz, Tv, Lr)
            # least passing T (monotone in T, see module doc)
            lo_, hi_ = 1, max(Tv, 1)
            if not ok:
                hi_ = Tv
                while True:
                    hi_ *= 2
                    if settled(exact_row(I, L, v, hi_, tail_key)[1], hi_, Lr) or hi_ > 10 ** 7:
                        break
                lo_ = Tv
            while lo_ < hi_:
                mid = (lo_ + hi_) // 2
                if settled(exact_row(I, L, v, mid, tail_key)[1], mid, Lr):
                    hi_ = mid
                else:
                    lo_ = mid + 1
            ms = stage_margin(I, L, stages, S, v, Tv)
            tb = exact_row(I, L, v, max(lo_ - 1, 1), tail_key)[1]
            why = ("gap" if len(tb) > 1 else "empty" if not tb else
                   "short(end<T+Lrip)" if tb[0][1] < max(lo_ - 1, 1) + Lr else "?")
            row["v"][v] = {"T": Tv, "Lrip": Lr, "pass": ok, "tail": tz, "Tstar": lo_,
                           "margin_exact": Tv - lo_, "margin_stage": ms, "binding": why,
                           "fallback": sum(fb for *_, fb in I.arcs)}
            d = dump_net(I, L, sides, tail_key, v)
            d.update({"base": base, "kind": row["kind"], "var": v, "T": Tv, "py": row["v"][v]})
            DUMP.append(d)
        ROWS.append(row)
    wire_di(c)
    if "U" in which:
        rule_Fu(c)


WIRE = {}


def wire_di(c):
    """H_WIRE_DI (O4): every route that copies one net to a reading pin lags >= 1 tick.
    Checked over EVERY routed INTERCONNECT arc of the graph (a superset of the fork
    req_out / join ack_out / mux ctl_ack / snk ack / DELAY=0 link nets O4 names): per
    variant, the number of arcs whose lower bound is 0 ps, with examples."""
    T = c["T"]
    G = K._graph(c)
    for v in c["VARIANTS"]:
        n, zero, ex, mn = 0, 0, [], None
        for s_, d_, iv in G.arcs:
            if T.pin_split(s_)[0] == T.pin_split(d_)[0] and not T.is_output(s_):
                continue                      # a cell arc, not a route
            if T.is_const(s_):
                continue                      # tie-off: never switches
            n += 1
            lo = iv[v][0]
            mn = lo if mn is None else min(mn, lo)
            if lo == 0:
                zero += 1
                import re as _re
                si, sp_ = T.pin_split(s_); di, dp = T.pin_split(d_)
                key = (_re.sub(r"[\[\]0-9]+", "#", si.split(".")[-1]) + "/" + sp_ + " -> " +
                       _re.sub(r"[\[\]0-9]+", "#", di.split(".")[-1]) + "/" + _re.sub(r"\d+", "#", dp)
                       + (" [fallback]" if K._W(c, s_, d_) is not None and c["ivl"](s_, d_, K._W(c, s_, d_))[1] else ""))
                ex.append(key)
        cnt = {}
        for k in ex:
            cnt[k] = cnt.get(k, 0) + 1
        WIRE[v] = {"routes": n, "zero_lo": zero, "min_lo": mn,
                   "kinds": sorted(cnt.items(), key=lambda x: -x[1])[:40]}


def rule_Fu(c):
    """rule Fd (tcheck/rules10k.py) mirrored for the FASTRISE `uack` lines."""
    T, edges, back = c["T"], c["edges"], c["back"]
    seg, Inst, ivl = c["segment"], c["Inst"], c["ivl"]
    chains = T.find_chains(edges)
    frside = T.fastrise_side_arcs(edges)
    side_by_base = defaultdict(list)
    for (s_, d_) in frside:
        side_by_base[T.RE_LINK.match(T.pin_split(d_)[0]).group("base")].append((s_, d_))
    inputs_of, output_of = defaultdict(list), {}
    for p in set(edges) | set(back):
        inst = T.pin_split(p)[0]
        if not T.RE_LINK.match(inst):
            continue
        if T.is_output(p):
            output_of[inst] = p
        else:
            inputs_of[inst].append(p)
    W = lambda a, b: K._W(c, a, b)  # noqa: E731
    for base in sorted(side_by_base):
        meta = {"rule": "Fu", "ctl": base}
        links = chains.get(base, [])
        head, tail = T.chain_endpoints(edges, back, links)
        srcs = {s_ for s_, _ in side_by_base[base]}
        if len(srcs) != 1 or tail is None:
            meta["skip"] = "side taps from several nets or no tail"
            c["meta"].append(meta)
            continue
        src = next(iter(srcs))
        I = Inst(f"Fu {base} n={len(links)}")
        L = ("launch", src)
        prev, ok, pairs = None, True, []
        for i, inst in enumerate(links):
            out = output_of.get(inst)
            if out is None:
                ok = False
                break
            n_in, side_pin, chain_pin = 0, None, None
            for ip in inputs_of.get(inst, ()):
                arc = W(ip, out)
                if arc is None:
                    continue
                if (src, ip) in frside:               # the side tap: controlling 1 (OR)
                    iv, fb = ivl(src, ip, W(src, ip)); I.add(L, ("f", ip), iv, fb)
                    iv, fb = ivl(ip, out, arc); I.add(("f", ip), ("fo", out), iv, fb)
                    n_in += 1
                    side_pin = ip
                elif prev is not None and prev in back.get(ip, ()):
                    chain_pin = ip
            if n_in == 0 and i == 0:                  # the head: src -> its input(s)
                ins = [ip for ip in inputs_of.get(inst, ()) if W(ip, out) is not None]
                rh = seg(I, "h", L, src, set(ins), set())
                for ip, k in rh.items():
                    iv, fb = ivl(ip, out, W(ip, out)); I.add(k, ("fo", out), iv, fb)
                    n_in += 1
            if n_in == 0 and prev is not None and chain_pin is not None:   # ripple only
                iv, fb = ivl(prev, chain_pin, W(prev, chain_pin)); I.add(("fo", prev), ("f", chain_pin), iv, fb)
                iv, fb = ivl(chain_pin, out, W(chain_pin, out)); I.add(("f", chain_pin), ("fo", out), iv, fb)
                n_in += 1
            if n_in == 0:
                ok = False
                break
            if side_pin is not None and prev is not None and chain_pin is not None:
                iv, fb = ivl(prev, chain_pin, W(prev, chain_pin))
                I.add(("fo", prev), ("fc", chain_pin), iv, fb)
                pairs.append((("fc", chain_pin), side_pin, 1))
            prev = out
        if not ok:
            meta["skip"] = "stage not traceable"
            c["meta"].append(meta)
            continue
        if not pairs:
            meta["skip"] = "no side-tapped stage after the head"
            c["meta"].append(meta)
            continue
        sp = c["certs"].spec(src, [], two=1, noFr0=0, stop0=1, sw={tail})
        sp["cut"] = set()
        meta["stages"] = len(pairs)
        K.emit_pairs(c, I, L, sp, pairs, meta)
