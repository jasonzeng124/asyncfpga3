#!/usr/bin/env python3
"""Probe C-10g front end, part 3 (UNTRUSTED): obligations the project rules do NOT
check, emitted from the real route (extract.py `--rules2 WR`).

W  8e's latch OPEN WIDTH (C-8e-endtoend.md, `H_LATCH` open width;
   race2 (req (j+2) ++ ack (j+1) ++ [(1,1)]) (en j b) 0).  Per link pair up -> ctl
   (up's controller requests ctl's, as in 10e's rule I): launch = the RISE of up.
   Data (must be early): up -> every enable pin of up's own latch bank (the enable
   wire must have shown the open phase at every bit).  Request (must be late): up's
   next FALL, lower-bounded by the round trip up -> ctl (rise, fast-fall taps off)
   -> up (ack) -> up's own LUT arc to its output (the "+1" of 8e).  A Muller C node
   falls on its LAST input, so taking the ack input alone is a lower bound (sound for
   the late side).  Same segment construction as 10e's I.
R  RT_FB, the C-element feedback race (C-10d-routed.md, C-8g, C-10f): per storage node
   o that is not a bd_latch bit (every C-element / handshake node in the design):
   launch = o's output edge.  Data (must be early): o's routed feedback wire(s) to its
   own LUT pin(s).  Request (must be late): the earliest response of the rest of the
   circuit to o's edge at ANY other input pin of o: the shortest path from o's output
   to such a pin, crossing anything (each storage node firing when first reached, a
   lower bound), feedback arcs of o excluded; chosen by Dijkstra on each of the sdf,
   fast and slow lower bounds and merged (min).  The project has no rule for this.
"""
import heapq
import math
from collections import defaultdict


def emit_all(c, which, ZERO, _emit):
    if "W" in which:
        rule_W(c, ZERO, _emit)
    if "R" in which:
        rule_R(c, ZERO, _emit)


def rule_W(c, ZERO, _emit):
    T, edges, timing = c["T"], c["edges"], c["timing"]
    seg, Inst, ivl, ff = c["segment"], c["Inst"], c["ivl"], c["ff"]
    ctls = c["controllers"]
    for up in ctls:
        if T.dc_link_of(up) is not None:
            continue
        en = T.latch_enables(edges, up)
        if not en:
            continue
        reach = timing.early(up)
        for ctl in ctls:
            if ctl == up or ctl not in reach or not T.latch_enables(edges, ctl):
                continue
            lab = f"W {T.pin_split(up)[0]} next={T.pin_split(ctl)[0]}"
            I = Inst(lab)
            L = ("launch", up)
            r1 = seg(I, "s1", L, up, {ctl}, ff)
            if ctl not in r1:
                continue
            r2 = seg(I, "s2", r1[ctl], ctl, {up}, ff)
            if up not in r2:
                continue
            I.req = r2[up]
            for p, w in en:
                iv, fb = ivl(up, p, w)
                I.add(L, ("en", p), iv, fb)
                I.data.add(("en", p))
            _emit(c, I, L, {"rule": "W", "ctl": T.pin_split(up)[0], "next": T.pin_split(ctl)[0],
                            "bits": len(en)})


def rule_R(c, ZERO, _emit):
    T, edges, stops, Inst, ivl = c["T"], c["edges"], c["stops"], c["Inst"], c["ivl"]
    W = lambda a, b: next((w for d, w in edges.get(a, ()) if d == b), None)  # noqa: E731
    for o in sorted(stops):
        inst = T.pin_split(o)[0]
        if T.RE_BD_LATCH.search(inst):
            continue
        fbs = [(d, w) for d, w in edges.get(o, ()) if not T.is_output(d) and T.pin_split(d)[0] == inst]
        if not fbs:
            continue
        fbset = {d for d, _ in fbs}
        targets = {p for p in set(c["back"]) if T.pin_split(p)[0] == inst and not T.is_output(p)
                   and p not in fbset}
        if not targets:
            continue
        I = Inst(f"R {inst}")
        L = ("launch", o)
        for d, w in fbs:
            iv, fb = ivl(o, d, w)
            I.add(L, ("fb", d), iv, fb)
            I.data.add(("fb", d))
        used = set()
        for j, v in enumerate(("sdf", "fast", "slow")):
            path = _dijkstra_any(edges, o, targets, fbset, inst, T,
                                 lambda a, b, w, v=v: ivl(a, b, w)[0][v][0])
            if path is None or tuple(path) in used:
                continue
            used.add(tuple(path))
            for x, y in zip(path, path[1:]):
                iv, fb = ivl(x, y, W(x, y))
                I.add(L if x == o else ("r", j, x), ("r", j, y), iv, fb)
            I.add(("r", j, path[-1]), ("resp",), ZERO, False)
            I.req = ("resp",)
        kind = "link C" if inst.endswith(".ctl.u.u") else "other"
        _emit(c, I, L, {"rule": "R", "ctl": inst, "kind": kind, "chains": len(used),
                        "fb_pins": sorted(T.pin_split(d)[1] for d in fbset)})


def _dijkstra_any(edges, start, targets, fbset, inst, T, wfun, limit=200000):
    best, prev, heap, n = {start: 0}, {}, [(0, start)], 0
    while heap:
        t, p = heapq.heappop(heap)
        if t > best.get(p, math.inf):
            continue
        if p in targets:
            path = [p]
            while path[-1] != start:
                path.append(prev[path[-1]])
            return path[::-1]
        n += 1
        if n > limit:
            return None
        # never leave through o's own instance again (that would be o itself)
        if p != start and T.pin_split(p)[0] == inst:
            continue
        for d, w in edges.get(p, ()):
            if d == start or (p == start and d in fbset):
                continue
            nt = t + wfun(p, d, w)
            if nt < best.get(d, math.inf):
                best[d] = nt; prev[d] = p
                heapq.heappush(heap, (nt, d))
    return None
