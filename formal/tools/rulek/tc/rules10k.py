#!/usr/bin/env python3
"""Probe C-10k front end (UNTRUSTED for the shapes; the late sides are checked
potentials): the capstone timing hypotheses no tcheck rule checked before, as
two-path races decided by tcheck's proved per-pair cert verdict
(`Tcheck.pverdict`, `pverdict_sound`).  Called from extract.py (`--rules10k FZX`).

Every instance: launch = one storage node's output edge at time 0 (node 0).
  data side (must be EARLY): a DAG of the routed arcs (10a, upper bounds), as in
                             every other rule;
  late side (must be LATE):  the whole cyclic routed graph seen through a phase
                             rule (`Tcheck.Late`, now with `cut`), bounded below
                             by a checked potential;
  pairs:                     (data node, target pin, phase): each data node must
                             precede ITS target only (not a cross product).

Fd  H_FF_DRAINED (C-10j; B's D2 "rule F, MISSING TERM").  Per fast-fall delay
    line (bd_delay_gated: s[i+1] = AND(s[i], gate)) and per stage j >= 1 with a
    side tap: stage j-1's FALL must have reached stage j's chain-input pin before
    the gate's NEXT RISE reaches stage j's side pin.  Then the AND sees a
    controlling 0 on its chain input when the side tap rises, and the stage rises
    only through the ripple (what every rise-side rule, and rule Z's `cut`, use).
    Data: rule F's stage falls (H_CONTROLLING: side tap alone), plus the hop
    stage j-1 output -> stage j chain pin.  Late: Fc's phase rule (falling wave to
    the tail, switch, then anything back to the gate source), target = (stage j's
    side pin, phase 1).  Rule F / Fc check stage j-1's fall at its OUTPUT against
    the gate's next change at its SOURCE; Fd adds hop_hi(j-1 -> j) and credits
    tap_lo(j).  So F is not sufficient for H_FF_DRAINED; Fd is.
Z   H_AMERGE_RTZ (C-8j), both cascade stages of the 3-input control_merge
    (C-8l's stage-1 race).  Per arbiter acknowledge C-element ua_k whose output
    reaches a consumer latch's D pin without crossing storage (the index
    `won = g2 | A_k` and the data mux read it): launch = the storage driver of
    A0 (z_ack of the cell, or stage 2's A1 for stage 1).  Data: A0 -> ua_k pin
    -> A_k (C-element crossing: it falls on A0, g_k having fallen before, H_GK_LOW)
    -> won/index/data LUTs -> consumer latch D pin -> latch output -> its own
    feedback pin (rule I's data endpoint).  Late: the earliest change of THAT
    consumer link's latch-enable pins over the whole graph (its latch closes only
    after its controller sees z_req), with the fast-fall side taps of the cell's
    own z_req line CUT (inert on R0's rise: H_FF_DRAINED, i.e. that line's Fd
    rows).  A PASS means the next token's z_req cannot close a consumer latch on
    a stale index: the stale-index run of C-8j cannot happen.
X   H_MUX_RTZ / B's X1 (mux uxa, uya; muxn ua_k) and B's A3 "pulse" (arbiter
    ua_k), one shape: an acknowledge C-element u = C(j, z) whose LAST enabling
    input is z (z falls after j by the protocol: j's fall is what makes z fall).
    The low pulse of z at u's pin must outlast u's own fall: z must not rise again
    at u's pin before u's output has fallen and reached its feedback pin.
    launch = the storage node D that drives z (through any non-storage LUTs, e.g.
    a link's DACK line).  Data: D -> z pin -> u output -> u's feedback pin(s).
    Late: z's NEXT edge at u's pin: phase 0 = the response to D's edge; a switch
    (p,0) -> (p,1) at every NON-feedback input pin p of D; phase 1 = D's next
    output edge and its route to u's pin.  Leaving D's feedback pins out of the
    switch is H_NEXT_EDGE: D's next edge needs a non-feedback pin change
    (Formal/Timing/FbFirstRt.lean `next_needs_input`, from LutFb + H_FB_FIRST of D
    (its Rc row) + `NoInv` of D's INIT).
"""
import heapq
import math
import re
from collections import defaultdict

INF = 10 ** 12


def emit_all(c, which):
    c["_root_cache"] = {}
    if "F" in which:
        rule_Fd(c)
    if "Z" in which:
        rule_Z(c)
    if "X" in which:
        rule_X(c)


# ---------------------------------------------------------------- the cert writer

def _graph(c):
    cc = c["cctx"]
    G = cc.get("_certG")
    if G is None:
        G = cc["_certG"] = c["certs"].CertGraph(cc)
    G.write(cc["out"])
    return G


def _dists(G, spec, v, targets, prev=None):
    """Dijkstra on the product graph (Tcheck.expand, with `cut`), stopped once
    every target is settled.  -> (best dict, cap) with cap = the largest settled
    target distance (INF if none is reachable)."""
    s = spec["s"]
    best = {(s, 0): 0}
    heap = [(0, 0, s, 0)]
    cnt, left, seen_t = 0, set(targets) - {(s, 0)}, []
    while heap and left:
        t, _, p, ph = heapq.heappop(heap)
        if t > best.get((p, ph), math.inf):
            continue
        if (p, ph) in left:
            left.discard((p, ph)); seen_t.append(t)
            if not left:
                break
        for (q, qh), lo in G.out_arcs(spec, p, ph, v):
            if (q, qh) == (s, 0):
                continue
            nt = t + lo
            if nt < best.get((q, qh), math.inf):
                best[(q, qh)] = nt
                if prev is not None:
                    prev[(q, qh)] = (p, ph)
                cnt += 1
                heapq.heappush(heap, (nt, cnt, q, qh))
    cap = max(seen_t) if seen_t else INF
    return best, cap


def emit_pairs(c, I, L, spec, pairs, meta, spec_v=None):
    """I: data DAG (launch L); pairs: [(data key, target pin, phase)]; spec: the
    late phase rule (certs.spec plus `cut`).  One instance per corner variant.
    The potential is min(dist, cap) with cap = the largest target distance: a
    valid potential for any cap (pot dst <= pot src + lo survives the min)."""
    G = _graph(c)
    f = c["cctx"]["out"]
    pairs = [(d, p, ph) for d, p, ph in pairs if p in G.id]
    if not pairs or not I.arcs:
        meta["skip"] = "no pair"
        c["meta"].append(meta)
        return False
    succ, indeg, nodes = defaultdict(list), defaultdict(int), {L}
    for a, b, _, _ in I.arcs:
        succ[a].append(b); indeg[b] += 1; nodes |= {a, b}
    order, ready = [], [L]
    while ready:
        n = ready.pop(); order.append(n)
        for m in succ[n]:
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
    if len(order) != len(nodes):
        raise RuntimeError(f"{I.label}: data side not a DAG")
    idx = {n: i for i, n in enumerate(order)}
    pairs = [(d, p, ph) for d, p, ph in pairs if d in idx]
    nfb = sum(fb for *_, fb in I.arcs)
    tg = {(p, ph) for _, p, ph in pairs}
    unreach = {}
    picks = {}
    spec0 = spec
    for vi, v in enumerate(c["VARIANTS"]):
        if spec_v is not None:
            spec, picks[v] = spec_v(v)
        else:
            spec = spec0
        prev = {} if v in ("slow", "slowG") else None
        best, cap = _dists(G, spec, v, tg, prev)
        if prev is not None:
            # report (evidence only): the critical late path to the first pair's target
            x = (pairs[0][1], pairs[0][2])
            path = []
            while x in prev:
                path.append(x); x = prev[x]
            path.append(x)
            insts = []
            for (pp, ph) in reversed(path):
                nm = pp.rsplit("/", 1)[0].replace("urig.udut.", "") + (":1" if ph else "")
                if not insts or insts[-1] != nm:
                    insts.append(nm)
            meta.setdefault("late_path", {})[v] = [best.get((pairs[0][1], pairs[0][2])), insts]
        unreach[v] = sorted(f"{p}:{ph}" for p, ph in tg if (p, ph) not in best)
        lst = [(G.id[p], ph, d) for (p, ph), d in best.items() if d < cap and (p, ph) != (spec["s"], 0)]
        f.write(f"inst {I.label} {v} fallback={nfb}/{len(I.arcs)}\n")
        f.write("setup 0\n")
        f.write("data " + " ".join(str(idx[d]) for d in sorted({d for d, _, _ in pairs}, key=idx.get)) + "\n")
        for a, b, ivd, _ in sorted(I.arcs, key=lambda x: (idx[x[0]], idx[x[1]])):
            lo, hi = ivd[v]
            f.write(f"arc {idx[a]} {idx[b]} {lo} {hi}\n")
        f.write("late %d %d %d %d %d %d\n" % (vi, G.id[spec["s"]], spec["two"], spec["noFr0"],
                                              spec["stop0"], spec["swStor"]))
        if spec["sw"]:
            f.write("sw " + " ".join(str(G.id[p]) for p in sorted(spec["sw"]) if p in G.id) + "\n")
        if spec["blocked"]:
            f.write("blocked " + " ".join(str(G.id[p]) for p in sorted(spec["blocked"])) + "\n")
        cut = sorted((G.id[a], G.id[b]) for a, b in spec.get("cut", ()) if a in G.id and b in G.id)
        for i in range(0, len(cut), 32):
            f.write("cut " + " ".join(f"{a} {b}" for a, b in cut[i:i + 32]) + "\n")
        for d, p, ph in sorted(pairs, key=lambda x: (idx[x[0]], x[1], x[2])):
            f.write(f"pair {idx[d]} {G.id[p]} {ph}\n")
        f.write(f"cap {cap}\n")
        for i in range(0, len(lst), 40):
            f.write("pot " + " ".join(f"{a} {b} {d}" for a, b, d in lst[i:i + 40]) + "\n")
        f.write("end\n")
    meta["label"] = I.label
    meta["pairs"] = len(pairs)
    if picks:
        meta["sw_pick"] = picks
    if any(unreach.values()):
        meta["unreachable_targets"] = unreach
    c["meta"].append(meta)
    return True


# ---------------------------------------------------------------- helpers

def _roots(c, pin, limit=4000):
    """Storage nodes reaching `pin` through non-storage nodes only (backwards);
    plus a flag: some backward path ends at a non-storage source (reset logic,
    a pad, a constant)."""
    key = pin
    if key in c["_root_cache"]:
        return c["_root_cache"][key]
    T, back, stops = c["T"], c["back"], c["stops"]
    roots, free, seen, work = set(), False, {pin}, [pin]
    while work and len(seen) < limit:
        p = work.pop()
        bs = back.get(p, ())
        if not bs and p != pin:
            free = True
        for s in bs:
            if T.is_const(s):
                continue
            if s in stops:
                roots.add(s)
                continue
            if s not in seen:
                seen.add(s); work.append(s)
    c["_root_cache"][key] = (roots, free)
    return roots, free


def _fb_pins(c, o):
    T, edges = c["T"], c["edges"]
    inst = T.pin_split(o)[0]
    return {d for d, _ in edges.get(o, ()) if not T.is_output(d) and T.pin_split(d)[0] == inst}


def _in_pins(c, inst):
    T = c["T"]
    return sorted(p for p in c["back"] if T.pin_split(p)[0] == inst and not T.is_output(p))


def _W(c, a, b):
    return next((w for d, w in c["edges"].get(a, ()) if d == b), None)


# ---------------------------------------------------------------- Fd

def rule_Fd(c):
    T, edges, back = c["T"], c["edges"], c["back"]
    seg, Inst, ivl = c["segment"], c["Inst"], c["ivl"]
    chains = T.find_chains(edges)
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
    W = lambda a, b: _W(c, a, b)  # noqa: E731
    for base in sorted(side_by_base):
        meta = {"rule": "Fd", "ctl": base}
        links = chains.get(base, [])
        head, tail = T.chain_endpoints(edges, back, links)
        srcs = {s for s, _ in side_by_base[base]}
        if len(srcs) != 1 or tail is None:
            meta["skip"] = "side taps from several nets or no tail"
            c["meta"].append(meta)
            continue
        src = next(iter(srcs))
        I = Inst(f"Fd {base} n={len(links)}")
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
                if (src, ip) in ffside:               # the side tap (rule F's H_CONTROLLING)
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
                # NEW (D2's missing term): the previous stage's fall AT this stage's chain pin
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
        sp = c["certs"].spec(src, [], two=1, noFr0=1, stop0=1, sw={tail})
        sp["cut"] = set()
        meta["stages"] = len(pairs)
        emit_pairs(c, I, L, sp, pairs, meta)


# ---------------------------------------------------------------- Z

def _latch_ctl(c):
    """latch LUT instance -> its controller (state node) and that ctl's enable pins."""
    if "_latch_ctl" in c:
        return c["_latch_ctl"]
    T, edges = c["T"], c["edges"]
    m = {}
    for ctl in c["controllers"]:
        en = T.latch_enables(edges, ctl)
        for p, _ in en:
            m[T.pin_split(p)[0]] = (ctl, sorted({q for q, _ in en}))
    c["_latch_ctl"] = m
    return m


def rule_Z(c):
    T, edges, stops = c["T"], c["edges"], c["stops"]
    seg, Inst, ivl, ff = c["segment"], c["Inst"], c["ivl"], c["ff"]
    lc = _latch_ctl(c)
    arbs = sorted({m.group(1) for s in stops
                   for m in [re.match(r"^(.*\.uarb\d+)\.ua[12]\.u$", T.pin_split(s)[0])] if m})
    for a in arbs:
        cm = a.rsplit(".uarb", 1)[0]
        cut = {(s, d) for (s, d) in ff if T.pin_split(d)[0].startswith(cm + ".udly.")}
        for k in (1, 2):
            ua = f"{a}.ua{k}.u"
            o = ua + "/O6"
            meta = {"rule": "Z", "ctl": f"{a}#{k}"}
            if o not in stops:
                continue
            fbs = _fb_pins(c, o)
            a0pins, a0drv = [], set()
            for p in _in_pins(c, ua):
                if p in fbs or _W(c, p, o) is None:
                    continue
                roots, _free = _roots(c, p)
                if roots and not any(T.pin_split(r)[0].startswith(a + ".") for r in roots):
                    a0pins.append(p); a0drv |= roots
            if len(a0drv) != 1 or len(a0pins) != 1:
                meta["skip"] = f"A0 not resolved (pins {a0pins}, drivers {sorted(a0drv)})"
                c["meta"].append(meta)
                continue
            D, p0 = next(iter(a0drv)), a0pins[0]
            # consumer latch D pins reached from A_k without crossing storage
            latch_pins = {p for p in c["back"] if not T.is_output(p) and T.RE_BD_LATCH.search(T.pin_split(p)[0])}
            I = Inst(f"Z {a}#{k} A0={T.pin_split(D)[0]}")
            L = ("launch", D)
            r0 = seg(I, "z0", L, D, {p0}, set())
            if p0 not in r0:
                meta["skip"] = "A0 route not walkable"
                c["meta"].append(meta)
                continue
            iv, fb = ivl(p0, o, _W(c, p0, o)); I.add(r0[p0], ("zo", o), iv, fb)
            rd = seg(I, "z1", ("zo", o), o, latch_pins, set())
            pairs = []
            for dp, dk in rd.items():
                li = T.pin_split(dp)[0]
                if li not in lc:
                    continue
                ctl, enp = lc[li]
                for lo_, w in edges.get(dp, ()):
                    if T.is_output(lo_) and T.pin_split(lo_)[0] == li:
                        iv, fb = ivl(dp, lo_, w)
                        I.add(dk, ("zq", dp, lo_), iv, fb)
                        for fbp, w2 in edges.get(lo_, ()):
                            if not T.is_output(fbp) and T.pin_split(fbp)[0] == li:
                                iv2, fb2 = ivl(lo_, fbp, w2)
                                I.add(("zq", dp, lo_), ("zfb", dp, fbp), iv2, fb2)
                                own = [e for e in enp if T.pin_split(e)[0] == li] or enp
                                for e in own:
                                    pairs.append((("zfb", dp, fbp), e, 0))
            if not pairs:
                meta["skip"] = "A_k reaches no consumer latch (no index/data reader)"
                c["meta"].append(meta)
                continue
            # keep only the data arcs that lead to a paired node
            sp = c["certs"].spec(D, [])
            sp["cut"] = cut
            meta.update(A0=D, cut=len(cut), consumers=sorted({T.pin_split(lc[T.pin_split(d[1])[0]][0])[0]
                                                             for d, _, _ in pairs}))
            emit_pairs(c, I, L, sp, pairs, meta)


# ---------------------------------------------------------------- X

RE_X = re.compile(r"^(.*)\.(u[xy]a|ua\d)\.u$")


def rule_X(c):
    T, edges, stops = c["T"], c["edges"], c["stops"]
    seg, Inst, ivl = c["segment"], c["Inst"], c["ivl"]
    for o in sorted(stops):
        ui = T.pin_split(o)[0]
        m = RE_X.match(ui)
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
            c["meta"].append({"rule": "X", "ctl": ui, "skip": f"z not resolved (pins {zp})"})
            continue
        p0 = zp[0]
        for D in sorted(zd):
            meta = {"rule": "X", "ctl": ui, "z": D, "roots": len(zd)}
            I = Inst(f"X {ui} z={T.pin_split(D)[0]}")
            L = ("launch", D)
            r0 = seg(I, "x0", L, D, {p0}, set())
            if p0 not in r0:
                meta["skip"] = "z route not walkable from this root"
                c["meta"].append(meta)
                continue
            iv, fb = ivl(p0, o, _W(c, p0, o)); I.add(r0[p0], ("xo", o), iv, fb)
            pairs = []
            for fp in sorted(fbs):
                iv, fb = ivl(o, fp, _W(c, o, fp)); I.add(("xo", o), ("xfb", fp), iv, fb)
                pairs.append((("xfb", fp), p0, 1))
            # D's handshake inputs (non-feedback, rooted in storage: not reset/constant)
            dfb = _fb_pins(c, D)
            cand = [p for p in _in_pins(c, T.pin_split(D)[0])
                    if p not in dfb and _W(c, p, D) is not None and _roots(c, p)[0]]
            if not cand:
                meta["skip"] = "z driver has no handshake input"
                c["meta"].append(meta)
                continue
            others = sorted(r for r in zd if r != D)
            G = _graph(c)
            base = c["certs"].spec(D, [], two=1)
            base["cut"] = set()

            def hs_inputs(r):
                rf = _fb_pins(c, r)
                return [p for p in _in_pins(c, T.pin_split(r)[0])
                        if p not in rf and _W(c, p, r) is not None and _roots(c, p)[0]]
            ocand = {r: hs_inputs(r) for r in others}

            def latest(v, pins):
                d0, _cap = _dists(G, dict(base, sw=set()), v, {(p, 0) for p in pins})
                fin = [(d0[(p, 0)], p) for p in pins if (p, 0) in d0]
                return max(fin)[1] if fin else pins[0]

            def spec_v(v, idle=False, cand=cand):
                # H_CEL_NEXT (FbFirstRt.cel_next_needs_all): D is a C-element, so its next
                # edge needs EVERY handshake input to change; switch at the input whose first
                # change is latest (any one is sound).  Other roots of an OR'ed z (a steer's
                # uack): X switches at their output's FIRST change (no hypothesis); Xi
                # assumes them at rest at the launch (H_OR_IDLE) and applies the same
                # C-element rule to them.
                pick = latest(v, cand)
                sw = {pick}
                for r in others:
                    if idle and ocand[r]:
                        sw.add(latest(v, ocand[r]))
                    else:
                        sw.add(r)
                return dict(base, sw=sw), pick
            meta.update(z_pin=p0, cand=len(cand))
            arcs0, data0 = list(I.arcs), set(I.data)
            emit_pairs(c, I, L, base, pairs, meta, spec_v=spec_v)
            if others:
                Ii = Inst(f"Xi {ui} z={T.pin_split(D)[0]}")
                Ii.arcs, Ii.data = arcs0, data0
                emit_pairs(c, Ii, L, base, pairs, dict(meta, rule="Xi", late_path={}),
                           spec_v=lambda v: spec_v(v, idle=True))
