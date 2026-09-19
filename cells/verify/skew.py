#!/usr/bin/env python3
"""skew.py -- rule E: does the request really arrive after the data?

That is the whole bundled-data contract and it is the only rule here.  What
makes it worth a separate file from tighten.py is WHERE it is checked and WHAT
it is checked against.

WHERE.  Not every channel.  A bundled-data request arriving ahead of its own
data is normal and harmless almost everywhere, and cells/rtl/bd_link.v says so
in its header at length: req_out is the C-element node itself, one arc from
req_in, while data_out is that node driving a latch, so two arcs.  The request
LEADS by a latch arc by construction, about 152 ps measured, and it grows with
pipe depth.  It is harmless because every consumer of a link output is a
TRANSPARENT LATCH that closes at ack-fall, a full phase later -- nothing
samples the request edge, so a value trailing its own request is still caught.

Two consumers in the library are not transparent latches:

  bd_steer   req0 = req . ~s     req1 = req . s
  bd_mux     j0 = C(x_req, ctl_req . ~s)   j1 = C(y_req, ctl_req . s)

Both are gates that ACT on the request edge, and what they act on is chosen by
`s`.  If the request reaches the gate before `s` has settled there, the request
is steered down the branch `s` used to name, and a token leaves on the wrong
wire.  That is an irreversible mis-steer, and it produces a MISSING result, not
a wrong one -- nothing computes an incorrect value, a token simply goes
somewhere nobody is waiting for it.  These sites, and only these sites, are
what this file measures.  They come from tighten.py's select_consumers(), which
finds them from the netlist's structure rather than from instance names.

WHAT AGAINST.  An earlier version of this file compared the request's LAST NET
HOP against the data's whole net, and reported 30 violations.  Those numbers
were meaningless: the request had already traversed a ten-element matched delay
chain, some 2.7 ns, that the comparison never counted.  Two arrivals are only
comparable if they are measured from a COMMON LAUNCH POINT.

So each site is measured as an ordinary static timing check.  Launch at a
state node -- a latch or C-element output, the same set tighten.py refuses to
walk through -- and take, for every state node that reaches both pins:

    t_req = SHORTEST path from that node to the gate's request pin
    t_sel = LONGEST  path from that node to the gate's select pin
    margin = t_req - t_sel        must be > 0

Shortest on the request and longest on the select because the check has to hold
in the worst case: the request as early as it can be, the select as late.  The
launch node is usually the feeding bd_link's own C node, which is exactly where
the request and the data diverge -- one goes through rdly, the other through
the latch -- so the margin this prints is the real lead, chain included.

The one place a path MUST cross storage is the latch itself, and the reason is
that the latch is transparent, not edge-triggered.  Walk back from a select pin
and the first thing you meet is a bd_latch output, which is a state node -- a
LUT feeding its own input -- and tighten.py stops dead there, which is why a
naive common-launch search finds no shared node at all and reports nothing.
But when the C node rises the latch OPENS, and the value walks straight through
the en -> Q arc; the d input was already stable, held by the sender's own
contract.  So the select's arrival is taken as exactly three real terms

    launch -> the latch's enable pin,  +  the en->Q cell arc,  +  the net to
    the select pin

and never through the latch's d input or its own feedback pin, which is what
would turn this into an accumulated arrival from half the netlist.  No latch is
identified by name to do this: the launch simply cannot reach a latch's d pin
(other storage blocks the way), so taking the worst reachable input pin picks
the enable on its own.

Apart from that single deliberate hop, paths never pass through a state node,
so every path considered is acyclic.
The packer's constant drivers are excluded as launch points, for the reason
tighten.py's CONST_DRV comment gives: a net that never transitions cannot start
a timing path, but it fans out everywhere and would otherwise be the one
"common source" any two pins are guaranteed to share.

This file does NOT emit padding.  A violation here is a placement and routing
result, and the remedy is to keep a link's latch, its request output and its
consumer together -- not to bolt delay elements onto the request until the
number goes positive.  Padding costs latency on every transaction, it changes
the route that produced the measurement, and measured on gcd it does not even
converge.
"""

import json, math, sys, pathlib

_raw = sys.argv[1:]
VERBOSE = "-v" in _raw
# --select-pads <path> writes, as JSON, the ADDITIONAL bd_delay elements each
# violating site's own link needs: {"ulink_n151__0": 3, ...}.  That is the
# shape bdc/emit.py's BDC_SELECT_PADS already reads.
#
# It is written HERE and deliberately not by tighten.py's rule D, which offers
# the same file and must not be used for it.  Rule D says so itself: it is a
# SCREEN, one-sided by construction -- it assumes every input launches at t=0,
# so it cannot see matched delay already upstream in the request path, and on
# gcd it therefore calls 38 of 39 branches violations at a bd_steer whose
# request really arrives around 10 ns.  Driving a padding loop off that number
# pads almost every channel in the design.  Measured 2026-08-17, that is
# exactly what happened: BDC_SELECT_PAD 4 vs 32 -- 96 versus 768 delay elements
# -- produced a byte-identical failing mask on silicon and bought nothing.
#
# Rule E measures from a common launch and, on the route this was written
# against, found 2 of 118 gates short on gcd, 2 of 24 on ipow.  A loop driven
# off THIS file touches a handful of links.  That count is a property of a
# ROUTE, not of the design: re-checked 2026-08-22 on two fresh single-seed
# rebuilds of gcd_hw and one of ipow_ps, ALL 118 / 24 gates measured clean
# under this file AND under the completely unmodified original -- the citation
# above did not reproduce on either route tried, on any version of this file.
# Consistent with the rest of this project's own experience ("one route is a
# sample"): treat "2 of 118" as a historical measurement, not a live invariant
# to compare future routes against.
# --osc <instance-prefix> declares one instance, or its whole subtree, a
# free-running ring oscillator rather than a handshake -- the same flag and the
# same meaning as tighten.py's.  A ring is the ONE legitimate combinational
# cycle that stores nothing; verify/soak_top.v:130 has exactly one and says so
# ("It is also the one loop in this design that stores nothing").  Traversal
# here stops at storage, so a storage-free cycle has nothing to stop it -- see
# fwd()'s pass cap below for what that costs if it is not declared.
#
# This flag may ONLY name a ring that is genuinely free-running end to end.  It
# is not a way to silence a real bundling violation by declaring the cycle it
# lives on an oscillator.
OSC = []
while "--osc" in _raw:
    _i = _raw.index("--osc")
    OSC.append(_raw[_i + 1])
    del _raw[_i:_i + 2]
PADS = None
if "--select-pads" in _raw:
    _i = _raw.index("--select-pads")
    PADS = pathlib.Path(_raw[_i + 1])
    del _raw[_i:_i + 2]
_pos = [a for a in _raw if not a.startswith("-")]
SDF = pathlib.Path(_pos[0]) if _pos else (pathlib.Path(__file__).resolve()
                                          .parent.parent
                                          / "build/hw/gcd_hw/gcd_hw.sdf")

# tighten.py reads its own argv at import time; hand it the SDF we were given
# so its SDF-relative paths (the routed JSON, next to it) resolve the same way.
sys.argv = [sys.argv[0], str(SDF)]
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import tighten as T                                          # noqa: E402
from collections import defaultdict, OrderedDict                           # noqa: E402


class CombinationalCycle(Exception):
    """A cycle with no latch and no C-element on it, so nothing stops a walk.

    Everywhere in this library that is a real defect: a handshake node IS
    storage, and a loop of pure combinational logic holds no state and cannot
    settle.  The one deliberate exception is a free-running ring oscillator,
    which is what --osc exists to declare.
    """


K = 6          # storage crossings a path may make before it is a lap, not a path

# The guardband, and the whole reason this file does not reuse the review's
# max(0.2*t_data, 200 ps).  That constant is EYEBALLED -- it is a judgement
# call written into tighten.py's rule A, not a derivation, and it should not
# be laundered into one by dividing it by a delay element and quoting the
# quotient.
#
# There IS a measured number for the thing a guardband here is actually for:
# how far a real route on this part lands from what the SDF predicted.
# hw/README.md, five bd_delay ring oscillators spanning 18x in length, closed
# and counted on silicon:
#
#     measured = 0.975 x predicted, residuals +0.1% -8.5% -5.7% -6.3% +2.2%
#
# with no trend against length, so it is per-route scatter rather than a model
# error.  The common 0.975 cancels between the two arrivals being compared --
# both routes are on the same die -- and what does not cancel is the residual
# band.  The worst case for this check is the request as fast as scatter
# allows against the select as slow as it allows:
#
#     GUARD_LO * t_req  >  GUARD_HI * t_sel
#
# HOW THE BAND IS DERIVED FROM THOSE FIVE NUMBERS.  Until 2026-08-21 it was
# their min and max, 0.915/1.022, which is wrong in a specific way: the
# extremes of a five-sample draw are a sample RANGE, and using one as a bound
# asserts that a sixth route cannot land outside five you happened to see.
# The sixth route routinely will.  What answers the actual question -- how far
# out can a route land -- is a one-sided 95/95 normal TOLERANCE interval,
# k = 4.202 at n = 5:
#
#     mean -3.64%, s 4.556%, k*s 19.14%  ->  0.772 / 1.155
#
# about 2.5x the old band.  Normality on five points is itself an assumption;
# it is a better one than treating min/max as a bound, not a good one, and if
# more rings are ever closed this should be recomputed rather than kept.
#
# THE WIDE BAND IS FREE, WHICH IS WHY IT IS THE ONE SHIPPING.  It was measured
# before being adopted, over 24 routed designs (verify/rloc_sweep.sh, 4 placer
# seeds x 2 designs x 3 placement variants).  With RLOC_GROUP v2 clustering on
# -- a bd_link's C node in the same SLICE as its own latch -- v2 reports ZERO
# violations at every width from raw to 95/95, on all 8 of its routes, worst
# margin +170 ps on gcd and +951 ps on ipow.  Unclustered, the same designs
# need 22 links and 66 delay elements of padding at this width, and still miss
# by 1541 ps.  So the price of honesty here was paid by the placer, not by a
# LUT budget.  Do not narrow this band to make an unclustered design pass:
# that trades a real correctness margin for a placement the tool will give you
# for nothing.
#
# Three things this number is still NOT.  It was measured on bd_delay chain
# routes, and it is applied here to ordinary interconnect.  It is five
# samples, tolerance interval or not.  And the SDF's cell arcs are nextpnr's
# flat 124 ps model rather than the per-pin silicon arcs, so the arcs inside
# each arrival are the weaker half of it.  It is still the only term here with
# silicon behind it, which is why it is preferred to a rounder number that has
# none.
GUARD_LO = 0.772          # request may run this fraction of its predicted delay
GUARD_HI = 1.155          # select may run this multiple of its predicted delay


def main():
    if not SDF.exists():
        print(f"no routed SDF at {SDF} -- run ./flow.sh first", file=sys.stderr)
        return 2

    edges, celltype, n_io, n_ic = T.parse_sdf(SDF)
    print(f"rule E       {SDF}")
    print(f"             {n_io} cell arcs, {n_ic} routed net delays")

    # The same pin-permutation correction tighten.py makes, for the same
    # reason: INIT is in logical order, the SDF names physical pins, and a LUT
    # input the function ignores is not a timing path.
    dead, jpath = T.false_arcs(edges)
    if dead:
        before = len(T.storage_nodes(edges))
        for s in list(edges):
            edges[s] = [(d, w) for d, w in edges[s] if (s, d) not in dead]
        if len(T.storage_nodes(edges)) != before:
            print("             ABORT: pruning removed a feedback loop",
                  file=sys.stderr)
            return 2

    # Drop every arc that touches a declared oscillator, before anything walks
    # the graph.  Pruning here rather than inside fwd() keeps the ring out of
    # the storage census and out of the launch candidates too, so it cannot be
    # picked as the point two signals diverged from.
    if OSC:
        def on_ring(pin):
            inst = pin.rsplit("/", 1)[0]
            return any(inst == o or inst.startswith(o + ".") for o in OSC)
        cut = 0
        for src in list(edges):
            keep = [(d, w) for d, w in edges[src]
                    if not (on_ring(src) or on_ring(d))]
            cut += len(edges[src]) - len(keep)
            edges[src] = keep
        print(f"             --osc {' '.join(OSC)}: {cut} arc(s) excluded")
        if cut == 0:
            print("             WARNING: that prefix excluded nothing.  A flag "
                  "that silences no cycle is\n             either misspelt or "
                  "unnecessary; it is not a pass.")

    sites = T.select_consumers(jpath)
    if sites is None:
        print(f"             no routed netlist at {jpath} -- cannot map "
              f"logical ports to physical pins", file=sys.stderr)
        return 2

    stops = T.storage_nodes(edges)
    side_arcs = T.fastfall_side_arcs(edges)
    early_edges = {
        src: [(dst, delay) for dst, delay in links
              if (src, dst) not in side_arcs]
        for src, links in edges.items()
    }
    binc, srcs_of = defaultdict(list), defaultdict(set)
    for s, lst in edges.items():
        for d, w in lst:
            binc[d].append((s, w))
            srcs_of[d].add(s)

    # A storage cell's own feedback arc is the one edge no walk may take: it is
    # what makes the node hold, and following it turns every crossing walk into
    # a positive cycle.  Every OTHER input arc is real inside a transaction --
    # a latch opens on its enable, a C-element fires on its last input -- which
    # is exactly why the walk has to be allowed to cross storage at all.
    feed = {(o, ip) for o in stops
            for ip, _ in binc.get(o, ()) if o in srcs_of[ip]}

    def fwd(launch, longest):
        """Arrival tables from `launch`, ONE PER CROSSING COUNT.  Levels are
        kept apart deliberately.  Take the extremal over all of them and a
        longest path granted six crossings simply goes round the handshake
        loop and comes back -- measured, it reported 44 ns of arrival at a pin
        two cells away.  Inside one transaction each storage cell fires once,
        so the signal's real path is the one with the FEWEST crossings and the
        deeper levels are laps."""
        better = (lambda a, b: a > b) if longest else (lambda a, b: a < b)
        # Bellman-Ford's bound.  A shortest-path relaxation over positive
        # weights settles on its own, but a LONGEST-path one does not: on a
        # cycle whose arcs are all positive, every lap improves every node and
        # the loop below never runs out of frontier.  Traversal stops at
        # storage nodes, so any cycle containing one is safe -- which is every
        # handshake in the library.  A cycle that stores NOTHING has nothing to
        # stop it, and that is what a free-running ring oscillator is.
        #
        # Measured, before this cap existed: verify/soak_top.v has exactly one
        # such ring (line 130, "the one loop in this design that stores
        # nothing") and rule E ran for five minutes on a 535-arc design with
        # two select gates and had to be killed.  It was not slow, it was not
        # terminating, and as a gate in check.sh it would have hung the whole
        # check rather than failing it.
        #
        # No path can improve more than |pins| times without revisiting a node,
        # so exceeding that bound IS a positive cycle.  Say which pin, and say
        # what to do about it -- a hang teaches nothing.
        # `pred` is kept alongside `out`, ONE PER LEVEL, so the exact walk a
        # pin's arrival took can be replayed rather than guessed at.  A node's
        # predecessor is (level, node) -- almost always the same level, except
        # a stop `o` seeded at the top of a new level, whose predecessor is
        # the enable pin `ip` back in the PREVIOUS level's table (the single
        # deliberate hop this docstring describes).  The launch's own entry
        # at level 0 has predecessor None; nothing else does, since every
        # other node was relaxed from something.
        cap = len(edges) + 1
        walked_edges = edges if longest else early_edges
        out, pred_out = [], []
        seeds, seed_pred = {launch: 0}, {launch: None}
        for lvl in range(K + 1):
            tab, pred = dict(seeds), dict(seed_pred)
            frontier = list(seeds)
            passes = 0
            while frontier:
                passes += 1
                if passes > cap:
                    raise CombinationalCycle(sorted(frontier)[0])
                nxt = []
                for pn in frontier:
                    tv = tab[pn]
                    for d, w in walked_edges.get(pn, ()):
                        if (pn, d) in feed:
                            continue
                        if d not in tab or better(tv + w, tab[d]):
                            tab[d] = tv + w
                            pred[d] = (lvl, pn)
                            # Record an arrival back at the launch, but never EXPAND
                            # from it.  The old condition was "d not in stops or
                            # d == launch", and that second clause is a lap: it lets
                            # the walk leave the launch, go round the launch's own
                            # handshake loop, and set off again with a larger number,
                            # forever, because every arc is positive and this is a
                            # LONGEST-path relaxation.  Levels are kept apart precisely
                            # so laps land at a deeper crossing count instead; the
                            # clause quietly readmitted them at level 0.
                            #
                            # Measured: rule E on verify/soak_top.v -- 535 arcs, two
                            # select gates -- ran five minutes and had to be killed.
                            # Not slow: not terminating.  As a gate in check.sh that
                            # would have hung the check rather than failing it.
                            if d not in stops:
                                nxt.append(d)
                frontier = nxt
            out.append(tab)
            pred_out.append(pred)
            seeds, seed_pred = {}, {}
            for o in stops:
                if o == launch:
                    continue
                for ip, arc in binc.get(o, ()):
                    if (o, ip) in feed or ip not in tab:
                        continue
                    v = tab[ip] + arc
                    if o not in seeds or better(v, seeds[o]):
                        seeds[o] = v
                        seed_pred[o] = (lvl, ip)
            if not seeds:
                break
        return out, pred_out

    def path_to(pred_out, level, node):
        """The exact walk from `launch` to `node` at `level`, as a list of
        (level, node) pairs, launch first.  Reconstructed from `fwd`'s own
        predecessor pointers -- not a proxy over what is merely backward-
        reachable, the concrete route that pin's arrival time came from."""
        chain = [(level, node)]
        seen = {(level, node)}
        p = pred_out[level].get(node)
        while p is not None:
            # A predecessor CYCLE is possible and must be caught here.  The
            # longest-path relaxation is bounded by Bellman-Ford's cap, not by
            # acyclicity, so on a loop that stores nothing -- a free-running
            # ring -- the pointers it leaves behind can close on themselves.
            # A pipeline cannot do this (soak_top.v has exactly one such ring;
            # gcd has none), which is why this walked fine on every compiled
            # design and hung only on soak: unguarded, the loop below appends
            # forever.  Measured, it reached 10.4 GB in under seven minutes
            # against 15.8 MB and 1.2 s for the same design before divergence
            # tracking existed.
            #
            # Report NO usable prefix rather than a guess.  The caller then
            # takes t_c = 0, which guards the whole launch-to-pin span -- the
            # conservative direction, and exactly what this check did before
            # divergent-tail guarding was added.  Degrading to the stricter
            # behaviour is safe; inventing a prefix here would not be.
            if p in seen:
                return None
            seen.add(p)
            chain.append(p)
            lvl, nd = p
            p = pred_out[lvl].get(nd)
        chain.reverse()
        return chain

    def divergence(out_f, pred_f, e, rp, out_t, pred_t, l, sp):
        """X, the last (level, node) the two MEASURED walks -- the shortest
        one that actually set the req arrival, the longest one that actually
        set the sel arrival -- still agree on, and t_c, its arrival time.
        Which table t_c is read from does not matter: a true shared prefix is
        one physical route, and both relaxations added up the same arc
        weights to reach it, so they agree by construction up to the exact
        point this comparison stops -- no proxy, the concrete routes
        `fwd`'s own predecessor pointers recorded."""
        pr = path_to(pred_f, e[1], rp)
        ps = path_to(pred_t, l[1], sp)
        if pr is None or ps is None:
            return 0          # cycle in the pointers: guard the whole span
        n = 0
        for a, b in zip(pr, ps):
            if a != b:
                break
            n += 1
        if n == 0:
            return 0
        xlvl, xnode = pr[n - 1]
        return out_f[xlvl][xnode]

    def back(pin):
        """Pins that reach `pin`, and how many storage crossings away."""
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

    def at(levels, pin):
        for k, tab in enumerate(levels):
            if pin in tab:
                return tab[pin], k
        return None

    # Pair each request pin with the select pin ON THE SAME LUT.  A bd_steer's
    # two branches are one fractured LUT6_2 and a bd_mux has two joins;
    # pairing across cells would compare a request at one gate against a
    # select at another and mean nothing.
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

    # Bounded cache.  fwd() returns arrival tables AND predecessor tables, one
    # per crossing level, and rule E walks up to four candidate launches per
    # gate.  Held unbounded across every gate that is gigabytes on a design
    # with many distinct launches -- soak was OOM-killed at 10.8 GB resident.
    # A gate needs at most its own 4 launches x 2 directions = 8 live entries,
    # so a cap well above that keeps all the reuse that matters and bounds the
    # footprint.  Evict oldest-first.
    CACHE_MAX = 64
    cache, rows, orphan = OrderedDict(), [], []
    for kind, parent, cell, rp, sp in checks:
        br, bs = back(rp), back(sp)
        # The launch is where the request and the select DIVERGE, and the
        # SELECT is what anchors it: the launch is the storage node that
        # released the select's value, the nearest one, and the request is then
        # measured from that same node.  Anchoring on the request instead picks
        # the steer's own join C-element -- zero crossings to the request pin,
        # four to the select -- which is not a divergence point at all but the
        # handshake loop coming back around.
        cand = sorted((bs[q], br[q], q)
                      for q in set(br) & set(bs)
                      if q in stops and not T.is_const(q))
        # Keep the WORST candidate launch, and guard only the DIVERGENT tails.
        #
        # These are two separate things and only the second one changed here.
        #
        # (1) Launch selection stays "worst over cand[:4]", as it always was.
        # An earlier revision of this file narrowed it to the nearest valid
        # launch, on the theory that a shared prefix cancels in the raw
        # subtraction so the choice could not matter.  That is false, and
        # measurably so: on gcd it moved the raw margin on 90 of 118 gates, by
        # as much as +15509 ps, always in the permissive direction.  The reason
        # is the one this file's own header already gives -- the launch is the
        # feeding bd_link's C node, "exactly where the request and the data
        # diverge", because that node drives the latch enable on one side and
        # the request chain on the other.  The nearest candidate is instead the
        # LATCH OUTPUT, which the request never travels through at all; it is
        # backward-reachable from the request pin only by going around the
        # handshake loop.  Measured on gcd's umux10.uj0: from the C node the
        # request is 0 storage crossings away and the select is 1, which is the
        # real picture, while from the latch the request comes back 4 crossings
        # and 19926 ps later -- about 15.2 ns of margin that is a lap of the
        # loop, not slack.  Across gcd that change made the request cross MORE
        # storage on 90 gates and fewer on none, which is the signature.  This
        # is exactly the failure the comment below the ABORT warns about.
        #
        # (2) The GUARDED margin now spans only the divergent tails.  It used
        # to be GUARD_LO*t_req - GUARD_HI*t_sel over the whole launch-to-pin
        # distance, including the prefix both legs share.  That prefix is ONE
        # physical delay drawing ONE sample of the PVT scatter these constants
        # model, so scoring it at 0.772x on the request leg and 1.155x on the
        # select leg at the same time guards a corner silicon cannot reach.
        # Subtracting the arrival at the divergence point removes it from both
        # legs, where it cancels.  This is a small, safe correction: measured
        # alone on gcd it moves the raw margin on 0 of 118 gates (mechanically
        # -- t_c cancels in a subtraction) and leaves the worst guarded gate
        # unchanged at +529 ps.  t_c comes from divergence(), which replays the
        # actual predecessor chains that set each arrival and takes their
        # longest common prefix, so it can only credit nodes genuinely on both
        # measured paths -- a backward-reachability proxy was tried first and
        # did over-credit (usteer got t_c=417 where the true value is 0).
        #
        # Worst is chosen by the GUARDED margin, since that is the verdict.
        worst = None
        for _, _, launch in cand[:4]:
            for d, lng in ((0, False), (1, True)):
                key = (launch, lng)
                if key in cache:
                    cache.move_to_end(key)
                else:
                    try:
                        cache[key] = fwd(launch, lng)
                        while len(cache) > CACHE_MAX:
                            cache.popitem(last=False)
                    except CombinationalCycle as e:
                        print(f"\n  ABORT: the walk from {launch} did not settle.")
                        print( "         A longest-path relaxation over positive arcs "
                               "terminates only if every")
                        print( "         cycle it can reach is broken by storage.  One "
                               "here is not.  Still")
                        print(f"         relaxing at: {e.args[0]}")
                        print( "         Every handshake in this library puts a latch or "
                               "a C-element on its")
                        print( "         loop, so this is a real defect unless it is a "
                               "free-running ring")
                        print( "         oscillator -- declare that with --osc <instance>, "
                               "and only if it")
                        print( "         genuinely runs free end to end.")
                        print( "         Rule E did not run.  This is a gap, not a pass.")
                        return 2
            out_f, pred_f = cache[(launch, False)]
            out_t, pred_t = cache[(launch, True)]
            e = at(out_f, rp)
            l = at(out_t, sp)
            if e is None or l is None:
                continue
            # X, the DIVERGENCE POINT: the last node the two walks that
            # actually set req's and sel's arrival still agree on, found by
            # replaying fwd()'s own predecessor pointers back from each pin to
            # `launch` and taking the longest common prefix of the two
            # concrete routes -- not a proxy over what is merely backward-
            # reachable from both pins, which can include nodes never on
            # either measured path.  t_c is X's arrival time; never let it
            # exceed either pin's own arrival, since X sits strictly before
            # both on their own walks by construction.
            tc = min(divergence(out_f, pred_f, e, rp, out_t, pred_t, l, sp),
                     e[0], l[0])
            g = GUARD_LO * (e[0] - tc) - GUARD_HI * (l[0] - tc)
            if worst is None or g < worst[0]:
                worst = (g, e[0] - l[0], launch, e[0], e[1], l[0], l[1], tc)
        if worst is None:
            orphan.append((kind, parent, cell))
            continue
        rows.append((worst[1], kind, parent, cell, rp, sp) + worst[2:])

    # Guarded margin, and the raw one kept alongside it so the guardband can
    # always be seen doing its work rather than being folded into the verdict.
    #
    # Only the DIVERGENT tail past t_c (the shared-prefix arrival computed
    # above) gets the asymmetric scatter; t_c itself is one shared physical
    # delay and drops out of the margin untouched.  GUARD_LO and GUARD_HI
    # model silicon PVT scatter on a signal's OWN path; a delay common to
    # both req and sel cannot run 0.772x on one leg and 1.155x on the other
    # at the same time, so guarding it in both directions at once was scoring
    # an impossible corner, not a real one -- see the cand[:4] comment above
    # for how t_c is found.  This also makes the guarded margin a function of
    # where req and sel actually split, not of how far back the search
    # happened to walk to find a common launch: t_c already backs out
    # whatever headroom launch selection alone could have bought.
    def guarded(t_req, t_sel, t_c):
        return int(GUARD_LO * (t_req - t_c) - GUARD_HI * (t_sel - t_c))

    rows = [(guarded(r[7], r[9], r[11]),) + r for r in rows]
    rows.sort()
    bad = [r for r in rows if r[0] <= 0]

    t_elem = T.measure_delay_element(SDF.read_text())
    if t_elem is None:
        t_elem = T.T_DELAY_RISE_FALLBACK
        elem_src = (f"no bd_delay chain in this design to measure -- falling "
                    f"back to {t_elem} ps/link off another route")
    else:
        elem_src = (f"{t_elem} ps per bd_delay link, measured off this route's "
                    f"own chains")

    print(f"             {len(checks)} select gates, {len(rows)} measured, "
          f"{len(bad)} violated")
    print(f"             guardband {GUARD_LO:.3f}*req vs {GUARD_HI:.3f}*sel, "
          f"from hw/README.md's five measured rings")
    print(f"             element cost: {elem_src}")
    if orphan:
        print(f"             {len(orphan)} gate(s) share no launch with their "
              f"own select within {K} crossings -- not checked")

    pads, unattributed = {}, []
    for (gm, margin, kind, parent, cell, rp, sp,
         launch, t_req, k_req, t_sel, k_sel, t_c) in (rows if VERBOSE else bad):
        flag = "VIOLATED" if gm <= 0 else "ok      "
        print(f"\n  {flag} {kind} {parent}")
        print(f"           launch {launch}")
        print(f"           divergence point {t_c} ps in (shared, not guarded)")
        print(f"           req  {rp}")
        print(f"                earliest {t_req} ps, {k_req} storage crossing(s)")
        print(f"           sel  {sp}")
        print(f"                latest   {t_sel} ps, {k_sel} storage crossing(s)")
        print(f"           margin {margin:+d} ps raw, {gm:+d} ps guarded"
              + ("   the request beats its own select" if gm <= 0 else ""))
        if gm > 0:
            continue
        # WHICH link's knob moves this edge.  The launch is the storage node
        # that released the select, and for every violation seen so far that
        # node IS a bd_link's own C-element output -- which is precisely the
        # node bd_link's DELAY pads, and it pads req_out ALONE (bd_link.v:99),
        # leaving data_out where it is.  So padding the link named by the
        # launch moves the request later and does not drag the select along
        # with it.  Anything else is not attributable from this measurement and
        # is reported rather than guessed at.
        m = T.RE_SEL_LINK.search(launch)
        if not m:
            # Fall back to the structural form, which finds the same knob on an
            # instance that is not named ulink_* -- see RE_SEL_LINK_STRUCT.
            m = T.RE_SEL_LINK_STRUCT.search(launch)
        if not m:
            unattributed.append((parent, launch))
            continue
        # The elements being added sit in the request path, so they are subject
        # to the same GUARD_LO scatter as the rest of it.
        need = math.ceil(-gm / (t_elem * GUARD_LO))
        pads[m.group(1)] = max(pads.get(m.group(1), 0), need)
        print(f"           fix: {need} more bd_delay element(s) on "
              f"{m.group(1)} ({t_elem} ps ea, derated to "
              f"{int(t_elem * GUARD_LO)})")

    if unattributed:
        print()
        for parent, launch in unattributed:
            print(f"  {parent}: launch {launch} is not a bd_link C node, so no "
                  f"DELAY knob\n    is attributable to it -- reported, not "
                  f"padded")
    if PADS is not None:
        PADS.write_text(json.dumps(dict(sorted(pads.items())), indent=1) + "\n")
        print(f"\n  wrote {len(pads)} per-link requirement(s) to {PADS} "
              f"-- ADDITIONAL elements, to be added to what each link carries")

    if bad:
        print(f"\n  {len(bad)} site(s) take the request before the select is "
              f"stable.  A token\n  leaves on the branch the select USED to "
              f"name -- a MISSING result, not a wrong one.")
        print("  The cause is placement, every time.  On gcd this site's own "
              "link spends 900 ps\n  getting from its C node to its OWN latch's "
              "enable -- two LUTs of one cell --\n  and another 1050 ps "
              "reaching the mux, while the first element of the same\n  link's "
              "delay chain sits 150 ps away.  Nothing declares that net "
              "critical, so\n  the placer, minimising wirelength over the whole "
              "design, has no reason to care.")
        print("  Padding is therefore a correction, not a cure: it costs "
              "latency on every\n  transaction through the gate and it changes "
              "the very route that was measured.\n  Per-link and measured it is "
              "worth trying -- a handful of LUT1s perturbs little.\n  If the "
              "loop does not converge, the answer is to make the placer keep a "
              "link's\n  C node and its latch in one slice, which is a packing "
              "decision, not a pinned\n  location.")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
