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

import sys, pathlib

SDF = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else
                   pathlib.Path(__file__).resolve().parent.parent
                   / "build/hw/gcd_hw/gcd_hw.sdf")
VERBOSE = "-v" in sys.argv[1:]

# tighten.py reads its own argv at import time; hand it the SDF we were given
# so its SDF-relative paths (the routed JSON, next to it) resolve the same way.
sys.argv = [sys.argv[0], str(SDF)]
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import tighten as T                                          # noqa: E402
from collections import defaultdict                           # noqa: E402


K = 6          # storage crossings a path may make before it is a lap, not a path


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

    sites = T.select_consumers(jpath)
    if sites is None:
        print(f"             no routed netlist at {jpath} -- cannot map "
              f"logical ports to physical pins", file=sys.stderr)
        return 2

    stops = T.storage_nodes(edges)
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
        out, seeds = [], {launch: 0}
        for _ in range(K + 1):
            tab, frontier = dict(seeds), list(seeds)
            while frontier:
                nxt = []
                for pn in frontier:
                    tv = tab[pn]
                    for d, w in edges.get(pn, ()):
                        if (pn, d) in feed:
                            continue
                        if d not in tab or better(tv + w, tab[d]):
                            tab[d] = tv + w
                            if d not in stops or d == launch:
                                nxt.append(d)
                frontier = nxt
            out.append(tab)
            seeds = {}
            for o in stops:
                if o == launch:
                    continue
                for ip, arc in binc.get(o, ()):
                    if (o, ip) in feed or ip not in tab:
                        continue
                    v = tab[ip] + arc
                    if o not in seeds or better(v, seeds[o]):
                        seeds[o] = v
            if not seeds:
                break
        return out

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

    cache, rows, orphan = {}, [], []
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
        worst = None
        for _, _, launch in cand[:4]:
            for d, lng in ((0, False), (1, True)):
                key = (launch, lng)
                if key not in cache:
                    cache[key] = fwd(launch, lng)
            e = at(cache[(launch, False)], rp)
            l = at(cache[(launch, True)], sp)
            if e is None or l is None:
                continue
            m = e[0] - l[0]
            if worst is None or m < worst[0]:
                worst = (m, launch, e[0], e[1], l[0], l[1])
        if worst is None:
            orphan.append((kind, parent, cell))
            continue
        rows.append((worst[0], kind, parent, cell, rp, sp) + worst[1:])

    rows.sort()
    bad = [r for r in rows if r[0] <= 0]

    print(f"             {len(checks)} select gates, {len(rows)} measured, "
          f"{len(bad)} violated")
    if orphan:
        print(f"             {len(orphan)} gate(s) share no launch with their "
              f"own select within {K} crossings -- not checked")

    for (margin, kind, parent, cell, rp, sp,
         launch, t_req, k_req, t_sel, k_sel) in (rows if VERBOSE else bad):
        flag = "VIOLATED" if margin <= 0 else "ok      "
        print(f"\n  {flag} {kind} {parent}")
        print(f"           launch {launch}")
        print(f"           req  {rp}")
        print(f"                earliest {t_req} ps, {k_req} storage crossing(s)")
        print(f"           sel  {sp}")
        print(f"                latest   {t_sel} ps, {k_sel} storage crossing(s)")
        print(f"           margin {margin:+d} ps"
              + ("   the request beats its own select" if margin <= 0 else ""))

    if bad:
        print(f"\n  {len(bad)} site(s) take the request before the select is "
              f"stable.  A token\n  leaves on the branch the select USED to "
              f"name -- a MISSING result, not a wrong one.")
        print("  The remedy is placement: the producing link's latch, its "
              "request output and\n  this gate belong together.  Padding the "
              "request is latency on every single\n  transaction, and it "
              "changes the very route that produced this measurement.")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
