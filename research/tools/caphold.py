#!/usr/bin/env python3
"""caphold.py SOAK_SDF [--tco-min PS] -- the HOLD side of every memory load's capture latch (bdc_load_cap's `ucap`), as
routed: does the RAM's read data stay until the capture has closed?

Why a tool of its own.  The capture latch (bdc/mem.py CAPTURE) is open while ~done & ~z_ack and closes when `done`
rises: done -> ucapen (LUT2) -> its fanout net -> each latch LUT.  The word it holds is the RAM's DOADO, which changes
only on the port's NEXT rising clock edge.  Rule H (cells/verify/tighten.py) has no model of a RAM output: until
2026-11-19 its latch pattern did not even recognise `ucap` as a latch, read each capture LUT as a controller, and
reported 100-625 ps "hold violations" between unrelated paths (37 071 rows on the farm's routes, every one 'unfixable').
With the pattern fixed, rule H has no row for the capture at all (its enable comes through ucapen from `done`, not
from a storage node directly) -- so this measures the race the rule cannot see.

The race, from one event (done rising):
  close  = LONGEST path done -> ucapen -> latch LUT enable pin, + the latch LUT's longest arc to its output;
  change = a LOWER BOUND on the next DOADO change reaching a latch D pin:
           sp(done -> CLK)            any CLK edge after done needs this path (the claim drops: upr, the arbiter, R0,
                                      DSETUP, the clock buffer); the first edge it carries is the FALL;
         + sp(CLK -> CLK)             the next RISE needs the whole return to zero and a new grant: CLK -> DCO line
                                      -> ack -> arbiter -> R0 -> DSETUP -> CLK (the arbiter is four-phase on R0 / A0);
         + T_CO                       the RAM's clock-to-out, as the SDF gives it (or --tco-min);
         + sp(DOADO -> D pin)         the read data's wire into the latch.
  sp = shortest path over EVERY arc of the graph, storage nodes passed through as if they fired on that input alone
  (a C-element or the arbiter can only fire later than that), fast-fall and fast-rise side arcs included: each term
  is a lower bound, so `change` is one, and margin = change - close - guard is a lower bound on the hold margin.
  guard = rule H's own (max(50, 3 %) of the close path).
One analysis, one corner: every delay is the SDF's (corner_audit's soak.sdf at its band); --tco-min overrides T_CO
alone, for a reading with the RAM at the fast end of its own band.
Output: one line per capture station: station, RAM, close, the four terms, margin; last line the worst."""
import argparse, heapq, re, sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "cells" / "verify"))
import tighten as T  # noqa: E402

RE_CAP = re.compile(r"^(.*)\.ucap\.(?:pair\[\d+\]|odd)\.u(?:\$LUT[56])?$")


def sp_from(edges, srcs, limit=None):
    """Shortest arrival from any of srcs (dict pin -> t0) over every arc; storage passed through."""
    dist = dict(srcs)
    h = [(t, p) for p, t in srcs.items()]
    heapq.heapify(h)
    while h:
        t, p = heapq.heappop(h)
        if t > dist.get(p, float("inf")) or (limit is not None and t > limit):
            continue
        for q, w in edges.get(p, ()):
            nt = t + w
            if nt < dist.get(q, float("inf")):
                dist[q] = nt
                heapq.heappush(h, (nt, q))
    return dist


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sdf")
    ap.add_argument("--tco-min", type=int, default=None, help="T_CO in ps in place of the SDF's CLK -> DO arc")
    a = ap.parse_args()
    edges, back, stops = T.routed_graph(Path(a.sdf))
    timing = T.Timing(edges, stops)
    pins = set(edges) | {d for l in edges.values() for d, _ in l}
    stations = defaultdict(set)                       # station prefix -> its ucap LUT instances
    for p in pins:
        m = RE_CAP.match(T.pin_split(p)[0])
        if m:
            stations[m.group(1)].add(T.pin_split(p)[0])
    worst = None
    if not stations:
        print("caphold: no capture latch (bdc_load_cap ucap) in this design")
        return
    for st in sorted(stations):
        insts = stations[st]
        done = [p for p in pins if T.pin_split(p)[0] == st + ".udone" and T.is_output(p) and p in stops]
        capen = [p for p in pins if T.pin_split(p)[0] == st + ".ucapen" and T.is_output(p)]
        if len(done) != 1 or len(capen) != 1:
            print(f"{st}: no single udone / ucapen output ({done} / {capen}) -- not measured")
            continue
        done, capen = done[0], capen[0]
        en_pins = {q for q, _ in edges.get(capen, ()) if T.pin_split(q)[0] in insts}
        # data pins: latch inputs driven (through at most the route) by a RAM read-data pin
        d_pins = {}
        for i in insts:
            for p in pins:
                if T.pin_split(p)[0] != i or T.is_output(p) or p in en_pins:
                    continue
                drv = [s for s in back.get(p, ()) if re.search(r"/DO[AB]DO\d+$|/DOP[AB]DOP\d+$", s)]
                if drv:
                    d_pins[p] = drv
        if not en_pins or not d_pins:
            print(f"{st}: enable pins {len(en_pins)}, RAM data pins {len(d_pins)} -- not measured")
            continue
        rams = sorted({T.pin_split(s)[0] for drv in d_pins.values() for s in drv})
        late = timing.late(done)
        close = max(late[p] + max((w for q, w in edges.get(p, ()) if T.is_output(q)), default=0)
                    for p in en_pins if p in late)
        guard = max(50, round(0.03 * close))
        sp_done = sp_from(edges, {done: 0})
        best = None
        for ram in rams:
            clk = ram + "/CLKARDCLK"
            drv = sorted(back.get(clk, ()))
            if len(drv) != 1 or drv[0] not in sp_done:
                print(f"{st}: {clk} driven by {drv}, reached from done: {[d in sp_done for d in drv]}")
                continue
            cd = drv[0]                                   # the clock net's one driver (bd_mem's buffer): the DCO
            t1 = sp_done[cd] + dict(edges[cd])[clk]       # line reads the same net, so the cycle runs from it
            # the shortest way back to the clock net's driver: the DCO line, the arbiter, R0, DSETUP (never through
            # the RAM itself: its clock-to-out arcs are the data, not the cycle)
            e2 = {s: [(d, w) for d, w in lst if T.pin_split(d)[0] != ram] for s, lst in edges.items()}
            sp_clk = sp_from(e2, {q: w for q, w in e2.get(cd, ()) if T.pin_split(q)[0] != ram})
            t2 = sp_clk.get(cd)
            if t2 is None:
                print(f"{st}: no way from {cd} back to itself")
                continue
            for p, drv in d_pins.items():
                for s in drv:
                    if T.pin_split(s)[0] != ram:
                        continue
                    tco = a.tco_min if a.tco_min is not None else dict(edges.get(clk, ())).get(s)
                    if tco is None:
                        continue
                    wire = dict(edges.get(s, ())).get(p)
                    if wire is None:
                        continue
                    ch = t1 + t2 + tco + wire
                    if best is None or ch < best[0]:
                        best = (ch, ram, t1, t2, tco, wire, p)
        if best is None:
            print(f"{st}: no path done -> CLK -> CLK found -- not measured")
            continue
        ch, ram, t1, t2, tco, wire, p = best
        margin = ch - close - guard
        print(f"{st:<32} {ram.split('.')[-2]:<28} close {close:>5}  change >= {ch:>6} = "
              f"done->CLK {t1:>5} + CLK->CLK {t2:>5} + T_CO {tco:>5} + DO->D {wire:>5}  guard {guard:>3}  "
              f"margin >= {margin:>6}")
        if worst is None or margin < worst[0]:
            worst = (margin, st)
    if worst:
        print(f"worst capture hold margin (lower bound): {worst[0]} ps at {worst[1]}")


if __name__ == "__main__":
    main()
