# placekeep: keeping the previous route's placement between the sizing loop's finish routes (2026-11-19 / 20)

Research bot, session cluster-research-29671222-1. nextpnr 6e5d224472232d5d (cells/verify/toolchain.sh all ok).
Why: research/data/converge/notes.txt -- a re-route moves every constraint's margin by sd ~0.5 ns even where none of
its lines changed, and 95 % of the rows short on a finish route were not short before; its open lead was "an
incremental placement keeping the previous route's cells". Status: **opt-in, NOT a default**
(cells/hw/build_bench.sh BD_PLACE_FROM, cells/hw/place_from.py, research/tools/auto/auto_size.sh AUTO_PLACE_KEEP=1).

## What works
- A --pre-place script binds every matched cell to its previous bel at STRENGTH_FIXED (USER: the router then does not
  permute the bound LUTs' pins, 55 site wires stay overused; STRONG: the post-place repair moves 681 cells).
- test_bool_array s1 it 5 -> 6 (3 new LUTs; a fresh re-route moved 6051 of 6136 shared cells): 6130 kept, routed, rule
  CLEAN, margin change of the 16 sized constraints whose lines did not change sd 95 ps (fresh 221).
- xorshift s1 (suite12's loop, its finish phase resumed locally at it 5 = the farm's own route bed7ecfa):
  - matcher v1 (names only, 1fd98f586): the kept placement held on 1 of 3 steps; that step (it 7) was rule-CLEAN,
    P 19.59 ns, EQUIVALENT;
  - matcher v2 (f4747b20b): it 6 kept 6990 of 7533 cells, **rule-CLEAN at it 6, P 18.11 ns, EQUIVALENT, ffmux-clean**.
  The farm's fresh finish phase on the same loop: 4, 4, 4, 2, 2 short rows at it 6-10, never clean (shipped it 9,
  NOT CLEAN, P 17.81).
  - it 5 -> 6 margin change of unchanged-line constraints: fresh median |d| 282 ps, p5 -552 (n 122); everything kept
    median 122, p5 -332, p95 +930 (n 154); the kernel alone kept (BD_PLACE_ONLY=^bridge_i\.udut\.) 196 / -541.
  - both kept routes decode EQUIVALENT with fasm_equiv (the LUT pin restoration writes consistent bitstreams).

## What does not (yet)
- **Names are not stable across routes outside the kernel.** yosys numbers abc's cells and every $auto$ object from
  one counter: when a kernel's size changes, the harness's names shift (xorshift: +4 on the abc run, carry chains +4,
  and 104 of 1910 flops renumbered), and a reused number names ANOTHER cell (xorshift it 6's
  $auto$ff.cc:337:slice$9999 shares no neighbour with it 5's). Binding by such names put flops of other control sets
  into one slice (nextpnr "post-placement validity check failed for Bel ..A5FF (no cell)"). matcher v2: names with no
  counter, abc by its index relative to the run, then the output nets' user names, then structure (the one previous
  cell of the type whose low-fanout nets hold all its matched neighbours, with their ports). On gather the abc
  numbering is not a pure offset (680 abc cells unmatched) and 1481 of 8360 cells stay new.
- **Routing after a kept placement fails on 3 of 4 kernels**: countloop s1 (it 6, 7: router2 8 overused wires),
  iterative_division s1 (it 6), gather s1 (it 6, 7; reproduced by hand: nextpnr segfaults after the pre-place script,
  1481 new cells). Each such step falls back to a fresh build (logged), so the loop never breaks, but nothing is gained.
- The LUT input pins: the router permutes them per route and the packer starts every LUT1 on A1, so a kept LUT5 / LUT6
  pair (or a constant tie in a kept carry slice) starts on one shared pin; the constant router does not swap a tie's
  pin. matcher v2 restores the previous route's pins on every kept LUT (port rewiring + X_ORIG_PORT).
- **Routes cannot be kept in this toolchain** (route_from.py here, not wired in): the routed JSON's ROUTING pip names
  for site pips and tile -> INT pips do not parse back through getPipByName (assertions pip != PipId(), first_dot):
  1575 of 8141 xorshift nets lockable; the binary's --fixed-routes loader segfaults even replaying a route on its own
  netlist (xs5.fr, 130 445 pips). The router re-routes every net, which is where the ~100-300 ps left comes from.

## Next, if taken up again
Make names deterministic at the source for a whole loop (an opt-in yosys `autoname` after synthesis: on xorshift it 5
vs it 6 all 5545 harness cell names then match, 5544 with identical type and parameters, against 1831 now), so the
matcher needs no structure; then re-run these four finish phases (state: research/tools/suite/finish_state.sh on
suite12 tasks 1, 8, 28, 31) against the farm's fresh ones. Check first that the rules read an autonamed netlist the
same way (rloc_stamp's v2 path does not use the '$' test; itercost/categorize.py does).
