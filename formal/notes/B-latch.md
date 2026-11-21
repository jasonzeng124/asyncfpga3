# B-latch: probe 6a, the LUT latch (`bd_latch`, `bd_latch_rst`)

File: `formal/lean/Formal/Cells/Latch.lean` (core Lean, imports only
`Formal.Cells.Prelim`; no new shared defs needed).

Check (clean, ~1.4 s, no `sorry`/`admit`/`axiom`/`native_decide`):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/Latch.lean

The file ends with `#print axioms` for the main theorems: only `propext` and
`Quot.sound` appear.

## What is proved

All statements use the real INITs from `cells/rtl/bd_latch.v` evaluated by
Prelim's `lutB`/`lutK`/`o5K`/`o6K`/`muxTree`, with the real pin maps.

### Part 1: the functions (exhaustive, `decide`)
- `pair_o5_bin`, `pair_o6_bin`: for all 32 binary inputs, O5 of
  `64'hFF33_CC00_B8B8_B8B8` (pins d0,en,q0,d1,q1,1) is `en ? d0 : q0` and O6 is
  `en ? d1 : q1`. Each output ignores the other bit's pins: the pair is two
  independent latches.
- `odd_bin`: odd-bit LUT6 `B8B8..` with I3..I5 = 0 is `en ? d : q`.
- `rst0_bin`, `rst1_bin`: `00B8..`/`FFB8..` with rst on I3: rst = 1 forces 0/1,
  rst = 0 is the latch.
- `pair_o5_kleene`, `pair_o6_kleene`, `odd_kleene`: for ALL 3^5 Kleene
  inputs, the closure semantics equals `K3.mux en q d` (en = x gives q if q = d,
  else x). Independence therefore also holds under X: an X on the other bit's
  d or q never reaches this bit.
- `rst0_kleene`, `rst1_kleene`: `lutK RSTv [d,en,q,rst,0,0] = K3.mux rst (K3.mux en q d) v`.
- `pair_o5_muxTree`, `pair_o6_muxTree`: the same equations hold under the
  per-mux reading of H_KLEENE_LUT (`muxTree`, Prelim's I0-at-root order), so
  the Kleene claims below do not depend on closure vs mux-tree for that order.
  (Other physical input orders not checked; see "missing".)

### Part 2: Kleene corollaries
- `no_hazard_en_x`: en = X with d = q = v gives v on both outputs. Covers the
  closing edge and the opening edge with d = q (the INIT contains the
  consensus term, no static hazard).
- `closed_contains_dx`: en = 0, d = X: output = q (X on d is contained).
- `en_x_d_ne_q_is_x`: en = X, d ≠ q (both definite): output X. The latch is
  metastable-capable on a setup violation; nothing in the cell resolves it.
- `rst_forces`: rst = 1 forces the reset value even with d, en, q all X.
- `rst_x_closed`: rst = X while closed is harmless iff q equals the reset
  value; otherwise X.

### Part 3: timing (ℕ time, traces `ℕ → K3`; binary = no x)
Model of one bit (`LatchBit L`): `q t = o5K PAIR [d t, en t, p t, d1 t, p1 t, 1]`
at the LUT pins, and the feedback pin `p t = q (t - k t)` with
`LoopDelay L`: `H_LOOP_MIN : 1 ≤ k t`, `H_LOOP_MAX : k t ≤ L` (bounded pure
delay, allowed to vary per tick). The other bit's pins are arbitrary traces.
- `holds_value` (main): window `[s, T]`. Hypotheses
  `H_EN_OPEN` (en definitely 1 on `[s, s+L)`) and `H_DATA` (d = v whenever en
  is not definitely 0). Conclusion: q = v on the whole window. Reading:
  **setup** = d stable for at least the loop delay L before en starts to fall
  (so the loop is full of v when the mux switches to it); **hold** = d stable
  while en is not yet fully 0 at the LUT pin (the x window of the edge). While
  en = 0, d is free (may be X). Reopening with d = v is also covered.
- `holds_value_bin`: the binary phrasing with a close time `te`: en = 1 on
  `[te-L, te)`, 0 after; d = v on `[te-L, te)`; then q = v on `[te-L, T]`.
- `LoopDelay.widen`: a `LoopDelay L'` with `L' ≤ L` is a `LoopDelay L`, so data
  stable for the slow-corner loop delay suffices for every faster loop.
- Counter-traces (concrete, checked by `decide` against the gate relation
  `relOK` on a finite horizon, constant loop delay):
  - `ct1_hold_violation` (binary, L = 1): en falls at the pin at tick 4, the
    sender's next value (t→f) reaches d at tick 3. The latch closes on the
    NEW value and holds f: a silent wrong token.
  - `ct2_hold_violation_x` (Kleene, L = 1): d changes during the en edge
    (en = x at tick 4): q = X from tick 4 and the loop keeps it.
  - `ct3_setup_violation` (L = 2): d becomes valid only 1 tick (< L) before
    the close; the loop stores the last two samples and q circulates f,t,f,t
    (wrong at tick 4). A real loop would partly filter that pulse inertially;
    the model's point is that the stored state is not a single value.
  - `ok_setup_met`: same en, d valid L = 2 ticks before close: holds t (the
    counter-traces are not an artefact of `relOK`).
- Bridge to `bd_link` (`hold_of_dack`, `link_latch_holds`): with the C node
  falling at `tc`, `H_EN_FANOUT` (this bit's en pin is 0 from `tc+E`),
  `H_RELEASE` (data at the pin is still v before `tc+A+R`: A = earliest ack
  fall at the sender incl. the DACK chain, R = earliest sender-to-pin data path)
  and `H_RULE_H : E ≤ A + R`, the hold part of `H_DATA` follows, and the latch
  bit holds v. This is exactly the bd_link.v note "ack_in FALLS BEFORE THE
  LATCH HAS CLOSED": the enable net reaches its last latch ~1125 ps after its
  first, so E is large; DACK raises A until rule H holds (verify/tighten.py
  rule H). `ct1` is the failure when E > A + R (e.g. tc = 0, E = 4, A + R = 3).
  Note also LIBRARY.md's point that the window ends at ack↓, not req↓: in
  pin terms the obligation is "until en has fallen at THIS latch's pin".
  **Scope (audit REPORT row 21, findings B #6):** `hold_of_dack` is a
  one-line `omega` lemma about a SINGLE close/transaction (`H_RELEASE` fixes
  `d = v` for every `t < tc + A + R` from time 0). It does not cover a stream
  of transactions. The windowed, per-transaction form on a routed netlist is
  `OnNetlistTimed2.latch_rule_h_net` (B-on-netlist-timed2.md).

## Hypotheses (named) and how to test them
- H_KLEENE_LUT (Prelim): closure semantics of the LUT; checked here to agree
  with the per-mux tree reading (one input order). Test: GLS/board with a slow
  edge on en and d = q.
- H_LUT_LUMPED (doc comment in the file): the pin-to-O5 arc is a pure delay
  folded into the loop; q is the output shifted in time. Ignores the LUT's
  inertial filtering and any per-pin arc differences. Test: routed SDF arcs
  I1→O5 vs I0→O5 vs I2→O5.
- H_LOOP_MIN / H_LOOP_MAX (`LoopDelay`): loop delay in `[1, L]` ticks.
  Test: prjxray slow-max of the O5 arc + q→I2 route; routed GLS.
- H_EN_OPEN, H_DATA (setup/hold), H_EN_FANOUT, H_RELEASE, H_RULE_H (link):
  hypotheses of the theorems, sized on the route by tighten.py rules H/L.

## What did not work / is missing
- Everything attempted checks. Not done:
  - The O6 bit's timing theorem is not restated (symmetric: replace
    `pair_o5_kleene` by `pair_o6_kleene`; ~10 min). Odd and rst variants also
    only at the function level, not the trace level.
  - The model has no inertial filtering in the loop, so `ct3` shows a
    circulating pulse forever; physically it may die out or resolve to either
    value (metastability). Needs the inertial/involution channel (track 3).
  - Delay of the d/en paths into the pins is outside the bit model (traces are
    at the pins); only the link bridge adds them, as plain arithmetic bounds.
  - `muxTree` checked only for Prelim's I0-at-root order; the silicon order
    (I5 at the root of a LUT6_2, O5 tapped below it) not checked. Cheap to add
    once MuxTree.lean defines reorderings.
  - Not yet ported to shard A's Core trace/channel definitions.

## Verdict
**Works.** Functions (binary + Kleene, all inputs, real INITs), the Kleene
hazard/containment facts, and a timing theorem with a derived setup/hold
window plus concrete counter-traces all check in core Lean in about 1.4 s.
Effort to finish (O6/odd/rst trace-level, other mux orders, port to Core):
~0.5 day. Adding an inertial loop channel to say what a violated latch
resolves to: 1-3 days, depends on track 3. What it buys: the latch cell's
correctness reduced to two named, route-measurable conditions (setup ≥ loop
delay before en leaves 1; data stable until en is 0 at this pin), which are
exactly what rules L and H check; DACK's sizing rule `E ≤ A + R` is proved to
be sufficient for the hold side of a single transaction (`hold_of_dack`; the
windowed form is `OnNetlistTimed2.latch_rule_h_net`).

## Fidelity per primitive
- LUT6_2 / LUT6: real INIT and pin map; binary = exact truth table. Kleene =
  hypothesis H_KLEENE_LUT (closure), cross-checked against one mux-tree order.
  No delay inside the LUT model; its arc is lumped into the loop (H_LUT_LUMPED);
  no glitch/runt filtering.
- Feedback wire: bounded pure delay `[1, L]` ticks, variable per tick;
  no R/C, no inertial filtering, no pass-transistor pip distinction.
- en edge: a finite window of `x` at the pin (Kleene); d likewise.
- Time: ℕ ticks; any ps grain.
