# B-bundling (probe 6c): matched delay lines and the bundling condition

File: `formal/lean/Formal/Cells/Bundling.lean` (core Lean, imports only
`Formal.Cells.Prelim`, 742 lines, checks in about 3 s). It contains no sorry
or native_decide and declares no axioms. `#print axioms` on every main theorem
gives a subset of {propext, Classical.choice, Quot.sound}. The file uses Prelim's
`K3.admits`. Its own helper names avoid the word "admit".

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/Bundling.lean

Status: checks clean. No warnings, no errors.

## Model

- **Time and signals.** Time is ℕ and a signal is a `Sig := ℕ → Bool`. Before time 0 a signal holds its value at 0, which is what truncated `t - s` gives.
- **Pin window.** A LUT pin is `(net, lo, hi)`. `[lo, hi]` bounds the routed wire delay plus that pin's LUT arc (SDF INTERCONNECT + IOPATH). `winK` reads the net over `[t-hi, t-lo]`: it gives `t` or `f` if the net was constant over the window, and `x` otherwise.
- **Gate relation.** `Gate INIT pins y` says that y t = b whenever `lutK INIT (window readings) = b`. `lutK` is Prelim's Kleene closure (hypothesis H_KLEENE_LUT). When the closure is `x` the output is unconstrained, so glitches, runts and metastable levels are all allowed. A circuit is the conjunction of its gate relations.
- **Soundness (`transport_gate`, proved).** A fixed transport delay `d_i ∈ [lo_i, hi_i]` per pin satisfies `Gate`. The relation also covers per-edge (rise ≠ fall) and time-varying delays, because the output only ever reads inside the window. It does not cover an inertial channel whose rejection width is larger than the window. Nothing in this file uses that case.
- **Real constants.** All INITs are the real ones, evaluated by `lutK`:
  - LUT1 `2'h2`
  - LUT2 `4'h8` (FASTFALL)
  - LUT2 `4'hE` (FASTRISE)
  - latch LUT6 `B8B8…`
  - latch LUT6_2 `FF33_CC00_B8B8_B8B8`, with O5 = low 32 bits on I0..I4 and O6 with I5 = 1

  The file proves that each latch LUT equals the Kleene mux `en ? d : q` for all 3^k inputs (`odd_kleene`, `pair_o5_kleene`, `pair_o6_kleene`, by `decide`). It also proves the latch bridges `odd_latch`, `pair_o5_latch` and `pair_o6_latch`: a LUT satisfying `Gate` is a `LatchRel` for its bit, whatever the other bit's pins do.

## Theorems (all proved)

### Delay lines (`bd_delay`)

- **`sym_chain` / `sym_edge` (symmetric chain).** N LUT1 hops, each with window `[lo, hi]` (hop = wire + LUT).
  - If `a` holds `v` on `[T, T']`, then `z` holds `v` on `[T + N·hi, T' + N·lo]`.
  - Edge form: suppose `a` holds `u` on `[T0, T-1]` and `v` on `[T, T1]`. Then `z` holds `u` until `T - 1 + N·lo` and `v` on `[T + N·hi, T1 + N·lo]`. So for both polarities the edge reaches `z` between `N·lo` and `N·hi` after `a`.
  - Minimum pulse width: the `v` interval is non-empty iff `T1 - T ≥ N·(hi - lo)`.
- **`buf_pulse_lost` (counter-trace).** One stage with a pulse of width `w ≤ hi - lo`. The output that stays constant at the old value satisfies the relation, so the pulse can be swallowed. Physically this is a buffer whose arc for one edge is slower than its arc for the other by more than `w`.
- **FASTFALL and FASTRISE.** Proved once for a generic side INIT with a "fast value" `c`: AND/`4'h8` has c = 0 and OR/`4'hE` has c = 1. The structure `FastLine` holds the gate hypotheses plus three Kleene properties of the side INIT, which are proved by `decide`:
  - the fast value on the tap forces the output;
  - the fast value on the chain pin forces the output;
  - with the tap at the slow value, the stage passes the chain pin.

  `fastfall_line` and `fastrise_line` instantiate it with the real INITs. The theorems:
  - **`fast_edge`** (N ≥ 2). If `a` is at the fast value on `[T, T']`, `z` is at it on `[T + thi, T' + tlo]`. That is one tap hop (tap wire + LUT), whatever the chain is doing. For N = 1 the line is just a buffer, which `sym_edge` covers.
  - **`slow_not_early`** (the matched edge is not early). Suppose `a` is at the fast value on `[F, T-1]` and H_FLUSH holds: `2·hi + thi ≤ (T - F) + tlo`, a minimum width for the fast phase. Then every stage `i ≥ 1` holds the fast value until `T + i·lo - 1`, so `z` cannot take the slow value before `T + N·lo`.
  - **`slow_arrives`.** If `a` is at the slow value on `[T, T']`, stage `i` holds it on `[T + i·hi + thi, T' + min lo tlo]`. The slow edge therefore reaches `z` between `N·lo` and `N·hi + thi`. The upper bound is loose by `thi`.
- **`ff_counter` (counter-trace, short low pulse, FASTFALL).**
  - Setup: N = 3, bounds `[1, 2]`, transport with chain hops of 2 and taps of 1, and `a` low for one tick at 10.
  - Result: `z` rises at 12, one tick after `a` rose at 11. The matched minimum is 14. `z` then pulses low again, which is a glitch train on a request.
  - H_FLUSH fails on this trace.
- **`ff_counter_ruleF` (counter-trace aimed at rule F).**
  - Setup: chain bounds `[1, 3]` (hops of 3), taps of 1, and `a` low on `{10, 11}`.
  - Every stage output is already low at 11 and at 12, so the premise of tighten.py's rule F holds without the guard. Still, `z` rises at 13, one tap hop after `a` rose at 12, where the matched minimum is 15.
  - Cause: a 1 that stage 1 drove before it fell is still in flight on the 3-tick wire into stage 2 when the fast tap re-enables stage 2.
  - The exact per-stage requirement is `fall_i(latest, at output) + hop_hi(i→i+1) ≤ T + tap_lo(i+1)`. H_FLUSH is a uniform sufficient form of it.

### The latch and the bundling condition (`bd_link`, Muller controller)

One stage. The node `c` is the latch enable. It is taken as a clean pulse, high on `[Ton, Toff)` and low on `[Toff, Tnext)` (H_EN_CLEAN; the C-element is track 5). The sender's data net holds `v` on `[Td, Tnew)`. Each bit reads:
- `d` through `[dlo, dhi]`;
- `en` through `[elo, ehi]`, which is this bit's enable fanout wire plus the I1 arc;
- its own `q` through `[flo, fhi]`, which is the loop wire plus the I2 arc, with H_LOOP_POS `1 ≤ flo`.

**`capture` (proved).** Under the two conditions below, `q = v` on `[max(Ton+ehi, Td+dhi), Tnext + elo)`:

- **H_SETUP:** `max(Ton + ehi, Td + dhi) + fhi ≤ Toff + elo`
- **H_HOLD:** `Toff + ehi ≤ Tnew + dlo`

The proof is a case split on time:

1. **Transparent.** While the enable window is all 1 and `d` is settled, the output is `d`.
2. **Closing.** While the enable window is mixed (it reads `x`), the Kleene mux gives `v` only because `d = q = v` on both legs. This step needs H_KLEENE_LUT's consensus behaviour.
3. **Opaque.** Once the enable window is all 0, the loop carries `v`. This uses strong induction on time through the loop window.

How to read the two conditions:

- **H_SETUP is a condition on the enable FALL, not its rise.** The latest settling of the bit is its D-pin arrival plus the D arc, or the enable rise plus the I1 arc, whichever is later. Add one full loop window (loop wire plus the I2 arc). The total must come no later than the earliest arrival of the enable fall at that bit.
  - H_SETUP has two parts. The data part is `Td + dhi + fhi ≤ Toff + elo`. The pulse-width part is `Ton + ehi + fhi ≤ Toff + elo`: the enable's high phase at the bit must be longer than its own spread plus the loop.
- **H_HOLD:** the next value's earliest arrival through the D pin must be no earlier than the latest arrival of the enable fall.

Related results:

- **`setup_from_request`.** Suppose the node cannot rise before `Tr + Rlo` (H_REQ_LO: the sender's node rise plus the rdly chain's `N·lo` from `sym_edge` plus the C-element's req pin), and it stays high at least `W` (H_EN_WIDTH: the handshake round trip, track 8). Then H_SETUP follows from `Td + dhi + fhi ≤ Tr + Rlo + W + elo` together with `ehi + fhi ≤ W + elo`. So for a Muller link the request competes with the data only through the enable fall, a whole handshake (`W`) after the request.
- **`classic_implies_setup` and `setup_not_classic`.** "Data at the latch output before the latest enable-rise arrival" is the classic "request after data" condition, which is also `input_lead`'s premise. Together with the pulse-width part it implies H_SETUP. The converse is false.
- **`counter_rule_I` (counter-trace, transport, odd LUT6).**
  - Setup: D arc 1, en arc 1, loop = wire 2 + I2 arc 1. The enable is high on `[0, 10)`. Data rises to 1 at 8 and stays.
  - Rule I's inequality without the guard is `8 + 1 + 2 ≤ 10 + 1`. It holds with margin 0.
  - H_SETUP is `8 + 1 + 3 ≤ 11`. It fails.
  - Result: `q 11 = 0`. The loop is left circulating the pattern 1,1,0, so the token is corrupted.
- **`counter_rule_H` (counter-trace).**
  - Setup: D arc 0, en arc 2, loop 1. The sender releases data at 10, the instant the node falls.
  - H_HOLD (`12 ≤ 10`) fails, while H_SETUP holds.
  - Result: the still-transparent latch takes the released value, and `q 12 = 0`.

## Comparison with the repo's post-route rules

| derived | project rule | verdict |
|---|---|---|
| H_HOLD: `Tnew + (D wire + D arc)_min ≥ Toff + (en wire + en arc)_max` | **H** (tighten.py): `t_d` = earliest disturbance at the D *pin* (no D arc) ≥ `t_en` = enable wire + max arc of the en pin, + guard | **H is stronger** (more conservative) by the D-pin arc (min) plus the guard. Sound. |
| H_SETUP data part: `Td + D wire_max + D arc_max + loop wire_max + I2 arc_max ≤ Toff + (en wire + en arc)_min` | **I** (tighten.py): `t_data` = data at D pin + max D arc + `loop_wire` vs `t_close` = closing path + min enable wire + min en arc, + guard | **I is weaker** by one I2-pin arc (the feedback pin's own LUT arc). `counter_rule_I` is a trace that passes I's inequality at zero guard and corrupts. With nextpnr's flat 124 ps arcs and the guard `max(0.2·t, 200 ps)` ≥ 200 ps, the guard covers it numerically, but only by using up guardband meant for route scatter. Suggested fix: add `max arc of the q pin` to I's data side. I also audits only data that comes from an upstream link stage; data from pins or from outside is "not audited". |
| H_SETUP pulse part: `Ton + ehi + fhi ≤ Toff + elo` | none explicit | Not checked by any rule. In practice it is implied by the handshake round trip being much longer than one loop, but nothing states it. |
| classic "data before enable rise" | **A** (sender's request is the last output, from a common source, + guard) and `input_lead` | **A is a different and stronger condition.** It is sufficient (with the pulse part) but not necessary for a Muller link's latch, because that latch closes a whole handshake later. It is the right condition for an edge-sampling consumer. |
| — | **E** (skew.py): steer/mux select vs request at a combinational gate | Not the latch condition. E's consumer acts on the request edge, so its exact condition is the classic one at that gate. Not modelled here. |
| FASTFALL flush, per stage: `fall_i + hop_hi(i→i+1) ≤ T + tap_lo(i+1)` (H_FLUSH uniform form) | **F** (tighten.py `audit_fastfall`): latest stage-output fall ≤ earliest re-rise of the input, + guard | **F is weaker** by `hop_hi(i→i+1) - tap_lo(i+1)`: it misses a value still in flight on the chain wire. `ff_counter_ruleF` passes F's premise and the rise still skips the chain. Covered by the guard only when that wire-minus-tap difference is under the guard. |

## What did not work / not done

- The C-element is not modelled. The enable is a hypothesis (H_EN_CLEAN, H_REQ_LO, H_EN_WIDTH). Composing with track 5's C-element relation and with a sender model (track 8) would turn those into theorems.
- Exactness is shown only by boundary counter-traces, not by a general "violation ⇒ some bad trace" theorem. H_SETUP is tight at the boundary in `counter_rule_I` (one tick less passes, by `capture`). H_FLUSH is a sufficient uniform form, not the exact per-stage condition.
- `slow_arrives` has a loose upper bound (`N·hi + thi`).
- FASTRISE counter-traces are not written. They are the mirror of FASTFALL; the positive theorems cover both.
- `bd_delay_gated` (taps from `gate`) is not covered. Its premise "a is a buffered copy of gate" would be a hypothesis of the same shape.
- The pair LUT's O5 is modelled as `lutK (INIT % 2^32)` on five pins. That is Prelim's `o5K` semantics.

## Verdict

**Works.** The bundling condition comes out as a derived hypothesis (H_SETUP/H_HOLD) of a gate-level, relation-based model with real INITs. It is proved sufficient, and counter-traces in a sound transport instance show it cannot be weakened at the I2-arc or hold boundary.

Effort to finish: about 1–2 days.
- Compose with the C-element (track 5) to discharge H_EN_CLEAN and H_EN_WIDTH.
- Do a W-bit link with per-bit windows (a direct ∀-bit lift).
- Prove the exact per-stage flush condition.
- Possibly a general exactness theorem.

What it buys:
1. Rules H and I and the FASTFALL rule F are checked against a derivation. H is sound. I and F each have a concrete missing term: the I2-pin arc for I, and the chain wire vs tap arrival for F. Today only the guardband hides them.
2. It is the precise spec a verified timing checker (track 10) should implement.

## Fidelity per primitive

- **LUT.** A Kleene closure of the real INIT over per-pin delay windows (H_KLEENE_LUT). This is not the mux-tree level. Sibling MuxTree.lean relates the two, and Latch.lean proves that the mux-tree form agrees for the latch pair.
- **Glitches.** Allowed wherever the closure is `x`.
- **Timing.** The relation is sound for fixed and per-edge transport delays, and for drifting delays. It is not sound for inertial filtering wider than a window.
- **Routing wire.** A delay interval folded into the pin window (wire + arc). Testable against the SDF min/max at the corners. Silicon scatter of about ±19 % (GUARD_LO/HI) belongs in the interval bounds.
- **Feedback loop (latch).** A routed wire like any other, with its own window, plus H_LOOP_POS.
- **Enable / C-element.** Not modelled; hypothesis.
- **Discrete time.** One tick is an arbitrary quantum. Closed integer windows introduce ±1-tick boundary conventions (`Toff - 1` and similar).
