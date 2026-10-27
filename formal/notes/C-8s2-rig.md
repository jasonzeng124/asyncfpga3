# C-8s2: from H_START_ONCE to gcd_rig's re-offering environment

Shard C, probe 8s2, 2026-10-27. About 1.5 h.

**Status: DONE** for (1) the first result and (3) the reset caveat. For (2), every result:
**a NEGATIVE result, proved.** The re-arm induction is proved conditionally, but its
hypothesis is false at every rig re-offer.

## Verdict

1. **Freezing works, and no gate-model field resists it.** Every field of every structure
   in `Cell` (Fork, Join, Steer, Mux, MuxN, AMerge, Link, Src, Sink) and `Held` is one of:
   - a guarded step `x(t+1) ≠ x(t) → …`;
   - an unguarded step that holds on a stutter (`H_AMERGE_RTZ`, `H_LATCH_HOLD`, `Held`);
   - a pointwise property;
   - a tick-0 reset value.

   There is no liveness, fairness or look-ahead field.

   `cell_rt` proves that re-timing all wires and ghost traces through any
   stutter-or-advance map `φ` with `φ 0 = 0` preserves `Cell`. `held_rt` proves the same
   for `Held`, without needing `φ 0 = 0`. Freezing is `φ t = min t T`.

2. **First result without H_START_ONCE.** (`gcd_hw_window`, `gcd_hw_first`, `gcd_rig_first`.)

3. **Reset level settled, with no new hypothesis.** The rig's `start_req` is high at reset
   release, so `Src.iz` is false for it. Prepending one idle tick (every request low) turns
   "`H_CELLS` without `Src.iz`" (`CellR`) into `H_CELLS` (`cell_pc`). The reset level
   becomes the first offer. The source's acknowledge being low at tick 0 is derived from
   its consumer's own reset field.

4. **Every result: re-arming is FALSE at the rig's re-offers.** (`rearm_fails_at_reoffer`.)
   At every re-offer of `start`, `out0`'s first handshake is still open: its ack is high.
   So the network is never back in its reset state when the next invocation starts.
   Induction over invocations by re-arming cannot reach the rig. It needs a different
   argument (below).

## Theorems (`Formal/Net/CapstoneRig.lean`)

All assume `a, b < 2^31`, as 8s does.

- **`gcd_hw_offer_safe`** (8s's theorem, at offers). Assumes H_CELLS, H_BUNDLE,
  H_START_ONCE. Conclusion: `OffAt (ch out0) k r → dat (r+1) = gcd a b`. Same route as
  8m/8s, using `net_refines` instead of `net_refines_close`.

- **`gcd_hw_window`**. Assumes H_CELLS and H_BUNDLE only. Every `out0` token offered at
  step `r` with `cnt (riseB start.req) (r+1) ≤ 1` is `gcd a b`. Proof:
  - freeze the whole run at `r+1`;
  - the frozen run meets H_CELLS (`cell_rt`), H_BUNDLE (`held_rt`) and H_START_ONCE
    (`cnt_frz`);
  - the offer survives freezing.

- **`gcd_hw_window_close`**. The same at the close, by `close_val` (protocol + `Held`).

- **`gcd_hw_first`**. Assumes H_CELLS, H_BUNDLE and
  **H_START_AFTER_RESULT**: `∀ r2, OffAt start 1 r2 → ∃ r < r2, OffAt out0 0 r`.
  Concludes that `out0`'s first offered value and its first latched value are `gcd a b`.

- **`gcd_rig_first`**. This is the rig version. Its hypotheses:
  - `ch` starts at reset release;
  - `CellR`, which is H_CELLS without `Src.iz`;
  - H_BUNDLE;
  - **`H_ENV`**: `riseB start.req t → out0.ack t`.

  `H_ENV` is uenv1's gate model. `uenv1 = bd_c2n_set(env_c0, in_ack)` drives `start_req`
  (bd_fork's `req_out` is a wire). `env_c0` is `out0_ack` (`assign res_ack = env_c0`).
  C(a,¬b) rises only while `a` is high. This is H_CEL_SI style, the same as every other
  cell model.

  Conclusion: `out0`'s first offered value and first latched value are `gcd a b`.
  H_START_AFTER_RESULT is *derived*: `out0.ack` high implies `out0` was offered (`rise_inv`).

- **`gcd_rig_window`**. Assumes `CellR` and H_BUNDLE. Every `out0` token offered while
  `[start.req 0] + #rises ≤ 1` is `gcd a b`, counting the reset level as an offer.

- **`gcd_hw_window_from`**. If **`H_REARM T`** holds (the gate models hold for the run
  shifted to `T`, reset fields included), then every `out0` token offered at `r ≥ T` with
  at most one start rise in `[T, r]` is `gcd a b`.

- **`rearm_fails_at_reoffer`**. Under `H_ENV`, `¬ H_REARM T` at every `T` with
  `riseB start.req T`. The re-armed `out0` sink (`opAt (consOf out0) = sink out0`) needs
  `out0.ack T = false`, but `H_ENV` says it is true.

`Formal/Net/CapstoneRigTime.lean` holds the generic re-timing lemmas:
- `rtC`, `StepMono`, `frz`, `shf`;
- `*_rt` per structure and `cell_rt`, `held_rt`;
- `pd`, `pc`, `*_pc` per structure, `SrcR`, `CellR`, `cell_pc`, `held_pc`.

## An important detail: the first result closes AFTER the second offer

In the rig, `env_c0` (out0's ack) falls only when `env_c` is high. So `out0`'s first close
comes after `start`'s second rise. A run frozen before the second offer therefore contains
no close of `out0` at all, and 8s's close-level theorem says nothing about it.

The route is:
1. offer-level safety on the frozen run (`gcd_hw_offer_safe`);
2. then, on the unfrozen run, `close_val`: the close value equals the offer value, by
   `Held` and the protocol.

This is why `gcd_hw_offer_safe` was needed.

## Why every result is out of reach (task 2)

What has to hold between invocations for the shift induction is `H_REARM`: all channels
idle and all ghost C-elements low at a tick `T` before the next start rise.

**At the re-offer instant this is provably false** (`rearm_fails_at_reoffer`).

**Earlier candidates in the same window fail too, informally.** `Src.iz` needs
`start.req T = false`, so `T` lies after `start`'s fall in invocation 1. `out0` must also
be idle at `T`. `out0.ack` rises before the re-offer and falls after it, so `T` must come
before `out0`'s first offer. At such a `T` the result token is still inside the network,
so internal channels are busy. (Not formalised: it needs a count lemma, "no `out0` offer
without a preceding start token".)

**So the rig's invocations overlap at the `out0`/env handshake.** A proof for every result
needs one of two things:
- a periodic token run whose spine re-enters `start` while `out0`'s return-to-zero is still
  pending (8s's item 4); or
- a re-arm notion that allows channels in their return phase.

Both are open. The vector is fixed per window (`idx` may change only under reset), so every
invocation would compute the same `gcd a b`. This is not proved.

## Fidelity

- **`H_ENV`** is the C-element model of `uenv1`: it moves only to the value both inputs
  agreed on one tick earlier, under unbounded inertial delay. `bd_fork`'s `req_out` and
  `res_ack` are wires.
- **CMPD delay line.** `res_req` is a delayed `out0_req`. It is used only through `uenv0`
  (`env_c0 = out0_ack`), which the existing Sink model of `out0` already abstracts. Sink
  says ack moves only to req; this is not re-examined here.
- **`CellR` drops only `Src.iz`.** `Src.H_LUT_SI` for `start`, `a` and `b` in the rig
  (the env moves `start_req` only to `¬start_ack`) remains the 8m hypothesis. It is
  plausible from `in_ack = C3(acks)` plus the receivers' protocol, but not proved here.
- **Tick 0 of `ch` is the first tick after `rig_rst` falls.** During reset, kernel
  C-elements are forced low (`bd_c2*`: `q = ~rst·C`), so the consumers' reset fields hold.
  `uenv1` is SET (`q = rst + C`), so `start_req = 1`.
- **Range hypothesis.** `a, b < 2^31`. All 16 rig vectors satisfy it, vector 12 only just: its `a` is `0x7FFFFFFF = 2^31 - 1` (from `a_v = vec[31:0]`).

## Commands that check (run 2026-10-27)

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    FORMAL_SLOT_CWD=$PWD ../slot.sh lake build Formal.Net.CapstoneRig   # both modules, ~12 s
    ../slot.sh lake env lean Wip/C8s2/Axioms.lean   # all ⊆ [propext, Classical.choice, Quot.sound]
    cd .. && ./check.sh Formal/Net/CapstoneRigTime.lean Formal/Net/CapstoneRig.lean
    # [audit] 3590 declarations checked, [check] OK

## Files (all new)

| file | what |
|---|---|
| `formal/lean/Formal/Net/CapstoneRigTime.lean` | Re-timing and prepend lemmas for every cell model. |
| `formal/lean/Formal/Net/CapstoneRig.lean` | Offer form, window, first result, rig version, re-arm theorem and its refutation. |
| `formal/lean/Wip/C8s2/Axioms.lean` | `#print axioms` only. |

No pre-existing file was edited. The lead has to add `Formal.Net.CapstoneRigTime` and
`Formal.Net.CapstoneRig` to `Formal.lean`.

## What it does NOT show

- **Only the first result.** Not the second and later ones, for the rig.
- **Safety only.** It does not show that `out0` is ever offered. The all-quiet run meets
  every hypothesis (O5 is still open).
- **Nothing at cell or timing level.** H_CELLS and H_BUNDLE are unchanged.
- **The rig's ok/err compare logic and the CMPD padding are not modelled.**
- **The `H_REARM` failure is shown only at the re-offer instant.** The rest of the window
  is argued informally (above).

## Surprises

- **No gate-model field had a liveness shape.** Freezing went through for all 66 fields,
  with one generic lemma (`rt_guard`) for the guarded ones.
- **The rig's first close lies after the second offer**, so the freeze needed the offer-level
  theorem.
- **The reset caveat cost no hypothesis.** One prepended idle tick turns the rig's high
  reset level into the first offer. The only extra fact (source ack low at tick 0) already
  follows from the consumer's reset field.
- **H_START_AFTER_RESULT follows from a one-line gate model of `uenv1`.**
