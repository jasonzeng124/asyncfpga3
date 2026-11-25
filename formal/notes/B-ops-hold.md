# B probe G3: operator data held until the consumer's ack FALL

Shard B, Phase 3, gap G3 of `B-contracts.md`. 2026-10-27. Core Lean, no Mathlib.

File (CLAIMED, checks clean): `formal/lean/Formal/Cells/OpsHold.lean` (680 lines).
Imports (read-only, through their oleans): `Formal.Cells.OpsTimed2`, `Formal.Cells.MuxN3Timed`,
`Formal.Cells.LinkTimed`. No shared definitions added or changed. `OpsExact` was read but not
imported: `merge_data_ok_exact` was not extended (see "Not done").

## Check

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OpsHold.lean
    python3 ../scan.py Formal/Cells/OpsHold.lean

- The check produces no output in about 13 s. Most of that time is the kernel `decide` on the
  witnesses' simulated traces. Two `set_option maxRecDepth … in` are needed for those.
- `scan.py` is clean: no `sorry`, `admit`, `axiom` or `native_decide`.
- `#print axioms` was run on a scratch copy. The main theorems and the witness theorems use only
  `[propext, Classical.choice, Quot.sound]`; the `*_witness_values` use `[propext, Quot.sound]`.
- The lead must add `Formal.Cells.OpsHold` to `Formal.lean`, after `OpsTimed2`, `MuxN3Timed` and
  `LinkTimed`.

## The question, and which side is right physically

C's `Held` (H_BUNDLE, `Formal/Net/Ops.lean`) wants the bus stable from req↑ until the ack↓ that
closes the same token. B's operator data theorems stop at the server's ack↑ plus a margin. That
is not a weakness of the cells. It comes from B's sender contracts (`H_*_HOLD`): a sender only
promises its data until it has seen its ack RISE (the "early" protocol).

**Where the window must end (ack↓ or later).** The library is written to end it at ack↓, and the
consumers need that:
- **A `bd_link` (Muller, `bd_link_ctl`) consumer.** Its latch is transparent while its node C is
  high, and closes when C falls. C falls only after req_in falls, so the latch closes after ack↑,
  in the return-to-zero (`bd_link.v`: "the data hold window ends at ack-fall and not at
  req-fall"; LinkTimed `stage_token`: capture at `cph(2k+1) = max(φ k, α k)`, which is after
  α k). Data that is held only until ack↑ plus a few gate delays walks through a latch that is
  still open.
- **Select inputs** (`bd_mux` s, `bd_muxn` s0/s1, `bd_steer` s): `bd_mux.v` says "s is held … from
  ctl_req-rise until ctl_ack-fall … valid across exactly the output window". `bd_merge.v` says
  "Selecting on x_req flips the mux the moment x enters phase three, while the downstream latch
  is still transparent. The select must … fall with the acknowledge".
- **The library's promise.** `bd_link` with BROAD=1 holds data_out "until ack_out has fallen", and
  `bd_ctl.v` says "the bundled hold window … runs to ack-fall".
- **Not needed** only for a `BD_LINK_DC` consumer with BROAD=0 (it captures at b↑, before its
  ack↑). That build is not used: B-gcd-cells found `BD_LINK_DC` undefined in the gcd build.

**Verdict on (a) and (b).** Extending B is right (option (a)), and it is done below. As an exact
physical condition, though, C's zero-margin `Held` is not the window the consumer latch needs.
See the proposal to C at the end.

## Theorems (all proved)

| theorem | statement | new hypotheses beyond the old theorem |
|---|---|---|
| `mux_data_hold_fall` | `bd_mux` data bit (REAL `bd_datamux` INITs via `DmRel`) = the selected token's bit on `[Z(2k) − Mz, ζ(2k+1) + holdM k]`, i.e. to `holdM` after the server's z_ack **fall** | `MuxHoldF`: **H_S_HOLDF** `Wzc.fst(ζ(2k+1)) ≤ sE k`, **H_X_HOLDF** `XA(2κ0 m+1) ≤ xE m`, **H_Y_HOLDF** `YA(2κ1 m+1) ≤ yE m`. No new static obligation; `holdM` and `MuxDataStatic` are unchanged. |
| `muxn3_data_hold_fall` | `bd_muxn` LUT5 bit (REAL `32'hF0AA_CCF0`) = the selected token's bit on `[Z(2k) − Mz, ζ(2k+1) + Hm]` | `MN3HoldF`: **H_D_HOLDF** `XA i (2κ i m + 1) ≤ dE i m`. The index sender already held to ctl_ack fall (`MN3DataEnv.H_S_HOLD`). Same `Hm`, same `MN3DataStatic`. |
| `merge_data_hold_fall` | `bd_merge` bit (REAL `usel` `4'hE` + datamux) = the owner's bit on `[Z(2k) − Mz, ζ(2k+1) + Hm]` | `MergeHoldF` (owner holds to its ack fall) and `MergeHoldStatic`: **S_SEL_HO** `hq ≤ Wxa.lo + Eo + lr` (x owner: as x_req falls in the return-to-zero, `sel = x_req ∨ x_ack` must be handed over to uxa's node without a gap; x_req falls at least `Wxa.lo + Eo` after the node rose) and **S_HMF_SEL_X** `Hm + 1 ≤ Wzx.lo + Lxa.lo + lq + sl` (x_ack's fall, after z_ack's, reaches the datamux select only after the hold margin). The y-owner side needs nothing new: x_req and x_ack stay low until the next merged request, which comes after y_ack's fall (H_OWN), and `S_HM_SEL_Y` already bounds it. |
| `link_hold_fall` | a `bd_link` output bit (LinkTimed: REAL `bd_c2n` controller, enable fanout windows, Kleene latch) holds token k on `[max(cph(2k)+dlmax+ehi i, dS k+dhi i), β k + dlmin + elo i − 1]`, so it holds through the instant its `ack_out` pin sees the receiver's ack fall (β k) | **H_EN_POS** `1 ≤ dlmin + elo i` (a positive delay). The rest comes from `stage_token` and `cph(2k+2) = max(ρ(k+1), β k)`. |
| `link_x_sender` | if mux client x is latch bit i of a `bd_link`, and the mux's x_ack fall for token m is no later than the link's `ack_out` pin sees it (`hXA`; equality under the G2 convention, which uses one pin), then x meets `H_X_DATA` and `H_X_HOLDF` with `xE m = β m + dlmin + elo i − 1` | `hXA` (the identification of the two event times) |
| `usel_high2`, `stable_union` | helper lemmas: usel is high through its x_ack pin; two abutting stable windows make one stable window | |

So the obligation the probe asked for is stated and discharged: "the selected input's sender must
hold its data until it sees its own ack fall" is `MuxHoldF`, `MN3HoldF` or `MergeHoldF`.
`link_hold_fall` proves it for a `bd_link` sender from the link contract alone (6d's `CtlEnv` +
`DataPath`, including rule H as `H_RULE_H`). It is not assumed.

**Non-vacuity (all proved).**
- `MuxHoldWit.witness`: Lt's unit-delay mux run, tokens x, y, x, y. The control sender's select
  is re-timed to hold to ctl_ack fall (`sF`, `Ls = 0`). `witness_values`: token 0's bit (1) is
  still delivered at t = 26 = ζ 1 + 2, ten ticks past the old window's end ζ 0 + 2 = 16, while the
  unselected y carries 0. Only the data theorem's hypotheses are instantiated: the control-side
  `MuxGates` read Lt's old select `sx`, and `mux_data_hold_fall` does not take the gates.
- `MergeHoldWit.witness`: Lt's unit-delay merge run, with every control and data hypothesis
  instantiated, including `S_SEL_HO` and `S_HMF_SEL_X`. The clients' data are re-timed to hold to
  `XA(2k+1) = 16k+19`. `witness_values`: token 0's bit is delivered at 18 = ζ 1 + 2 while
  `x 16 = false`, i.e. through the usel handover to x_ack.
- `Mn3HoldWit.witness`: probe M3's 3-way run. Its existing data contract already holds 60 ticks,
  past the ack fall. `witness_values`: the bit is delivered at 48 = ζ 1 + 2, where the old window
  ended at 38.

**Negative controls (proved; they show the strengthening is necessary).**
- `MuxHoldWit.early_release_breaks`: OpsTimed2's own mux witness meets every hypothesis of
  `mux_data_ok` (its select is released after ctl_ack rose, before it fell). Inside token 0's
  hold-to-fall window (t = 26), its output is already 0, not token 0's bit 1.
- `MergeHoldWit.early_release_breaks`: the same holds for OpsTimed2's merge witness at t = 18.

So B's old theorems do NOT imply C's `Held`, and the hold-to-fall sender contract is what closes
the gap.

## What did not work, and what is not done

- Everything attempted is proved. No unproved goals.
- **`merge_data_ok_exact` (OpsExact, the no-skew variant) is not extended.** The same edit applies:
  replace the hold with `MergeHoldF` and add S_SEL_HO and S_HMF_SEL_X. About 1 h.
- **The sender's LEAD side is not derived from the link.** `link_x_sender` gives `H_X_DATA` and
  `H_X_HOLDF`, but not `H_X_LEAD` (`xS m + Lx ≤ ξ(2m)`). For a `bd_link` sender, `xS m` is
  `cph(2m) + dlmax + ehi i` (or the D path). That is AFTER its req_out rises (the node), by the
  latch arc plus the enable branch: `bd_link.v` says "req_out LEADS data_out", 152 ps measured.
  `H_X_LEAD` therefore holds only if the request wire from the link to the mux pin (plus any
  `DELAY`) is at least that lead: rule E at steer and mux, rule I. That is a per-arc obligation to
  state, not something the link guarantees.
- The early hold fields (`MuxDataEnv.H_*_HOLD`, `MergeDataEnv.H_*_HOLD`, `MN3DataEnv.H_D_HOLD`)
  are still taken as hypotheses, alongside the hold-to-fall ones. They follow from them whenever
  `XA(2j) ≤ XA(2j+1)`, which holds in every causal run, but I did not prove that monotonicity in
  general. In both witnesses they are discharged directly.
- Not done here: G1 (time-truncated theorems) and G2 (observation points). The `hXA`
  identification in `link_x_sender` is exactly a G2 item.

## Proposal to shard C (option (b): what the consumer latch actually needs)

C's `Held` (bus constant on every step that starts and ends mid-transaction, zero margins at the
channel's wires) is the library's promise. With this file, B can deliver it for mux, muxn3 and
merge outputs: the output holds to ζ(2k+1) + margin as long as the inputs' senders hold to their
own ack fall, and a `bd_link` sender does. So C may keep `Held`. As a physical condition, though,
it is neither the necessary window nor a sufficient one:

1. **The end: ack↓ at the channel is not where the consumer latch closes.**
   - A Muller `bd_link` consumer's latch bit i closes at `Tf + [elo i, ehi i]`, where `Tf` is its
     node's fall. The channel's ack↓, as seen at the producer, is `Tf` plus the ack wire (plus
     `DACK`).
   - What the latch needs at its D pin is the value up to `Tf + ehi_max` (+ hold). The
     producer's own window ends at `ζ(2k+1) + holdM` and then runs through the data wire.
   - The needed condition is therefore `ack wire_min + DACK + holdM + data wire_min ≥ ehi_max`,
     which is tighten.py **rule H** (LinkTimed row 16, `H_RULE_H`).
   - `bd_link.v` gives the measured counterexample: the enable spread was 1125 ps, larger than
     the ack path, which is why DACK exists. So zero-margin `Held` is NOT sufficient for a link
     consumer. It must be paired with 8a's `SetupHold m h` at every link consumer, with `h > 0`
     coming from rule H.
2. **The start: req↑ is earlier than a latch consumer needs.**
   - A latch consumer needs the value settled only by `Tf − setup`. That is rule I:
     `H_DATA_SETUP`, data through the D arc plus one latch loop before the earliest enable fall.
   - Combinational consumers need it earlier: the select of a steer, mux or muxn3, a
     join→compute→link cone, and anything C reads at the offer step `r+1`. For them the need
     starts `Mz` before the request reaches the server (B's `S_Z_*`, `S_ZM_*`).
   - Conversely, a `bd_link` PRODUCER does not meet `Held`'s start at its own pins: req_out leads
     data_out.
   - C's offer-time value read is therefore sound only under the G2 convention, with the channel
     observed at the consumer's pins and with rule E/I's lead obligation between the two.
3. **Concrete weaker contract.** For a channel whose consumer is a `bd_link` (Muller), C needs
   only:
   - `Port` without `Held`, plus
   - the value read at the CLOSE (8a's `TokAt`/`close_val` view), plus
   - `SetupHold m h` around the close.
   For a channel whose consumer is combinational (steer, mux, muxn3, merge, join), C needs
   `Held` from the offer to the consumer's OWN ack fall. Mux, muxn3 and merge now provide that
   for their outputs; for a `bd_link` output it is `stage_forward`/`link_hold_fall`, valid from
   `α k` under the output-bundling inequality. Keeping one uniform `Held` is acceptable because
   B can now supply it. The rule-H margin must then still be added as 8a's `SetupHold` at link
   consumers. **It is not implied by `Held`.**

## Verdict

**Works.** G3 is closed on B's side for `bd_mux`, `bd_muxn` (3-way) and `bd_merge` (the timed
`MergeStatic` form): each output holds the selected or owner token until the hold margin after
the server's z_ack FALL.
- The only new assumptions are the hold-to-fall sender contracts. They are derived for a
  `bd_link` sender (`link_hold_fall`). The merge also gets one new handover obligation,
  S_SEL_HO, plus a hold margin on the select path.
- All three theorems are witnessed. Negative controls show that the old contracts cannot give
  the new window.
- Remaining effort: `merge_data_ok_exact` (~1 h); stating the lead obligation of a link sender
  at a mux, muxn3 or merge input (rule E form, ~half a day); the `XA` monotonicity lemma
  (~1 h).
- What it buys: C's `Held` at operator outputs is now a theorem of the gate models under
  per-channel sender facts. Each of those facts is GLS-testable as "the data net changes only
  after the ack's falling edge at the sender's pin". The latch-side margin (rule H) is
  identified as a separate obligation that C's `Held` does not contain.

## Fidelity per primitive

- **`bd_datamux`** (mux, merge): REAL INITs `8'hE4` and `64'hFFAA_5500_E4E4_E4E4`, through
  OpsTimed2's `DmRel` (Kleene mux over pin windows; window = routed wire + site pin + LUT arc;
  H_KLEENE_LUT). It is unchanged.
- **`usel`** (merge): REAL `4'hE` via `Gate` (Kleene, windows). It is used through BOTH pins in
  the handover (`usel_high2`), so a glitch-free handover is proved under S_SEL_HO, not assumed.
- **muxn3 LUT5**: REAL `32'hF0AA_CCF0` via `Gate`. It is unchanged.
- **`uxa`** (`bd_c2`, REAL INIT, feedback a routed `WinDelay`) is MergeRun's token trace
  (`cel_node`/`cel_run`), unchanged.
- **Control-side event times**: Lt's FIFO bounded-delay arcs (`Ret`: H_LUT_FIFO/H_WIRE_FIFO; no
  glitch, no runt, no inertial filtering on the request/acknowledge paths), unchanged.
- **`bd_link` sender**: LinkTimed's model, unchanged.
  - Controller: REAL `bd_c2n` `0x00B200B200B200B2`, `WinDelay` LUT arc and feedback wire;
    non-FIFO windows, so glitches are allowed in the transition windows.
  - Latch bits: Kleene latch LUTs with their own feedback loop and per-bit enable fanout windows.
- **Witnesses**: unit transport delay on every arc (`Ret.shift 1`, windows [1, 1]). That is a
  consistency check, not timing evidence.
