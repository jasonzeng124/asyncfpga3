# B-necessity7: the fork rows with `H_DEP` asked only at real edges (probe Bnx7)

Shard B, 2026-10-29. Scope: the three `formal/out/cell_constraints.json` rows
that B-necessity6 left `sufficient` with an unproved "probably not necessary"
analysis: `bd_mux.isochronic_forks`, `bd_mux.uxa_join_latency` (first
conjunct, `S_XA_J.1`) and `bdc_muxn.iso_zack`. The JSON is NOT edited. The
table below is the proposed relabelling.

All Lean is core-only. Each file checks with `/tmp/claude-0/btools/bcheck.py`
(OK, no warnings):

- `formal/lean/Formal/Cells/Necessity7Mux.lean`: bd_mux, gate-aware event and
  static forms, sufficiency (`mux_ok_g`, `mux_ok_gs`).
- `formal/lean/Formal/Cells/Necessity7MuxRuns.lean`: weakened claims, run
  family `RA` (z_ack → uxa wire), `passA5`, `failSEQ6`.
- `formal/lean/Formal/Cells/Necessity7MuxRunsN.lean`: run families `RN` (uxa
  feedback net) and `RB` (j0 → uxa wire with rise/fall spread), `passN5`,
  `failR6`, `passB`.
- `formal/lean/Formal/Cells/Necessity7MuxN.lean`: bdc_muxn, gate-aware event
  and static forms, sufficiency (`muxn3_ok_g`, `muxn3_ok_gs`).
- `formal/lean/Formal/Cells/Necessity7MuxNRuns.lean`: run family `Mn7`
  (z_ack → ua_i wires), `passN7`, `failSEQ8`.

`#print axioms` was run on 21 headline theorems, by appending the lines to
the two leaf files and then removing them. Each gives
`[propext, Classical.choice, Quot.sound]`. The two `staticG_of_static` give
`[propext, Quot.sound]`. There is no sorry, admit, native_decide or axiom.
Values are checked with `decide` or `decide +kernel`.

## Goal 1: the gate-aware `cel_run`

The gate-aware C-element run already existed: `cel_run_g` (OpsExact2, probe
Lt5). Lt5 used it for bd_merge only. It asks `H_DEP` only in gate-on tokens.
In its place, after a gate-off token, it asks the ORDER fact `eb (2k+1) ≤
ea (2k+2)`, with no loop term. This probe applies it to the mux and to the
muxn. No retiming lemma was needed beyond Lt3's `Tok.retime`, which
`cel_run_g` already uses.

- **`MuxTimingG`** (Necessity7Mux) is `MuxTiming` with three changes.
  - `H_DEP_XA` / `H_DEP_YA` are asked only in the owner's tokens. The instance
    against j0's next edge is asked only when that edge is also x's.
  - `H_SEQ_XA` / `H_SEQ_YA` are added: across a y → x hand-over, z_ack's fall
    reaches uxa no later than j0's rise.
  - `H_CTL_SEQ` and `H_OR_SKEW` are dropped. They follow from `MuxCausal`
    (`ζ_step`, `or_tok_mono`).

  `MuxTiming.g` shows that the old form implies the new one.
- **`mux_ok_g`** proves `mux_ok`'s whole conclusion (`MuxConcl`) from
  `MuxGates + MuxEnv + MuxTimingG + MuxCausal + 1 ≤ Es`. `mux_ok_of_timing`
  derives `mux_ok` from it.
- **`MN3TimingG`** and **`muxn3_ok_g`** (Necessity7MuxN) are the same for
  bdc_muxn, with `H_DEP_A` asked only in input `i`'s tokens and `H_SEQ_A` on a
  hand-over to `i`. `MN3Timing.g` shows that the old form implies the new one.

## The static forms

`Kz = wo + Lor.lo + Dz.lo + Es` and `Kc = Wzc.lo + Ec + wc + lj`, as in
OpsTimedMux. For bdc_muxn, `Kc = Wzc.lo + Ec + (wc + ls + wsj + lj)`.

`MuxStaticG` is `MuxStatic` with `S_XA_FORK`, `S_XA_J.1`, `S_OR` and the y
mirrors removed, and these fields added:

    S_XA_SEQ : Wzx.hi ≤ Kc + W0x.lo                                     (order only)
    S_XA_R   : S_XA_N ∨ (S_XA_FORK ∧ S_XA_J.1)
    S_XA_N   : Lxa.hi + wxah ≤ Lxa.lo + Wxa.lo + Ex + Wx.lo + Lj0.lo + W0x.lo

`S_XA_N` is the node-launched client loop: in an x token, j0's next real
edge comes after x_ack, through the x client. The right disjunct is the
shipped pair. The same edge is ALSO causally after z_ack through the control
sender, because the join waits for ctl_req as well. So the shipped pair stays
a valid sufficient branch. The analysis in B-necessity6 missed this. The
consequence is that the client loop alone is not the replacement: the
replacement is the disjunction.

`staticG_of_static : MuxStatic → MuxStaticG` shows that the new set is
implied by the shipped one. `mux_timing_g_of_static` and `mux_ok_gs` prove it
sufficient. `MN3StaticG`, `staticG_of_static`, `muxn3_timing_g_of_static`
and `muxn3_ok_gs` do the same for bdc_muxn: `S_A_SEQ`, and `S_A_R = S_A_N ∨
(S_A_FORK ∧ S_A_J.1)`.

## The runs

Every run uses real INITs. Every gate relation holds for ALL `t`: each
trace is defined by structural recursion on its own gate equation, and
`MuxGates` / `MN3Gates` hold by `rfl`. The environment is open-loop and
periodic. The partners are `Ex = Ey = Ec = Es = 1`, `Wzc = uW`, and every
other LUT and wire is one tick. For bd_mux: reset is high on `[0, 12)`,
control tokens alternate x and y, and the period is 23 per control token.
The weakened claims are `ClaimSEQ s` and `ClaimR s` (`MuxStaticW … sq sr`):
one field is weakened by `s` and every other hypothesis of `mux_ok_gs` is
copied verbatim. `claimSEQ0` and `claimR0` are proved.

| theorem | run | shipped field violated | new set | outcome |
|---|---|---|---|---|
| `passA5` | `RA.run 5 uW`: z_ack → uxa wire 5 ticks | `S_XA_FORK`: `5 + 2 ≤ 5` is false (strict `+1`: false by 3) | holds; `S_XA_SEQ` with equality (`5 ≤ 5`) | `mux_ok`'s whole conclusion (by `mux_ok_gs`); at the y → x hand-over z_ack's fall and j0's rise reach uxa at the same tick (69) |
| `failSEQ6`, `claimSEQ1_false` | `RA.run 6 uW` | (also `S_XA_FORK`) | every field of `MuxStaticW … 1 0`; `S_XA_SEQ` off by exactly 1 (`6 = 5 + 1`) | z_ack (still high from y token 1) and j0 (x token 2) are both high at uxa at 69; x_ack is 1 at 71, inside `[XA 2, XA 3) = [57, 72)` |
| `passN5` | `RN.run 5`: uxa feedback net 5 ticks, clients tight | `S_XA_FORK`: `1 + 6 ≤ 5` is false | holds; `S_XA_N` with equality (`6 ≤ 6`) | passes; the feedback shows x_ack's rise at 33, the same tick j0's fall reaches uxa |
| `failR6`, `claimR1_false` | `RN.run 6` | | every field of `MuxStaticW … 0 1`; `S_XA_R` false (`S_XA_N` off by exactly 1, `7 = 6 + 1`; `S_XA_FORK` off by 3) | j0's fall reaches uxa at 33, before the 6-tick feedback shows x_ack's rise (node at 28); x_ack is 0 at 35, inside `[XA 0, XA 1) = [29, 44)` |
| `passB` | `RB.run`: j0 → uxa wire 1 tick on rises, 8 on falls (`Rx`) | `S_XA_J.1`: `8 + 2 ≤ 4 + 4 + 1` is false (strict: false by 2) | holds; `S_XA_N` has 4 ticks of slack, `S_XA_J.2` is `10 ≤ 13` | passes; j0 falls at 37, reaches uxa at 45, x_ack's node falls at 46 |

The bdc_muxn runs use `Mn7.run d`: unit delays, DELAY = 1, all three
z_ack → ua_i wires `d` ticks, reset on `[0, 9)`, token `k` selects input
`k % 3`, period 27. The weakened claim is `ClaimSEQn s` (`MN3StaticW … sq
sr`), and `claimSEQn0` is proved.

| theorem | run | shipped field violated | new set | outcome |
|---|---|---|---|---|
| `passN7` | `Mn7.run 7` | `S_A_FORK`: `7 + 2 ≤ 7` is false (strict: false by 3) | holds; `S_A_SEQ` with equality | `muxn3_ok_gs`'s whole conclusion (`MN3Concl`) |
| `failSEQ8`, `claimSEQn1_false` | `Mn7.run 8` | | every field of `MN3StaticW … 1 0`; `S_A_SEQ` off by exactly 1 (`8 = 7 + 1`) | z_ack's fall of token 0 reaches ua_1 at 61, j_1's rise of token 1 at 60; in1_ack is 1 at 62, inside `[XA 1 0, XA 1 1) = [46, 63)` |

Each non-necessity claim follows from a sufficiency theorem that covers
EVERY run with these arc windows and partner latencies. So the shipped field
is not necessary over that box, not just in one lucky run. Each boundary
claim is one parameter point. None is an iff.

## Table (proposed relabelling)

| row id | old | new | form | Lean (file: theorem) |
|---|---|---|---|---|
| bd_mux.isochronic_forks (`S_XA_FORK`) | sufficient | **not_necessary**. Replacement: `S_XA_SEQ` (y → x hand-over, order only) **sufficient+necessary_at_boundary**, and `S_XA_R = S_XA_N ∨ (S_XA_FORK ∧ S_XA_J.1)` **sufficient+necessary_at_boundary** (shown on its `S_XA_N` disjunct, at a point where the fork disjunct also fails) | binary `≤` everywhere. The pass runs also violate the strict (`+1`) shipped form. The `+1` of the replacements is not addressed (`S_XA_SEQ` is an input-input order, `strict_pending` class) | Necessity7Mux: `mux_ok_gs`, `mux_timing_g_of_static`, `staticG_of_static`, `MuxStaticG`. Necessity7MuxRuns: `passA5`, `failSEQ6`, `claimSEQ1_false`, `claimSEQ0`. Necessity7MuxRunsN: `passN5`, `failR6`, `claimR1_false` |
| bd_mux.uxa_join_latency | sufficient | first conjunct (`S_XA_J.1`) **not_necessary**: it survives only inside the disjunct of `S_XA_R`. Second conjunct `S_XA_J.2` unchanged (Bnx6: necessary_at_boundary) | binary `≤`. `passB` also violates the strict `S_XA_J.1` | Necessity7MuxRunsN: `passB`. Necessity7Mux: `MuxStaticG.S_XA_R`, `mux_ok_gs` |
| bdc_muxn.iso_zack | sufficient | `S_A_FORK` **not_necessary**. Replacement `S_A_SEQ` **sufficient+necessary_at_boundary**. `S_A_R = S_A_N ∨ (S_A_FORK ∧ S_A_J.1)` **sufficient** only (no muxn boundary run). `S_A_J.1` is now only a disjunct (its muxn pass run was not built). `S_A_J.2` unchanged (sufficient; no muxn boundary run) | binary `≤`. `passN7` also violates the strict `S_A_FORK` | Necessity7MuxN: `muxn3_ok_gs`, `muxn3_timing_g_of_static`, `staticG_of_static`, `MN3StaticG`. Necessity7MuxNRuns: `passN7`, `failSEQ8`, `claimSEQn1_false`, `claimSEQn0` |

A checker should evaluate `S_XA_SEQ`, `S_XA_R` (as a disjunction), `S_XA_RTZ`
and `S_XA_J.2`, with the y mirrors. It should not reject on `S_XA_FORK` or
`S_XA_J.1` alone.

## Plain-language statements

**`mux_ok_gs`.**
- Assumed: OpsTimedMux's model (lumped FIFO LUT arcs, window wires, FIFO
  line, port-level causal partners with minimum latencies, server latency
  `Es ≥ 1`) and the real INITs. The static obligations are `MuxStaticG`
  (shipped set minus `S_XA_FORK`, `S_XA_J.1`, `S_OR` and the y mirrors, plus
  `S_XA_SEQ` and `S_XA_R`). Reset sequencing is `MuxRstG`: only z_ack's first
  edge must follow reset release at uxa / uya.
- Proved: `mux_ok`'s whole conclusion: joins, z_req, both acks in both
  indexings, and order.
- NOT covered: per-pin arcs, the Kleene X `+1`, an iff.

**`muxn3_ok_gs`.** The same, for bdc_muxn, with MuxN3Timed's FASTFALL line
model. The line's flush and `1 ≤ N` are taken as given.

**Counter-runs.**
- Assumed: one parameter point each, with every other hypothesis of the
  claim discharged.
- Proved: the conclusion fails at a decided sample point.
- NOT covered: the uya mirrors (`S_YA_SEQ`, `S_YA_R`: stated, no runs); the
  bdc_muxn `S_A_R` boundary and the `S_A_J.1` pass run; DELAY > 1 for the
  muxn.

## What did not work / open

- The B-necessity6 analysis ("the real bound is the client loop") is
  incomplete. In an x token, j0's next edge is causally after z_ack through
  the control sender too, because the join waits for ctl_req's fall. So the
  exact per-edge condition is the max of two launch paths, and it is stated
  here as the disjunction `S_XA_R`. Whether a finer max form (case split on
  which input of uxa is late) is exact was not examined.
- `RA.run 5`, `RN.run 5` and `Mn7.run 7` pass at equality in the binary
  model. With a Kleene X window (CElemStrict / KleeneWin), a same-tick
  hand-over is likely X. A passing run with one tick of slack exists in each
  family (for example `RA.run 4` satisfies `MuxStaticG`), but it was not
  stated as a theorem.
- bdc_muxn: the `S_A_R` boundary needs a new environment with tight clients,
  and the `S_A_J.1` pass run needs a spread Wja wire. Neither was built
  (time box).
