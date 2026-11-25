# B-kleene-box: the select box iffs in the Kleene model (probe Bkx)

File: `formal/lean/Formal/Cells/KleeneBox.lean` (core Lean; imports LibGapLatch,
LibGapMuxN). Check: `scratchpad/bchk.sh formal/lean/Formal/Cells/KleeneBox.lean`
gives `[bchk] OK`, no warnings. It has no sorry/axiom/native_decide.

## Question

`LibGapSteer.steer_box_exact`, `LibGapMux.join_box_exact` and
`LibGapMuxN.sel_box_exact` are iffs over binary traces, with a binary adversary
select `sAdv`. Only their sufficient halves had a Kleene form. In silicon a pin
that is mid-transition is X. If every pin is a K3 trace (request, ctl_req,
select/index bits, decode output, feedback), with X allowed anywhere outside
the stable windows and outputs computed by the real INITs through `lutK`
(Core's mux tree, H_KLEENE_LUT), what is the exact condition, and how does it
differ from the binary one?

## Answer

1. **In definite-window coordinates nothing changes.** Write `[Ra, Fa)` for
   the request's / ctl_req's support, the instants where it is not a clean 0
   (X windows included), and `[S0, S1)` for the window in which the select
   (each index bit) is definite `v`. Then the K3 iff has exactly the binary
   right side:
   * steer `S0 + Shi ≤ Ra + Rlo ∧ Fa + Rhi ≤ S1 + Slo` (`steer_box_exact_K`)
   * mux join `S0 + Shi ≤ Ca + Clo ∧ Cb + Chi ≤ S1 + Slo` (`join_box_exact_K`)
   * bdc_muxn selected join `SelCond`, per index bit (`muxn_sel_box_exact_K`)

   `steer_K_iff_binary` and `join_K_iff_binary` state K3 safety ⟺ binary
   safety directly. There are two reasons. (a) Necessity: binary traces embed
   in K3 (`*_K_to_B`, through `outK_def`, `jK_kb`, `cK_kb`, `decK_kb`,
   `c2K_kb`), so every binary counter-trace is also a K3 one. (b) Sufficiency:
   in the real INITs, a definite-0 request or ctl_req masks an X select
   (`outK_sel`, `jK_sel`, `decK_sel`, all 3^n by decide), and the select is
   definite wherever it is looked at. X on the request pin or the feedback pin
   never matters. X therefore adds no failure mode. It only moves the window
   edges.
2. **In binary-edge coordinates every setup and every hold gets `+w`.**
   Hypothesis H_X_UNIFORM: every binary edge `T` carries an X window
   `[T - a, T + c)` with the same split on every edge, `w = a + c`. Under it:
   steer `S0 + Shi + w ≤ R + Rlo`, `F + Rhi + w ≤ S1 + Slo`
   (`steer_edges_K`); join the same against `Cr`, `Cf` (`join_edges_K`);
   bdc_muxn the four per-bit inequalities each `+w` (`muxn_edges_K`); latch
   setup_pulse, setup_data and hold each `+w` (`latch_edges_uniform`, which
   generalises `box_exact_edges` from `c = 0` to any split). The result
   depends only on `w`, not on the split: the setup takes `c` from the
   select's rise and `a` from the request's rise, and the hold takes `c` from
   the request's fall and `a` from the select's fall. With one tick of X
   (`w = 1`) **all are strict** (`steer_strict_K`, `join_strict_K`,
   `latch_strict_uniform`). Zero-width windows give back the binary `≤`
   (`steer_atomic_K`).
3. **What the failure looks like at the binary-edge boundary.** Each edge is X
   for one tick before it. At binary-edge equality the binary iff is
   satisfied, yet the UNSELECTED output reads X where the spec says definite 0:
   * `steer_ct_setup_x`: O5 = X at 1299
   * `steer_ct_hold_x`: O5 = X at 3599
   * `join_ct_setup_x` / `join_ct_hold_x`: uj0 = X at 1299 / 3299, with
     x_req waiting, on every trace that obeys H_PIN_READ + H_RESET

   An X on an unselected join is a possible wrong-branch token.
4. **The latch was already Kleene.** `LibGapLatch.box_exact` is a K3 iff (every
   pin K3, X outside the windows, the real INITs through `latM`), and its
   `strict_edges` already settled bd_latch's own rows. The only new piece is
   the any-split form.

Spec, in K3. Steer: `out = kgate(req read, v == b)`. Join: the Kleene C-element
on (request read, ctl_req read gated by the token), with its own feedback
read. muxn: `c2K` of (request, ctl_req through `pc ∘ pd` gated by the token,
feedback). So wherever the spec is definite, the output must be definite and
correct (`specK_definite`), and an unselected join is definite 0 at every
instant (`unsel_definite`).

Non-vacuity:
* `steer_witness_K` and `join_witness_K`: X windows on every edge, strict
  margins, a constructed K3 run (`LibGapLatch.run`) for the join. Selected
  output definite 1, unselected definite 0 at every instant.
* muxn: no X-specific witness. LibGapMuxN's binary witnesses meet the K3
  hypotheses through the embedding.

Assumptions on the necessity witnesses: in the edge forms the request witness
is definite 1 inside its own X windows. That is allowed, because X means
unknown, and the `*_ct_*_x` theorems show the X form of the same failure.
Box necessity treats the pins as independent, as in the binary files.

## JSON rows this settles (`strict_pending` → strict)

The same reasoning as conventions.strictness (CElemStrict) applies: the
mechanism is now checked, and the rows become strict, `+1` at `w = 1`.

| row | before | now |
|---|---|---|
| `bd_steer.bundled_s_hold` | strict_pending | strict in binary-edge times (`steer_strict_K`, ct `steer_ct_hold_x`); exact in definite-window times (`steer_box_exact_K`) |
| `bd_mux.bundled_s_hold` | strict_pending | strict (`join_strict_K`, ct `join_ct_hold_x`); exact K3 (`join_box_exact_K`) |
| `bdc_muxn.s_hold` | strict_pending ("LibGapMuxN has no Kleene version") | strict (`muxn_edges_K` at `w = 1`); exact K3 (`muxn_sel_box_exact_K`), selected join only |
| `bd_steer.bundled_s_setup`, `bd_mux.bundled_s_setup`, `bdc_muxn.s_setup` | not flagged (`≤`) | the same `+w`: strict in binary-edge times (`steer_strict_K`, `join_strict_K`, `muxn_edges_K`; ct `steer_ct_setup_x`, `join_ct_setup_x`) |

NOT settled here: `bd_latch_rst.hold` (a different cell, bd_latch_rst),
the FASTFALL/FASTRISE/delay_gated rows, the arbiter fork / rt2 / cascade rows,
and `bdc_muxn`'s unselected `Cover` in K3.

## NOT covered

* The X width `w`. One tick is the grid minimum, not a measured slew.
* A mid-rail select inside the mux tree beyond H_KLEENE_LUT (grade B).
* Non-uniform splits: with a different split per edge, the setup gets
  `c(select rise) + a(request rise)`, which can be 0. That case is covered by
  the definite-window form, not by `*_edges_K`.
* `NecessityReset.reset_box_exact` (not redone).
* Correlated corners.
