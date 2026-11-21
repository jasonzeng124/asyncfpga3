# cell_constraints.json: the cells' exact timing conditions, as data

Shard B, Phase 2 item B (probe P2, 2026-10-27). Companion to
`cell_constraints.json` (schema `cell_constraints/1`). No new Lean, route or
measurement: every entry is transcribed from `formal/notes/B-obligations.md`
and the B-*.md notes, and every cited Lean name was checked to be declared in
the cited, git-tracked file (316 references, 0 missing; one is on
`origin/claude/audit`). Details and limits: `formal/notes/B-cell-constraints.md`.

**Update (probe P4, 2026-10-27).** Re-generated from the same generator
after the P3 and Bg2 Lean files landed (`Formal/Cells/Constraints{Sel,LatchRst,
FastFall,Mux,More}.lean`, `Formal/Cells/GcdCells.lean`; notes
`B-constraints-more.md`, `B-gcd-cells.md`, `B-arb-overlap-race.md`,
`B-ternary-on-bits2.md`). 16 of the 19 unproved entries are now proved; one
(`bd_link_dctl.lt_first`) is partial; two (isochronic forks) stay unproved.
New entries: `bd_latch_rst.reset` (proved) and `bd_steer.bundled_s_setup` /
`.bundled_s_hold` (unproved; bd_steer had no entry). New global hypothesis:
H_LUT62_SHARED_READ. Validator: 87 constraints, 5 hypotheses, 448 Lean
references in 40 files, 0 errors. Still no route and no measurement.

**Update (probe P5, 2026-10-27).** Re-generated after the timed operator
and control_merge Lean files landed (`OpsTimed`, `OpsTimedMux`,
`OpsTimedWit`, `OpsTimed2`; `AMerge*`, `AMergeTimed{,W,C}`, `MuxN3*`;
notes `B-ops-timed.md`, `B-ops-timed2.md`, `B-amerge.md`,
`B-amerge-timed.md`, `B-pipe-witness.md`, `B-arb-corners-pin.md`).
- Now proved (sufficient, lumped LUT arcs): `bd_steer.bundled_s_setup` /
  `.bundled_s_hold` (`SteerStatic.S_S_SETUP/S_S_HOLD`, `steer_ok_static`),
  `bd_mux.isochronic_forks` (`MuxStatic.S_XA_FORK/S_YA_FORK`; the ctl_req
  fork needs no condition under FIFO branches) and
  `bd_merge.isochronic_forks` (`MergeStatic.S_XA_FORK/S_YA_FORK`, plus the
  x_ack branch `S_SEL_XA_Z/S_SEL_XA_R` for the EARLY data protocol only).
- New operator entries (11): `bd_mux.{uj_env_latency_req,
  uj_env_latency_ctl, uxa_join_latency, reset_first, bundled_z_s,
  bundled_z_data}`; `bd_merge.{bundled_z_data, sel_low_xreq,
  uxa_req_latency, reset_first}`.
- Probe Lt3 (`B-ops-counter.md`, `OpsCounter.lean`):
  - The or-skew conditions (mux and merge `S_OR`, steer `S_ACK`) and the ack
    pulse-width conditions (`S_XA_PW`) are proof-route artefacts. Lt3 proves
    the conclusions without them (`mux_ok_noskew`, `merge_or_step`,
    `steer_back_noskew`, `mux_ack_pulses_noPW`, `merge_*A_real_step`).
  - They are therefore NOT entries. One `hypotheses_not_inequalities` row,
    `NOT_OBLIGATIONS`, records why.
  - One-tick counter-runs make `bd_mux.bundled_z_s`, `bd_merge.bundled_z`,
    `bd_merge.bundled_z_data` and the x_ack branch of
    `bd_merge.isochronic_forks` `sufficient+necessary_at_boundary`. That is
    tight on a concrete run, not a general iff. The x_ack branch also gains
    the node-launched form `S_SEL_XA_N`.
  - `bd_mux.bundled_z_data` stays `sufficient`: `surv_S_Z_X` shows 4 ticks
    of slack.
  - `bd_merge.sel_low_xreq` is redundant in exact form (the re-proof without
    it is not written).
  - `OpsCounter.lean` is not yet git-tracked, so it is cited in text only.
    The generator switch `OPSCOUNTER_TRACKED = True` adds 17 references once
    it is committed.
- New cells (19 entries): `bdc_amerge` (bundled_idx_grant, _ack, _ack_g,
  _grant_fall, idx_ack_fork; Cm2 arc forms, each with a counter-trace except
  `_ack_g`), `bdc_amerge3` (rt2_cascade_* x8, bundled_idx0_grant),
  `bdc_muxn` (rtz, s_setup, s_hold, iso_ctl, iso_zack: `unproved`, SI
  filter form only, `muxn3_ok` + counter-runs).
- Corner rule for the arbiter-based entries: `1C` with O5 arcs read from the
  routed physical pin (`ArbCornersPin.pinCol`); with DELAY = 0 the sign of
  amerge2's race 1 flips with q's pin (`pinA5_delay0`).
- References added to existing entries: `bd_mux.uxa/uya_rtz_env` (the
  `S_*_RTZ` fields of the whole-cell theorem), `bd_mux.bundled_s_*`
  (premise of `mux_ok`), `bd_mux.bundled_z` / `bd_merge.bundled_z`
  (`mux_data_ok`, `merge_data_ok`), `bd_delay[FASTFALL].flush_per_stage`
  (`ff_tok`, `mux_ok_fastfall`), the `bd_pipe` entries (PipeWitness W1-W3,
  non-degenerate witnesses), the `bd_arbiter` entries (instances inside the
  control_merges).
Validator: 116 constraints, 6 hypotheses, 708 Lean references in 53 files,
0 errors (also 0 missing against `HEAD`). Still no route and no measurement;
every margin quoted from Cm2 is arc-only (routes 0).

**Update (probe P6, 2026-10-27).** Re-generated after the Lt3, Lt4, Mn, Rst
and Rst2 Lean files were committed (`OpsCounter`, `OpsExact`, `MuxN3Timed`,
`ResetContract`, `ResetGcd`, `ResetGcdNet`; notes `B-ops-counter.md`,
`B-ops-exact.md`, `B-muxn3-timed.md`, `B-reset-contract.md`,
`B-reset-gcd.md`). Generator switch `OPSCOUNTER_TRACKED = True`.
- **bd_merge.** The x_ack branch of `isochronic_forks` now gates on the
  node-launched `S_SEL_XA_N` alone (`OpsExact.merge_data_ok_exact`; tight by
  one tick, `cex_S_SEL_XA_N`); `S_SEL_XA_Z`/`S_SEL_XA_R` are no longer forms.
  `S_SEL_XR` is redundant (proved), so `bd_merge.sel_low_xreq` is removed and
  listed under NOT_OBLIGATIONS. `H_SEL_START` moved out of `reset_first` into
  the new `bd_merge.sel_start`: exact (one tick, `MergeY.cex_H_SEL_START`) in
  its `Lxa.hi + hq` leg, but only against a uxa that powers up HIGH.
  `merge_ok_noskew` removes the merge's `S_OR` by a theorem.
  `uxa_feedback` (`S_XA_ZA`) is REDUNDANT when
  `Wzx.hi - Wzx.lo <= Wxc.hi - Wxc.lo` (`merge_za_of_R`, given `S_XA_R (1)`).
- **bd_mux.** `bundled_z_s`: `S_Z_S1` is necessary on its own
  (`MuxA.cex_S_Z_S1`); `S_Z_S0` by the x/y mirror (not built).
  `bundled_z_data` is now `sufficient+necessary_at_boundary`: the static
  `S_Z_X` is tight when x is the join's late input (`MuxA.cex_S_Z_X`), slack
  otherwise. `uxa_rtz_env`/`uya_rtz_env` are REDUNDANT when the z_ack wire's
  spread is at most the join wire's (`Wzx.hi - Wzx.lo <= W0x.hi - W0x.lo`,
  `mux_rtz_of_J` / `mux_rtz_y_of_J`, given `S_XA_J (1)`).
- **bdc_muxn** (MuxN3Timed): all five entries are now proved sufficient with
  timed EndpointOK forms (`MN3Static`, `MN3DataStatic`,
  `muxn3_s_pin_of_static`). `s_setup` (decode form) is exact in the one-tick
  counter-run family `Mn3Cex`. `iso_ctl` is no skew bound, only the per-branch
  join env latency `S_J_C`. `rtz` is redundant when the z_ack wire's spread at
  ua_k is at most the j wire's (`rtz_of_fork_j`). New entries
  `bdc_muxn.bundled_z_data` (`S_Z_D`) and `bdc_muxn.uj_env_latency_req`
  (`S_J_X`).
- **Reset** (new cells `design`, `gcd_rig`): `design.rst_hold`,
  `design.rst_flush` (`reset_binary`, `gcd_reset_binary`,
  `gcd_reset_release`; on gcd_hw rst must be held >= 23(D+W+1)+W model
  steps), `design.rst_release_skew` (`H_RST_SKEW`: only sufficient;
  `gcd_release_quiet` proves that nothing moves before a frontier link fires
  for EVERY release skew, so the form matters only for H_NO_RETURN after
  that), `gcd_rig.token_static` (`c2n_frontier`, `gcd_frontier`; replaces
  `H_RST_SEL(c)` at the 10 frontier links), `gcd_rig.idx_setup` (unproved,
  trivially met; proved exact since probe Bj's update, RigIdx). The bd_latch first write has no id of its own: it is the
  phase-0 instance of `bd_latch[*].setup_data`, `bd_pipe.boundary_I` and
  `bd_pipe.data_lead`, which now cite the latch lemmas; its guard half is the
  NRBW hypothesis row. `bd_c*.reset_width` cite the forcing lemmas
  (`*_rstB`, `*_rstK`), and bd_c2n's now cites the general `c2n_reset`.
- New `lean` role `redundancy`: a lemma showing that the entry follows from
  another entry under the condition in its note. A checker may skip the entry
  when the condition holds on the route.
Validator: 123 constraints, 8 hypotheses, 913 Lean references in 58 files,
0 errors. Negative control (scratch copy): a misspelt name, a name cited from
the wrong file and a bogus arc kind give 3 errors. Still no route and no
measurement.

**Update (probe Bj, 2026-10-27).** Re-generated after the Bs, Blt, Bfd, Bmx, Bdg and Bri
Lean files were committed (`CElemStrict`, `LibGapSteer`, `ForkData`, and then
`LibGapMux`, `LibGapDelay`, `RigIdx`; notes `B-celem-strict.md`,
`B-lib-gap.md`, `B-fork-data.md`, `B-lib-gap-mux.md`, `B-lib-gap-delay.md`,
`B-rig-idx.md`). Details:
`formal/notes/B-constraints-update.md`.
- **Strict own-feedback race** (Bs). In the per-pin Kleene mux-tree model a
  moving select reads X for at least one tick, so the race is clean iff
  `dlmax + dwmax + wa <= dlmin + E` (`CElemStrict.env_latency_iff`); with
  `wa = 1` ps every own-feedback entry reads `L + 1 <= R`
  (`env_latency_strict`; at equality bd_c2 reads X, `boundary_x`). 59 entries
  carry a new `strict` field and `margin_ps` + 1 on the listed forms (widths
  held `>= Dmax + 1`). The earlier `<=` theorems stay cited: they are proved
  with instantaneous selects and remain sufficient. The 1 ps is the grid
  minimum, not a measured slew (`conventions.strictness`). The
  `bd_mlink`/`bd_flink.qfb_first` margin is back to 1 (P3's `<=` holds only
  with zero-width selects). 20 input-against-input entries (latch hold,
  steer/mux select hold, bd_delay flushes, a0_fork, the rt2 fork fields)
  carry `strict_pending` instead and stay `<=`.
- **bd_steer** (Blt): `bundled_s_setup`/`_hold` are now the per-output,
  per-pin rows of `LibGapSteer` and **exact** (`steer_box_exact`,
  `steer_pin_exact`; counter-traces `spurious_token`, `late_hold_glitch`).
- **bd_fork / bd_join** (Blt, Bfd): new `bd_fork.branch_data` (H_FORK_DATA_W,
  sufficient+necessary, `ForkData.branch_capture`, `fork_data_needed`; rule I
  missing_term; strict like `bd_latch.setup_data`), `bd_fork.branch_data_edge`
  (C-8f's form, sufficient only, `edge_form_not_needed`), and the delegation
  rows `bd_fork.delegated`, `bd_join.delegated` (`see_refers_to`; bd_fork's
  points at `branch_data` for its data side).
- **bdc_amerge** (Bfd): new `bdc_amerge.idx_bundle` (the conjunction
  H_AMERGE_IDX). The per-race `bundled_idx_*`, `idx_ack_fork` and
  `bdc_amerge3.bundled_idx0_grant` now say that their necessity holds only at
  an edge-sampling consumer (`necessity_scope`); gcd_hw's index consumers are
  Muller links, where the exact form is `bd_fork.branch_data`.
- **bd_mux** (Bmx): `bundled_s_setup`/`_hold` are now per-join, per-pin
  rows of `LibGapMux` and **exact** (`join_box_exact`, `join_pin_exact`;
  counter-traces `wrong_branch_latched`, `wrong_branch_runt`,
  `selected_early_fall`). They no longer list bdc_muxn (other INITs).
- **bd_delay_gated.gate** (Bdg): **exact** (`LibGapDelay.box_exact_flushed`,
  `box_exact_no_early`) only under the side conditions in the new field
  `exact_under` (H_BAL_HI, H_LO_ORDER, H_START; H_SHORT for NoEarly);
  sufficient alone otherwise. Without H_LO_ORDER necessity is false
  (`rescue_*`). It keeps `strict_pending`.
- **gcd_rig.idx_setup** (Bri): now proved and **exact**: H_IDX_SETUP
  `vhi + su <= 16*Tlo + rlo + dlmin + enlo` (`RigIdx.idx_setup_suff`,
  `idx_setup_iff`, `cex_rig`, `idx_nonvacuous`). `gcd_rig.token_static` is
  needed only until F's first rise (`idx_fire`).
- The validator also checks the `strict` margins, a CElemStrict citation on
  every strict entry, and that every `refers_to` id exists.
Validator: 128 constraints, 8 hypotheses, 1295 Lean references in 64 files,
0 errors. Negative control (scratch copy): a misspelt LibGapSteer name, a
strict form with margin 0 and an unknown `refers_to` id give 3 errors. Still
no route and no measurement.

## What one entry says

- `id`, `cell` (RTL module; `bit_kind` for latch bits, `variant` for delay
  lines), `also_applies_to`, `catalogue_row` (row in B-obligations.md).
- `forms`: each form is A's `EndpointOK` shape. From a common `launch` event,
  `sum(hi of every arc on each data path) + margin_ps <= sum(lo of every arc
  on each request path)`, for every data path and every request path.
  `combine` = `all` (default) or `any` (RT1, RT1b: race OR structural).
- An arc is `{kind, from, to}` over cell-relative pins (`u.I2`, `ustate.O5`).
  The kinds are `lut_arc`, `site_pin`, `wire`, `feedback_wire`, `line` (a
  delay line traversal), `env` (a segment outside the cell, such as a
  neighbour's response or the server), and `cell_param` (a BRAM datasheet
  constant). `lean_sym` names the Lean variable that the arc instantiates.
- `lean`: `{file, name, role}`. The role is sufficient, exact, necessary,
  counter_trace, instance, rule_as_coded, corner, and so on.
  `exactness` + `exactness_note`.
- `site_pins`: whether the exact form needs per-pin site delays, and for which
  pin roles. nextpnr's SDF flattens every site pin to 25 ps, so it cannot see
  these.
- `rule`: the project rule that approximates the entry, and a verdict: exact,
  conservative, missing_term (with `missing`), *_missing_site_pins, none, or
  uncheckable_statically.
- `corner`: `1C` (one prjxray column for both sides, checked at FAST_MIN and at
  SLOW_MAX), `box`, or `1C_both_corners_required`. **Never take rise from FAST
  and fall from SLOW.** prjxray's two triples are corners, not edges.
- `strict` (Bs): the forms whose `margin_ps` was raised by 1 for the own-feedback race, with the backing Facts lemma; `strict_pending`: an input-against-input order that may need the same +1 but is unchecked.
- `status`: `proved`, or `unproved` when the inequality is not a Lean
  statement (extrapolated, the physical reading of an untimed result, or no
  theorem at all). A partial result keeps `status: unproved` (the validator
  allows only these two) and says `exactness: partial`.
- `check_scope`: static_route, route_plus_env, environment, protocol,
  structural or not_static.

## How shard C's checker consumes a form

Take one form. Node 0 is `launch`. Each path is a chain of 10a arcs `[lo, hi]`.
The `data` nodes are the ends of the data paths. `req` is a single node that
every request path ends in. `setup` is `margin_ps`. tcheck's PASS is then
`Tcheck.verdict_sound`. For a corner model, decide
`EndpointOK kappa (path P) (path Q) (margin + |P| + |Q|)` (`bundle_band`).
The checker resolves `env` arcs by walking the routed netlist when the
neighbour is inside the design. Otherwise they are environment hypotheses.

## Entries (128, plus 8 global hypotheses that are not inequalities)

Counts: 127 proved (19 exact, 64 sufficient; 59 with a strict +1 ps margin, 20 strict pending), 1 partial (`unproved` + `exactness: partial`: `bd_link_dctl.lt_first`), 0 unproved (`gcd_rig.idx_setup` is proved exact since probe Bj's update, RigIdx).

| id | status | exactness | site pins | rule: verdict |
|---|---|---|---|---|
| `bd_c2.pulse_width` | proved | exact (strict +1) | yes | none |
| `bd_c2.env_latency` | proved | sufficient+necessary (strict +1) | yes | none |
| `bd_c2.sel_order` | proved | sufficient+necessary_at_instance (strict +1) | yes | none |
| `bd_c2.reset_width` | proved | sufficient+necessary (strict +1) | yes | none |
| `bd_c2n.pulse_width` | proved | exact (strict +1) | yes | none |
| `bd_c2n.env_latency` | proved | sufficient+necessary (strict +1) | yes | none |
| `bd_c2n.sel_order` | proved | sufficient+necessary_at_instance (strict +1) | yes | none |
| `bd_c2n.reset_width` | proved | sufficient+necessary (strict +1) | yes | none |
| `bd_c3.pulse_width` | proved | exact (strict +1) | yes | none |
| `bd_c3.env_latency` | proved | sufficient+necessary (strict +1) | yes | none |
| `bd_c3.sel_order` | proved | sufficient+necessary_at_instance (strict +1) | yes | none |
| `bd_c3.reset_width` | proved | sufficient+necessary (strict +1) | yes | none |
| `bd_c4.pulse_width` | proved | exact (strict +1) | yes | none |
| `bd_c4.env_latency` | proved | sufficient+necessary (strict +1) | yes | none |
| `bd_c4.sel_order` | proved | sufficient+necessary_at_instance (strict +1) | yes | none |
| `bd_c4.reset_width` | proved | sufficient+necessary (strict +1) | yes | none |
| `bd_ctree.node_fork` | proved | not_necessary (strict +1) | yes | none |
| `bd_ctree.node_loop` | proved | exact (strict pending) | yes | none |
| `bd_ctree.ack_wait` | proved | exact | no | none |
| `bd_latch[odd].setup_data` | proved | exact (strict +1) | yes | I (also K, L for bd_link_dc): missing_term |
| `bd_latch[odd].setup_pulse` | proved | exact (strict +1) | yes | none |
| `bd_latch[odd].hold` | proved | exact (strict +1) | yes | H: conservative_arcs_missing_site_pins |
| `bd_latch[pair.O5].setup_data` | proved | exact (strict +1) | yes | I (also K, L for bd_link_dc): missing_term |
| `bd_latch[pair.O5].setup_pulse` | proved | exact (strict +1) | yes | none |
| `bd_latch[pair.O5].hold` | proved | exact (strict +1) | yes | H: conservative_arcs_missing_site_pins |
| `bd_latch[pair.O6].setup_data` | proved | exact (strict +1) | yes | I (also K, L for bd_link_dc): missing_term |
| `bd_latch[pair.O6].setup_pulse` | proved | exact (strict +1) | yes | none |
| `bd_latch[pair.O6].hold` | proved | exact (strict +1) | yes | H: conservative_arcs_missing_site_pins |
| `bd_latch_rst.setup_data` | proved | sufficient+necessary_at_boundary (strict +1) | yes | I (also K, L for bd_link_dc): missing_term |
| `bd_latch_rst.setup_pulse` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_latch_rst.hold` | proved | sufficient+necessary_at_boundary (strict pending) | yes | H: conservative_arcs_missing_site_pins |
| `bd_latch_rst.reset` | proved | sufficient+necessary (strict +1) | yes | none |
| `bd_latch.loop_bound` | proved | hypothesis | yes | none |
| `bd_delay[sym].pulse_width` | proved | sufficient+necessary_at_boundary | yes | A/B/C/D/E (edge window via SDF): none |
| `bd_delay[FASTFALL].flush_uniform` | proved | not_necessary (strict pending) | yes | F: missing_term |
| `bd_delay[FASTFALL].flush_per_stage` | proved | sufficient+necessary_at_boundary (strict pending) | yes | F: missing_term |
| `bd_delay[FASTRISE].ack_flush` | proved | not_necessary (strict pending) | yes | none |
| `bd_delay_gated.gate` | proved | exact (strict pending) | yes | F: missing_term |
| `bd_pipe.sel_order` | proved | sufficient+necessary_at_instance (strict +1) | yes | none |
| `bd_pipe.lat_lumped` | proved | sufficient+necessary_at_boundary (strict +1) | no | none |
| `bd_pipe.boundary_I` | proved | sufficient+necessary_at_boundary | yes | I: missing_term |
| `bd_pipe.boundary_H` | proved | sufficient+necessary_at_boundary | yes | H: conservative_arcs_missing_site_pins |
| `bd_pipe.rst_lines` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_pipe.data_lead` | proved | sufficient+necessary_at_boundary | yes | A: conservative |
| `bd_pipe.output` | proved | sufficient+necessary_at_boundary | no | consumer's own rule (I at the next stage; B/D/E at an edge-sampling consumer): different_condition |
| `bd_link_dctl.lt_first` | unproved | partial | yes | none |
| `bd_link_dc.rule_K_corrected` | proved | sufficient+necessary_at_boundary | yes | K: missing_term |
| `bd_link_dc.rule_L_corrected` | proved | sufficient+necessary_at_boundary | yes | L: missing_term |
| `bd_arbcell.req_separation` | proved | sufficient+necessary | no | none |
| `bd_arbcell.grant_skew` | proved | exact | no | none |
| `bd_arbcell.handover_overlap` | proved | sufficient+necessary_at_boundary | no | none |
| `bd_arbcell.bbm` | proved | sufficient | no | none |
| `bd_arbcell.settled_exclusion` | proved | exact | no | none |
| `bd_arbiter.a0_fork_client2` | proved | exact (strict pending) | yes | J: exact_arcs_missing_site_pins |
| `bd_arbiter.a0_fork_client1` | proved | exact (strict pending) | yes | J: exact_arcs_missing_site_pins |
| `bd_arbiter.rt1` | proved | sufficient+necessary_at_boundary | yes | none |
| `bd_arbiter.rt1b` | proved | sufficient+necessary_at_instance | yes | none |
| `bd_arbiter.rt2_pulse` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_arbiter.rt2_g1` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_arbiter.rt2_forkA` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bd_arbiter.rt2_forkG` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bd_arbiter.rt2b_pulse2` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_arbiter.rt2b_g2` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_arbiter.rt2b_forkA2` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bd_arbiter.rt2b_forkG2` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bd_arbiter.server_min` | proved | hypothesis | no | none |
| `bd_arbiter.alternation` | proved | sufficient+necessary | no | none |
| `bd_arbiter.ack_celements` | proved | see_refers_to | yes | none |
| `bd_mux.uxa_rtz` | proved | exact (strict +1) | yes | none |
| `bd_mux.uxa_rtz_env` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_mux.uya_rtz` | proved | exact (strict +1) | yes | none |
| `bd_mux.uya_rtz_env` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_mux.bundled_s_setup` | proved | exact (strict +1) | yes | E (skew.py), D (screen): exact_structure_missing_site_pins |
| `bd_mux.bundled_s_hold` | proved | exact (strict +1) | yes | none |
| `bd_mux.bundled_z` | proved | sufficient | yes | A: rule_is_the_check |
| `bd_mux.isochronic_forks` | proved | not_necessary (strict +1) | yes | none |
| `bd_mux.uj_env_latency_req` | proved | not_necessary (strict +1) | yes | none |
| `bd_mux.uj_env_latency_ctl` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_mux.uxa_join_latency` | proved | not_necessary (strict +1) | yes | none |
| `bd_mux.reset_first` | proved | sufficient (strict +1) | no | none |
| `bd_mux.bundled_z_s` | proved | sufficient+necessary_at_boundary | yes | A: different_condition |
| `bd_mux.bundled_z_data` | proved | sufficient+necessary_at_boundary | yes | A: different_condition |
| `bd_steer.bundled_s_setup` | proved | exact (strict +1) | yes | E (skew.py): exact_structure_missing_site_pins |
| `bd_steer.bundled_s_hold` | proved | exact (strict +1) | yes | none |
| `bd_merge.seq` | proved | sufficient+necessary | no | none |
| `bd_merge.bundled_z` | proved | sufficient+necessary_at_boundary | yes | A: rule_is_the_check |
| `bd_merge.bundled_z_data` | proved | sufficient+necessary_at_boundary | yes | A: different_condition |
| `bd_merge.isochronic_forks` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_merge.uxa_feedback` | proved | not_necessary (strict +1) | yes | none |
| `bd_merge.uxa_req_latency` | proved | not_necessary (strict +1) | yes | none |
| `bd_merge.uxa_loop` | proved | exact (strict pending) | yes | none |
| `bd_merge.reset_first` | proved | not_necessary (strict +1) | no | none |
| `bd_merge.sel_start` | proved | sufficient+necessary_at_boundary | yes | none |
| `bdc_amerge.bundled_idx_grant` | proved | sufficient+necessary | yes | A: different_condition |
| `bdc_amerge.bundled_idx_ack` | proved | sufficient+necessary | yes | A: different_condition |
| `bdc_amerge.bundled_idx_ack_g` | proved | sufficient+necessary_at_boundary | yes | A: different_condition |
| `bdc_amerge.bundled_idx_grant_fall` | proved | sufficient+necessary | yes | A: different_condition |
| `bdc_amerge.idx_ack_fork` | proved | sufficient+necessary | yes | none |
| `bdc_amerge3.rt2_cascade_pulse` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bdc_amerge3.rt2_cascade_g1` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bdc_amerge3.rt2_cascade_forkA` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bdc_amerge3.rt2_cascade_forkG` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bdc_amerge3.rt2_cascade_pulse2` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bdc_amerge3.rt2_cascade_g2` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bdc_amerge3.rt2_cascade_forkA2` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bdc_amerge3.rt2_cascade_forkG2` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bdc_amerge3.bundled_idx0_grant` | proved | sufficient+necessary | yes | A: different_condition |
| `bdc_muxn.rtz` | proved | sufficient+necessary_untimed (strict +1) | yes | none |
| `bdc_muxn.s_setup` | proved | exact (strict +1) | yes | E (skew.py): exact_structure_missing_site_pins |
| `bdc_muxn.s_hold` | proved | exact (strict +1) | yes | none |
| `bdc_muxn.no_third_branch` | proved | exact | yes | none |
| `bdc_muxn.iso_ctl` | proved | sufficient (strict +1) | yes | none |
| `bdc_muxn.iso_zack` | proved | not_necessary (strict +1) | yes | none |
| `bdc_muxn.bundled_z_data` | proved | sufficient | yes | A: different_condition |
| `bdc_muxn.uj_env_latency_req` | proved | not_necessary (strict +1) | yes | none |
| `bd_mlink.qfb_first` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_flink.qfb_first` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_mem.setup` | proved | exact | yes | B: conservative_partial |
| `bd_mem.hold` | proved | exact | no | none |
| `bd_mem.rdata_before_ack` | proved | exact | yes | C: missing_term |
| `bd_mem.clk_high_width` | proved | not_necessary | no | none |
| `design.rst_hold` | proved | sufficient+necessary_at_instance (strict +1) | yes | none |
| `design.rst_flush` | proved | sufficient | yes | none |
| `design.rst_release_skew` | proved | not_necessary | yes | none |
| `gcd_rig.token_static` | proved | structural | no | none |
| `gcd_rig.idx_setup` | proved | exact | yes | none |
| `bd_fork.delegated` | proved | see_refers_to | yes | none |
| `bd_join.delegated` | proved | see_refers_to | yes | none |
| `bd_fork.branch_data` | proved | sufficient+necessary (strict +1) | yes | I: missing_term |
| `bd_fork.branch_data_edge` | proved | not_necessary (strict +1) | yes | none |
| `bdc_amerge.idx_bundle` | proved | sufficient+necessary_at_boundary | yes | A: different_condition |
| `bd_link.stage` | proved | exact | yes | none |
| `bd_mux.uj0_env_latency_req_max` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_mux.uj1_env_latency_req_max` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bdc_muxn.uj_env_latency_req_max` | proved | sufficient+necessary_at_boundary (strict +1) | yes | none |
| `bd_delay[FASTRISE].ack_succ` | proved | exact (strict pending) | yes | none |
| `bd_mem.clk_high_width_exact` | proved | exact | no | none |
| `bd_link.stage_rearm` | proved | exact | yes | none |
| `bd_arbiter.settled_rise` | proved | sufficient | yes | none |
| `bd_mux.uxa_seq` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bd_mux.uxa_r` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bd_mux.uya_seq` | proved | sufficient (strict pending) | yes | none |
| `bd_mux.uya_r` | proved | sufficient (strict pending) | yes | none |
| `bdc_muxn.ua_seq` | proved | sufficient+necessary_at_boundary (strict pending) | yes | none |
| `bdc_muxn.ua_r` | proved | sufficient (strict pending) | yes | none |
| `bd_arbiter.rereq_Q` | proved | sufficient+necessary_at_boundary | yes | none |
| `bd_arbiter.rereq_R` | proved | sufficient+necessary_at_boundary | yes | none |
| `bd_arbiter.rereq_G` | proved | sufficient+necessary_at_boundary | yes | none |
| `bd_arbiter.rereq_Q2` | proved | sufficient+necessary_at_boundary | yes | none |
| `bd_arbiter.rereq_R2` | proved | sufficient+necessary_at_boundary | yes | none |
| `bd_arbiter.rereq_G2` | proved | sufficient+necessary_at_boundary | yes | none |

Global hypotheses (`hypotheses_not_inequalities`): H_LUT_FIFO / H_PIN_FIFO /
H_TREE_FIFO (C4), metastability with no deadline (C8/R3),
H_LUT62_SHARED_READ (O5/O6 of a LUT6_2 read a shared pin at the same time;
TernaryOnBits2.SiteSync, ArbOverlapRace.Decomp), NOT_OBLIGATIONS (proof-route
premises that are not cell obligations; P6 adds `S_SEL_XR` and the lumped
`S_SEL_XA_Z`/`S_SEL_XA_R`), NRBW (no read before first write; the never-reset
latch's guard), H_NO_RETURN (lost event after a frontier fires; argued, not
proved), H_RF_ASYM and H_WIRE_RATIO.

## Read first

- **Unchecked by any rule, and on routed evidence the most likely to bite.**
  - `bd_c*.env_latency` and `sel_order` (now proved for every C-element
    INIT, still checked by no rule): C-10f RT_FB fails 4-12 of 64 (mean 7.2, 8 seeds, nextpnr 9c732bc6303458df) Muller-pipeline
    muller stages at slowE.
  - `bd_latch[*].setup_pulse`: the binding environment constraint on the Bt2
    routes.
  - `bd_mux.uxa_rtz_env`: about -6 ps once the guard is applied, at adversarial
    fast.
- **A project rule exists but misses a term.**
  - Rule I, K and L: the feedback-pin arc and the site-pin terms
    (`bd_latch[*].setup_data`, `bd_link_dc.rule_*`).
  - Rule F: the in-flight hop (`bd_delay[FASTFALL].flush_per_stage` and the
    29 `bd_delay_gated` lines of gcd_hw; both now proved sufficient in the
    per-stage form rule F lacks).
  - Rule H and rule J: site pins.
  - Rule C: the consumer's route skew.
- **Proved in P4's update** (16 of the former 19 unproved, with the
  theorem names in the JSON): sel_order for bd_c2/c3/c4
  (`ConstraintsSel.sel_phase_gen`, `sel_order_of_lat_gen`; counter-runs
  `ce_c*_sel_order_fails`); bd_latch_rst setup_data/setup_pulse/hold
  (`ConstraintsLatchRst.capture_rst`, `capture_rst_from_request`); the
  per-stage FASTFALL form (`ConstraintsFastFall.slow_not_early_ps`);
  bd_delay_gated (`ConstraintsFastFall.gated_not_early` and
  `GcdCells.no_early` / `gflush1_of_lat` with the `uor` hop); `uya_rtz_env`
  (`ConstraintsMux.mux_rtz_env_safe_uya`); mux select setup/hold at the join
  pins (`uj0/uj1_unsel_low_timed`); mux and merge bundled_z, classic form
  (`bundled_z_capture`); mlink/flink qfb_first (`*_qfb_first_timed`; the
  former strict `<` is now `<=`, margin 0, tight by one tick on
  `qfb_counter`); BRAM clock high width (`MemPort.clk_high_ok`).
- **partial** (1): dctl `H_LT_FIRST` (`lt_first_window`, LUT level only; its
  link to the untimed schedule `ltFirst` is open).
- **unproved** (1, now 0): `gcd_rig.idx_setup` (a clocked-to-async setup with no
  composing theorem; trivially met by 16 hk cycles of reset; proved exact
  since probe Bj's update, `RigIdx.idx_setup_iff`). The five
  `bdc_muxn` entries that were unproved after P5 (SI filter only) are proved
  sufficient by MuxN3Timed since P6. The four entries that were unproved
  before P5 (mux and merge isochronic forks, bd_steer select setup and hold)
  are proved sufficient in the OpsTimed* model (lumped LUT arcs; the steer's
  per-pin I1-vs-I0 arc is charged as an extra arc).
- **New in P6 and checked by no rule**: the bdc_muxn timed forms (rule E
  covers only the decode setup's structure, without site pins), the three
  `design.rst_*` forms (rst is a general-routed net with fanout 414; its
  skew is unknown) and `bd_merge.sel_start`.
- **New in P5 and checked by no rule**: every new operator entry (join env
  latency, value path) and the
  control_merge's `idx_ack_fork` (a pure route-skew condition:
  `wai <= cmin + wr2g + g2f + wgi` at a consistent corner). The
  control_merge index races are carried by the DELAY line (arc-only margin
  1514 / 537 ps at DELAY = 12); with the bypass they fail by 3-8 ps at one
  corner, depending on q's physical pin.
