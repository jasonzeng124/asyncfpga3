# B-constraints-update: strict feedback race, exact steer/mux/gated delay, fork data, rig idx (probe Bj)

Also: the stray empty file `formal/out/=` was mine (a shell redirect inside an unquoted heredoc) and is deleted.

Files changed: `formal/out/cell_constraints.gen.py`, `formal/out/cell_constraints.validate.py`,
and, through the generator, `formal/out/cell_constraints.json` and the entry table of
`formal/out/cell_constraints.md` (the "Update (probe Bj)" paragraph is prose written by hand).
No Lean was changed.

The generator now takes an optional second argument. With it, the generator also redraws the
md's entry table:
`python3 -I cell_constraints.gen.py cell_constraints.json cell_constraints.md`.

Before the change, the unchanged generator reproduced the old JSON byte for byte.

## Checks

| file | result |
|---|---|
| `cell_constraints.validate.py cell_constraints.json` (final pass) | 128 constraints, 8 hypotheses, 1295 Lean references in 64 files, `strict 59 strict_pending 20`, **errors: 0** |
| negative control (scratch copy with a misspelt LibGapSteer name, a strict form with margin 0, and an unknown `refers_to`) | 3 errors, as expected |

I grepped every newly cited name as `theorem|def|structure <name>` in its cited file, and found
each one exactly once. `Rd` matches 3 times in LibGapSteer.lean. The same check covers LibGapMux (19 names), LibGapDelay (17) and RigIdx (5;
`H_IDX_SETUP` is a hypothesis name in prose, not cited). All six files are
tracked: `CElemStrict`, `LibGapSteer`, `ForkData`, `LibGapMux`,
`LibGapDelay`, `RigIdx`.

New validator checks:
- each form listed under `strict` has `margin_ps >= 1`;
- each strict entry cites CElemStrict;
- no entry is both `strict` and `strict_pending`;
- every `refers_to` id exists.

## Counts

|  | before | after |
|---|---|---|
| entries | 123 | 128 |
| proved | 121 | 127 |
| unproved | 2 (1 of them partial) | 1 (`bd_link_dctl.lt_first`, partial) |
| exact | 13 | 19 |
| sufficient | 68 | 64 |
| strict (+1 ps) | 0 | 59 |
| strict pending | 0 | 20 |

New entries: `bd_fork.delegated` and `bd_join.delegated` (Blt), and `bd_fork.branch_data`,
`bd_fork.branch_data_edge` and `bdc_amerge.idx_bundle` (Bfd). None was removed.

Newly exact: `bd_steer.bundled_s_setup/_hold` (Blt), `bd_mux.bundled_s_setup/_hold` (Bmx),
`bd_delay_gated.gate` (Bdg, conditional) and `gcd_rig.idx_setup` (Bri, formerly unproved).

## 1. Strictness (Bs, `CElemStrict`)

Every entry in B-celem-strict.md's change list now has:
- a `strict` field (`backing`, `forms`, `terms`, `margin_added_ps: 1`);
- `margin_ps + 1` on the listed forms;
- `L + 1 <= R` written in the inequality text. Held widths now read `>= dlmax + dwmax + 1`.

The existing Lean citations are kept. They are proved with zero-width selects and remain
sufficient for the strict form.

The new CElemStrict citations depend on what backs the entry:

| entries | new citations |
|---|---|
| bd_c2: `env_latency`, `sel_order`, `pulse_width` | `env_latency_iff`, `env_latency_strict`, `box_iff`, `clean_iff` (exact); `c2_all` (instance); `boundary_x` and `binary_glitch` (counter_trace) |
| bd_c2n: the same three | the same, with `c2n_c8g` and `boundary_x_c2n`. Only C-8g's transition is decided. |
| latch `setup_data` and `setup_pulse` (odd, pair.O5, pair.O6, latch_rst); `bd_latch_rst.reset` form 0; the qfb_first entries | the same, with `latch_facts` |
| c3/c4 entries, every `reset_width`, `design.rst_hold` | the generic theorems. Backing: "mechanism (Facts not decided)" |
| instances (ctree node_fork; pipe sel_order, lat_lumped and rst_lines loop terms; mux, merge and muxn race entries; the arbiter and amerge3 `rt2*_pulse*` and `_g*`) | `env_latency_strict` and `box_iff` (role exact, noted as being for the C-element race inside the entry); `c2_all`; `boundary_x` |

Partial forms:
- bd_mux and bd_merge `reset_first`: form 0 only (the H_RST_LONG loop terms).
- `bd_merge.isochronic_forks`: forms 0 and 1 only. The S_SEL_XA_N part is bundling.
- `bd_pipe.rst_lines`: only the two loop terms in the text. The single representative form is one
  of those loop terms.

`exactness` fields are unchanged. `bd_c2.env_latency` could arguably become `exact` per cycle
(`env_latency_iff` over the box, all 8 cycles). I left that to the lead, because
`c2_four_phase`, the multi-cycle result, is only sufficient.

For `qfb_first`, P3 had relaxed the margin to `<=`. That relaxation holds only with zero-width
selects, so the margin is back to 1, and the note now says so.

Already strict (field `strict` with `margin_added_ps: 0`): `lt_first`, `req_separation`, and
`rule_K/L_corrected`. The last two are strict only when `guard >= 1`.

The input-against-input entries are not made strict. They carry `strict_pending` (20 entries):
- latch `hold` ×4;
- `bd_steer.bundled_s_hold` and `bd_mux.bundled_s_hold`;
- the bd_delay flush rules (FASTFALL ×2, FASTRISE ack_flush, and `bd_delay_gated.gate`, which I
  included by analogy);
- `a0_fork_client1` and `a0_fork_client2`;
- `rt2_forkA/G` and `rt2b_forkA2/G2`, plus their amerge3 cascade twins.

A new convention `conventions.strictness` explains the change. It covers the H_MUX_KLEENE X
window, `wa >= 1`, and that the 1 ps is the grid minimum and not a measured slew. The physical
margin is the departing select's X width, which this model does not measure.

## 2. bd_steer exact (Blt, `LibGapSteer`)

Blt's draft logic is ported into the generator, so it no longer reads the scratch file.
`bundled_s_setup` and `bundled_s_hold` are now per-output, per-pin rows and are `exact`:
- exact: `steer_box_exact`, `steer_pin_exact`;
- sufficient: `steer_pin_ok`, `steer_both`, `steer_tokens`, `steer_pin_ok_K`;
- necessary: `setup_needed`, `hold_needed`;
- counter-traces: `spurious_token`, `late_hold_glitch`;
- witnesses: `witness_run`, `witness_hyps`;
- definitions: `Rd`, `SpecOK`;
- kept from before: `steer_req0`, `steer_req1`, `steer_op`, `steer_hold_of_ackfall`,
  `steer_excl_K`.

`bundled_s_hold` is exact in Blt's read-window model and is also flagged `strict_pending` (Bs).
The two statements do not contradict each other. Blt's model gives a read map per pin, but it has
no X inside the mux tree; its listed "not covered" item is H_KLEENE_LUT.

## 3. Fork data (Bfd, `ForkData`) and reconciliation with Blt

- `bd_fork.branch_data`: H_FORK_DATA_W, sufficient+necessary, rule I `missing_term`.
  - It is made strict like `bd_latch.setup_data`, of which it is an instance, backed by
    `latch_facts`. H_FORK_HOLD stays `<=`.
  - Bs's change list did not include this entry, because the entry is new.
- `bd_fork.branch_data_edge`: C-8f's form. Sufficient only (`edge_form_not_needed`). Strict.
- `bdc_amerge.idx_bundle`: H_AMERGE_IDX, with `refers_to` set to the per-race rows and to
  `branch_data`.
- The 5 `bdc_amerge` per-race rows and `bdc_amerge3.bundled_idx0_grant` now carry
  `necessity_scope: edge_sampling_consumer_only` and the caveat note. In gcd_hw the index consumers
  are Muller links, where the exact form is `bd_fork.branch_data`.
- Reconciliation: `bd_fork.delegated` now covers only the ack and C-tree side. Its `refers_to`
  includes `bd_fork.branch_data`, and it cites `ForkData.fork_capture` for the data side. Its latch
  and steer refs moved to `bd_join.delegated`, where they belong.

## 4. bd_mux select setup/hold exact (Bmx, `LibGapMux`)

Bmx's draft logic is ported into the generator. `bd_mux.bundled_s_setup` and `_hold` are now
per-join (uj0, uj1), per-pin rows and are `exact` (`join_box_exact`, `join_pin_exact`). They cite
the sufficient, necessary, counter-trace and witness theorems listed in the draft, and keep the
old MergeMuxSI/ConstraintsMux citations named in the draft's keep list. `also_applies_to` is now
empty: bdc_muxn has other INITs and its own rows. `_hold` keeps `strict_pending`, for the same
reason as the steer's.

## 5. bd_delay_gated.gate (Bdg, `LibGapDelay`)

The gate row is now `exact` with a new field `exact_under`: `[H_BAL_HI, H_LO_ORDER, H_START,
H_SHORT (NoEarly only)]`. A convention entry `conventions.exact_under` says that outside those
conditions the row is sufficient only (`flush_of_gflush`, `no_early_of_gflush`). The note says
that necessity is false without H_LO_ORDER (`rescue_*`). The inequality text is unchanged (it is
`GF`). `strict_pending` stays, consistent with section 1: Bdg's read-window model has no
mid-rail X.

## 6. gcd_rig.idx_setup (Bri, `RigIdx`)

The row is now proved and exact:
- inequality H_IDX_SETUP `vhi + su <= 16*Tlo + rlo + dlmin + enlo`, with side condition
  H_RST_LONG;
- the form is rebuilt: data = idx tCO + vector path + su; request = 16 hk periods + rig_rst path
  to F.I3 + F's arc + the enable path;
- citations: `idx_setup_suff` (sufficient), `idx_setup_iff` (exact), `cex_rig` (counter_trace),
  `idx_nonvacuous` (non_vacuity), `idx_fire` (context); the old RC/Bundling citations are kept;
- check_scope changes from environment to route_plus_env.

`gcd_rig.token_static` now cites `idx_fire`: the token is needed only until F's first rise plus
its loop bound.

## Bk2's kappa_check.patch

The patch was not applied. I re-tested it after the final pass, on a scratch copy of the
final generator and validator. It applies cleanly, with hunk offsets of +359 lines and no fuzz.
The patched generator runs (128 entries). The patched validator's only errors (460) are the
expected "ConstraintsKappa.lean untracked" ones.

So the patch needs no manual rebase, only regeneration. My new checks were placed outside its
context lines. The patch builds `kappa_check` after my pass, and its formula uses each form's `margin`, so
the +1 margins carry over.

Its CORNER_1C text replaces the corner rule that the Bfd rows also use (they use CORNER_1C), so
those rows will pick up the new text automatically.
