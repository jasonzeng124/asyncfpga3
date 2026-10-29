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

---

# Update (probe Bj2): bdc_muxn exact per bit, bd_latch exact per pin, reset necessity and box-exact reset forms, H_NO_RETURN

Files changed: `formal/out/cell_constraints.gen.py`, `formal/out/cell_constraints.validate.py`, and,
through the generator, `formal/out/cell_constraints.json` and the entry table of
`formal/out/cell_constraints.md` (no hand edits to the md). No Lean changed. Before editing, the
unchanged generator reproduced the committed JSON byte for byte. All logic is ported into one new
generator section ("probe Bj2", just before the global hypotheses), which runs after Bj's strict
and `strict_pending` passes. The generator reads no scratch file. It now also imports `copy`.

## Checks

| check | result |
|---|---|
| `python3 -I cell_constraints.validate.py cell_constraints.json` | 129 constraints, 8 hypotheses, 1437 Lean references in 69 files, strict 62, strict_pending 18, **errors: 0** |
| port against the drafts | Blp's 9 rows are identical to `Blp/draft_entries.json`. Bmn's 3 rows differ only by the intended fields below. Each of Bsx's 12 rows has the drafted exactness and every drafted citation. |
| negative control (scratch copy: misspelt `sel_box_exakt`, latch hold margin 0, `exact_scope` on a sufficient entry, `not_necessary` without `replacement`, `informational` with empty `refers_to`) | 5 errors, one for each fault |

Every cited name is checked by the validator's declaration grep (`theorem|def|...` at the start of
a line in the cited file). `LibGapMuxN`, `LibGapLatch`, `NecessityReset`, `NecessityMuxRtz` and
`ResetGcdWave` are all git-tracked.

New validator checks:
- `exact_scope` only on `exact` entries;
- `not_necessary` needs a `replacement` that is a `hypotheses_not_inequalities` id, and a citation
  whose role starts with `not_necessary`;
- `informational` needs a non-empty `refers_to`.

## Counts

|  | before | after |
|---|---|---|
| entries | 128 | 129 (+ `bdc_muxn.no_third_branch`) |
| proved / unproved | 127 / 1 | 128 / 1 |
| exact | 19 | 31 |
| sufficient | 64 | 51 |
| sufficient+necessary | 13 | 18 |
| sufficient+necessary_at_boundary | 18 | 13 |
| sufficient+necessary_at_instance | 5 | 6 |
| not_necessary | 0 | 1 |
| strict (+1) | 59 | 62 |
| strict_pending | 20 | 18 |

## 1. bdc_muxn (Bmn, LibGapMuxN)

- `s_setup` and `s_hold` carry Bmn's per-decode, per-index-bit inequalities, lean_syms and citations.
- Both get `exactness: exact` plus a new field `exact_scope`; the draft's compound value is not used:
  - s_setup: decode form (forms[0]) exact; data LUT5 form (forms[1], S_Z_S) sufficient;
  - s_hold: the inequality text is exact given S1_b. forms[0] still bounds S1_b − Cf by the sender's
    round-trip contract, and that bound is only sufficient.
- `s_hold` also gets `strict_pending`, for the same reason as `bd_mux.bundled_s_hold`: Bmn has no
  Kleene version.
- New row `no_third_branch` (H_NO_THIRD, exact per join 0):
  - `informational: true`, with `refers_to` set to s_setup and s_hold, which imply it;
  - fields copied from the original s_setup: cell, also_applies_to, corner, check_scope, combine.

## 2. bd_latch (Blp, LibGapLatch; added by the lead)

- The nine odd / pair.O5 / pair.O6 rows (setup_data, setup_pulse, hold) become `exact` with the
  per-pin inequalities.
- The three hold rows become STRICT: margin_ps 1, `strict.backing = strict_edges`, and
  `strict_pending` removed. They cite `box_exact_edges`, `strict_edges`, and
  CElemStrict.env_latency_strict as context.
- `bd_latch_rst.hold` is not in Blp's scope and keeps `strict_pending`.

## 3. Necessity (Bsx) and the reset-width forms

Exactness changes on Bsx's 12 rows:

| rows | new exactness |
|---|---|
| reset_width ×4 | sufficient+necessary |
| design.rst_hold | sufficient+necessary_at_instance |
| bd_latch_rst.reset | sufficient+necessary, with `necessity_scope` "forms[0] only" |
| bd_merge.reset_first, bd_mux.reset_first, bd_pipe.rst_lines | sufficient (notes and citations added) |
| design.rst_release_skew | **not_necessary**, with `replacement: H_NO_RETURN` (new vocabulary value, in conventions) |
| bd_mux.uxa_rtz_env, bd_mux.uya_rtz_env | sufficient+necessary_at_boundary |

**Form fix (Bsx finding 1).** `bd_c{2,2n,3,4}.reset_width` and `design.rst_hold` now have the
shape of `bd_latch_rst.reset` form 0, which is box-exact:
- data side: Rhi (the I_rst arc hi; for rst_hold also the wire and SP) plus Qhi (the feedback
  wire, SP[fb] and the feedback pin's own arc hi);
- request side: rst_width + Rlo (the I_rst arc lo; for rst_hold also the wire and SP lo);
- margin_ps stays 1 (strict).

Moving the I_rst arc lo to the request side alone would make the form weaker, not exact. With
Bsx's numbers, the old form passes at W >= 917 and "arc lo on the request side only" passes at
W >= 872. Exact box needs 995, and the new form (exact + 1) needs 996. The old form's single
`dlmax` arc stood for the feedback-pin arc, which equals the I_rst arc only when O6 is flat
(1C). The fixed form therefore charges both arcs.

The four rows get `corner = CORNER_1C` plus a note citing `reset_box_exact` and
`json_box_gap_fails`. The reset_width inequality text now says that the "release before the first
request" clause is sufficient, not necessary.

## 4. H_NO_RETURN (B-hypotheses.md section 2)

- The hypothesis entry is rewritten:
  - cell level: exact by `returned_pulse_lost` / `early_request_ok`;
  - design level: proved for the reset-release window by `ResetGcdWave.gcd_wave_settled`. Its
    docstring calls it "H_NO_RETURN for the reset-release window". It specialises
    `gcd_first_wave`, the name B-hypotheses cites, which states the covering sA / sB m;
  - residual: H_RST_BEFORE_LOOP (W < 34 steps), from `gcd_clean_release`, `gcd_loop_late` and
    `rst_reads_low`;
  - loop phases: not covered.
- Its `check` is now the routed SDF test of H_RST_BEFORE_LOOP.
- `design.rst_release_skew` cites both ResetGcdWave theorems as `not_necessary`.

## Bk2's kappa_check.patch

Not applied. I re-tested it on scratch copies of the final generator and validator with
`patch -p0`:
- it applies: hunk 2 at offset +639, hunk 3 with fuzz 2, because its trailing context line (the
  conventions `exactness` vocabulary) changed. The new vocabulary text is kept;
- the patched generator runs: 129 entries, each with `kappa_check`;
- the patched validator gives 464 errors, all "ConstraintsKappa.lean is untracked".

Bk2's text replaces CORNER_1C's rule, and CORNER_RST is built from CORNER_1C, so the reset rows
pick up the new text. The patch should be regenerated (not hand-applied) before it lands, because
of the fuzz.

---

# Update (probe Bj3): bd_merge.uxa_loop exact, CElemStrict2 backing, honest `exact` citation roles

Files changed: `formal/out/cell_constraints.gen.py`, `formal/out/cell_constraints.validate.py`, and,
through the generator, `formal/out/cell_constraints.json` and the entry table of
`formal/out/cell_constraints.md` (no hand edits to the md). No Lean changed. Before editing, the
unchanged generator reproduced the committed JSON byte for byte.

Most of the logic is in one new generator section ("probe Bj3", just before the global hypotheses),
which runs after Bj2's section. The generator reads no scratch file. Five citation roles were
relabelled where they are defined (see section 3).

## Checks

| check | result |
|---|---|
| `python3 -I cell_constraints.validate.py cell_constraints.json` | 130 constraints, 8 hypotheses, 1511 Lean references in 71 files, strict 63, strict_pending 18, **errors: 0** |
| new validator on the OLD json | 11 errors: 9 non-iff `exact` citations (the 7 theorems below; two of them are cited twice), and `bd_arbiter.rt1` / `rt1b` are exact with no exact citation and no `exact_scope` |
| negative control (scratch copy with 5 faults: `settled_exclusion` back to `exact`, unknown role `exactt`, a replacement that is itself not_necessary, `exact_scope` removed from `bd_mux.uxa_rtz`, CElemStrict* citations removed from the strict `bd_c4.reset_width`) | 5 errors, one for each fault |

`NecessityMerge.lean` and `CElemStrict2.lean` are git-tracked. Every cited name resolves through
the validator's declaration grep.

New and changed validator checks:
- **The `exact` role needs an iff.** The theorem's statement, from the declaration to the first
  `:=`, must contain `↔`. Exceptions go in `EXACT_NOT_IFF`, which is empty. 125 `exact`
  citations pass.
- **Roles come from a fixed set.** A role outside the vocabulary `ROLES` is an error. The set
  includes the new roles `exact_inner` and `exact_formula`.
- **`exact` entries without an exact citation are listed.** An `exact` entry with no `exact`
  citation must carry `exact_scope` or `exact_under` that says why. Five entries qualify:
  `bd_arbcell.handover_overlap`, `bd_arbiter.rt1`, `rt1b`, `bd_mux.uxa_rtz` and `uya_rtz`.
- **`not_necessary` replacements.** `replacement` may now be a constraint id as well as a
  hypothesis id. A replacement must not itself be `not_necessary`.
- **The strict citation check accepts CElemStrict2.lean.**

## Counts

|  | before | after |
|---|---|---|
| entries | 129 | 130 (+ `bd_merge.uxa_loop`) |
| proved / unproved | 128 / 1 | 129 / 1 |
| exact entries | 31 | 31 (+ uxa_loop, − settled_exclusion) |
| sufficient | 51 | 50 |
| not_necessary | 1 | 3 |
| strict (+1) | 62 | 63 |
| citations with role `exact` | 238 | 125 |
| `exact_inner` / `exact_formula` | 0 / 0 | 114 / 2 |

## 1. bd_merge (Bmg, NecessityMerge)

**New row `bd_merge.uxa_loop` (H_XA_LOOP / H_YA_LOOP), exactness `exact`.**
- Four forms: for uxa and uya, an x_req/y_req branch and a z_ack branch. Each is launched at the
  C-element's own O6 edge.
- Data side: the feedback wire, plus the I2 site pin hi and the I2 arc hi.
- Request side, x_req branch: Wxa.lo + Eo + (Wxc.lo + SP[I0].lo + I0 arc lo).
- Request side, z_ack branch: Wxa.lo + Eo + Kz + (Wzx.lo + SP[I1].lo + I1 arc lo).
- margin_ps 1, as strict +1 with backing c2_all.
- `exact_scope` says the binary iff (`uxa_box_exact`) is `<=`, and that the +1 is Bs's Kleene
  window on top. It also lists what is not covered: the protocol, the single bound K, and pins
  taken as independent.
- Citations:

| role | theorems |
|---|---|
| exact | `uxa_box_exact` |
| sufficient | `uxa_ok` |
| lemma | `merge_hhold` |
| exact_inner | `cel_box_exact` |
| function_equality | `uxa_init` |
| counter_trace | `glitch` |
| non_vacuity | `nonvacuous` |
| redundancy | `old_imply_new` |
| Bs's strict citations (role exact_inner) | the STRICT_INST list |

**The old rows are kept for traceability.** `bd_merge.uxa_feedback` and `uxa_req_latency` become
`not_necessary`, with `replacement: bd_merge.uxa_loop`. They cite:
- `old_not_necessary` and `old_not_necessary_R` (role `not_necessary`);
- `old_imply_new` (role `redundancy`).

Their `refers_to` includes the new row.

**Other bd_merge and bd_ctree notes.**
- `bd_merge.isochronic_forks` gets Bmg's note that the loop term is not needed in y phases. This
  is argued, NOT proved.
- `bd_ctree.node_fork` stays `sufficient`. It gets a note, with citations `ctree1_box_exact` and
  `cel_box_exact` (both `exact_inner`) and `c2/c3/c4_cspec`. The note says:
  - the row is not necessary for a one-node tree: it charges the port-wire spread, which cancels,
    and it omits the port read lo;
  - depth >= 2 is open. The proposed MaxMin condition is quoted as NOT proved.

## 2. CElemStrict2 backing (B-self-audit2 finding 2a)

The 11 rows with backing "mechanism (Facts not decided)" lose the STRICT_MECH citations and now
cite the decided facts:

| rows | new citations | new backing |
|---|---|---|
| bd_c3 and bd_c4: `env_latency`, `sel_order`, `pulse_width` | CElemStrict's generic iffs (`env_latency_iff`, `env_latency_strict`, `box_iff`, `clean_iff`); `c3_all` / `c4_all` (instance); `c4_clean_iff` (bd_c4); `boundary_x` (counter_trace) | "c3_all (CElemStrict2, all 18 cycles)" / "c4_all ... 32 cycles" |
| `bd_c{2,2n,3,4}.reset_width` | `reset_width_iff` and `reset_width_strict` (exact); `reset_width_atomic` (context); `rst_boundary_x`, `rst_glitch` and `rst_powerup_x` (counter_trace); `rst_strict_clean` and `rst_powerup_strict_clean` (non_vacuity); `c2_rst_dec` / `c2n_rst_dec` / `c3_rst_dec` / `c4_rst_dec` (instance); `c2_rst_race`, `c2_rst_forced`, `c2n_rst_race`, `c2_rst_classes`, `c2n_rst_classes`, `rst_boundary_x_c2n` | `<cell>_rst_dec` |
| `design.rst_hold` | the same reset citations, plus `c2set`, `c2nset` and `latrst0/1_rst_dec` | the decided cells are listed; uj0 / uj1 still mechanism (CElemStrict2 does not decide them) |

## 3. Honest `exact` roles (findings 2b, 2c)

**`exact_inner` (2b).** Every CElemStrict / CElemStrict2 citation with role `exact` becomes
`exact_inner`. There are 114 of them. The exception is rows where the race IS the entry:
`bd_c{2,2n,3,4}.env_latency`, `.pulse_width`, `.reset_width` and `design.rst_hold`. Everywhere
else the iff is for the strictness race inside the entry, not for the entry's inequality. The new
convention `conventions.lean_roles` defines `exact`, `exact_inner` and `exact_formula`.

**Non-iff theorems relabelled (2c).** I read each statement:

| theorem | statement | new role |
|---|---|---|
| ArbHandover `overlap_duration_r2_to_r1` | count = max 0 (...) | `exact_formula` |
| ArbCorners `overlap_C` | count = max 0 (d6 − o5q − w) | `exact_formula` |
| ArbCorners `corner_no_overlap` | ∀ t, g1 && g2 = false | `sufficient` |
| ArbBinary `settled_exclusion` | Boolean identity | `sufficient` |
| MuxRtzTimed `rtz_exact_safe` | the safe half only | `sufficient` |
| LibCtlMergeMux `steer_excl_K` | ¬(both t) | `context` |
| CElemInvolution `c2_eternal` (hypothesis "metastability") | an ∃ statement | `counter_trace` |

None of them is an iff.

Effects on the rows:
- `bd_arbcell.settled_exclusion` becomes `sufficient`. It is an unconditional structural fact,
  with no condition that could be necessary.
- `handover_overlap`, `bd_mux.uxa_rtz` / `uya_rtz` and `bd_arbiter.rt1` / `rt1b` stay `exact`,
  with an `exact_scope` that names the exactness argument:
  - the closed form;
  - rtz_exact_safe + rtz_counter;
  - rt1_exclusion + rt1_counter_minserver (rt1b: rt1_exclusion2 + rt1_counter2_minserver).

  These are pairs of theorems, not a single iff.

## Bk2's kappa_check.patch

Not applied. I re-tested it on scratch copies of the final generator and validator, with
`patch -p0` from a scratch root:
- it still applies: hunk 2 at offset +753, hunk 3 with fuzz 2 (its trailing context is the
  conventions `exactness` line), and the validator hunk cleanly. My `lean_roles` convention
  survives;
- the patched generator runs: 130 entries, each with `kappa_check`, including `bd_merge.uxa_loop`;
- the patched validator (REPO pointed at the repo) gives 468 errors, all "ConstraintsKappa.lean is
  untracked".

As before, regenerate the patch rather than hand-apply it.

---

# Update (probe Bj4): Bsx2 boundary necessity, exact bd_ctree.node_loop, where the reset width binds

Files changed: `formal/out/cell_constraints.gen.py`, `formal/out/cell_constraints.validate.py`, and,
through the generator, `formal/out/cell_constraints.json` and the entry table of
`formal/out/cell_constraints.md` (no hand edits to the md). No Lean changed. Before editing, the
unchanged generator reproduced the committed JSON byte for byte, and the final generator does too on
a second run.

All logic is in one new generator section ("probe Bj4", just before the global hypotheses), which
runs after Bj3's section. The generator reads no scratch file. Two conventions were added: `binds_at`,
and an extension of `lean_roles` that defines two new roles, `counter_run` and `numbers`.

## Checks

| check | result |
|---|---|
| `python3 -I cell_constraints.validate.py cell_constraints.json` | 131 constraints, 8 hypotheses, 1669 Lean references in 78 files, strict 64, strict_pending 18, binds_at 5, **errors: 0** |
| port against the drafts | Every one of Bsx2's 20 rows has the drafted exactness, replacement and citation (file, name, role). There is one intended difference: `flush_stage_of_uniform` on `flush_uniform` is cited as `redundancy` (the uniform form implies the per-stage form), not `lemma`. Bct's row is ported with the role changes listed in section 2. |
| negative control (a scratch JSON with 6 faults: a `binds_at` count that disagrees with design.rst_hold's `by_row`, a `binds_at` name missing from the entry's `lean`, `g1_false` cited as `exact`, node_fork's replacement pointing at a not_necessary row, the unknown role `counter_runn`, and a network count above the reset-vector count) | 6 errors, one for each fault |

Every cited name resolves through the validator's declaration grep. `Necessity2Arb`,
`Necessity2AMerge`, `Necessity2Delay`, `Necessity2Latch`, `CTreeExact`, `ResetGcdVec` and
`ResetGcdVec2` are all git-tracked.

New validator checks:
- the roles `counter_run` and `numbers` are added to `ROLES`;
- `binds_at` must have `reset_vector`, `per_cell_model` and `network`, each with an integer `cells`;
- the counts must be ordered network <= reset_vector <= per_cell_model, and reset_vector <= `of`;
- each name in `binds_at.lean` must be in the entry's own `lean` list;
- each `by_row` must sum to its `cells`, and must agree with the named rows.

## Counts

|  | before | after |
|---|---|---|
| entries | 130 | 131 (+ `bd_ctree.node_loop`) |
| proved / unproved | 129 / 1 | 130 / 1 |
| exact | 31 | 32 |
| sufficient | 50 | 31 |
| sufficient+necessary_at_boundary | 13 | 31 |
| sufficient+necessary_matched_fork | 2 | 0 |
| not_necessary | 3 | 6 |
| strict (+1) | 63 | 64 |
| strict_pending | 18 | 18 |
| citations with role `exact` / `exact_inner` | 125 / 114 | 132 / 118 |

## 1. Bsx2 (formal/notes/B-necessity2.md)

**18 rows become `sufficient+necessary_at_boundary`:**
- `bd_arbiter.rt2_g1`, `rt2_forkA`, `rt2_forkG`, `rt2b_g2`, `rt2b_forkA2`, `rt2b_forkG2`;
- `rt2_pulse` and `rt2b_pulse2`, which were `necessary_matched_fork`. `A1_band_overlap_matched` is kept, with role `necessary`;
- the 8 `bdc_amerge3.rt2_cascade_*` rows;
- `bd_delay[FASTFALL].flush_per_stage`;
- `bd_latch_rst.setup_pulse`.

Each cited `*_false` theorem has the form `¬ Claim(field weakened by 1)`. It is a refutation, not an
iff, so its role is `counter_trace`, never `exact`. The sufficient half (`claim0`, `claim2_0`,
`cclaim0`, `cclaim2_0`, `flush0`, `pw0`) is cited as `sufficient`.

The new role `counter_run` marks a theorem that an explicit run satisfies the model. The new role
`numbers` marks a decided fact that says by how much the run violates which field.

Each note ends with a sentence that depends on the row's margin:
- strict rows: Bsx2's sentence about the Kleene +1;
- `strict_pending` rows (the fork rows and the flush row): the margin stays 0, and the X window is
  not checked for an input-against-input order. Bsx2's draft used the strict sentence on these rows
  as well, which would have been wrong for a margin-0 form.

**Two rows become `not_necessary`:**
- `bd_delay[FASTFALL].flush_uniform`: replacement `bd_delay[FASTFALL].flush_per_stage`. It cites
  `uniform_not_necessary` and `uw_line` (non_vacuity).
- `bd_fork.branch_data_edge`: replacement `bd_fork.branch_data`. This is a reclassification only, by
  the existing `ForkData.edge_form_not_needed`.

Both rows add their replacement to `refers_to`.

## 2. Bct (formal/notes/B-ctree-exact.md, CTreeExact)

**New row `bd_ctree.node_loop` (H_CTREE_LOOP), exactness `exact`.** It is inserted after node_fork.

The row has one form per (node n, child c), launched at n's O6 edge:
- data side: the feedback wire, the site pin and the feedback-pin arc, all hi;
- request side: dist_min(n -> root) + E + MaxMin(c) + read_lo(c -> n), where read_lo is the wire,
  site pin and arc, all lo.

The form keeps `margin_ps 1` as strict +1. Its backing is c2_all (CElemStrict) and c3_all / c4_all
(CElemStrict2).

`exact_scope` says:
- the binary iff (`tree_box_exact`) is `<=`;
- the +1 is Bs's Kleene window, put on top and not re-proved;
- NOT covered: H_ACK, which is assumed; the single E; correlated corners.

Citations:

| role | theorems |
|---|---|
| exact | `tree_box_exact` |
| sufficient | `tree_suff` |
| necessary | `tree_needs` |
| lemma | `arrive_bound`, `cel_box_exact` |
| exact_inner | `sh6_cond_iff`, `ctree1_box_exact` |
| counter_trace | `sh6_glitch` |
| non_vacuity | `nonvacuous` |
| redundancy | `old_imply_new` |
| function_equality | `c2/c3/c4_cspec` |
| strict | the strict citations |

Bct's draft roles are changed in three places:
- `ctree1_box_exact` becomes `exact_inner`: it is the one-node special case, as in Bj3's convention;
- `nonvacuous` becomes `non_vacuity`;
- Bct's draft exactness `sufficient+necessary` becomes `exact`, as the brief asks, because
  `tree_box_exact` is an iff.

**`bd_ctree.node_fork` becomes `not_necessary`**, with `replacement: bd_ctree.node_loop`. It cites:
- `sh6_numbers` (`not_necessary`): on box numbers the old form fails by 234 ps, and every run is
  correct;
- `old_imply_new` (`redundancy`).

The row is kept for traceability, and its `refers_to` includes the new row. `bd_fork.delegated` and
`bd_join.delegated` now refer to `bd_ctree.node_loop` as well.

## 3. Where the reset width binds (field `binds_at`; Brst ResetGcdVec, Bfw ResetGcdVec2)

The field is on `bd_c{2,2n,3,4}.reset_width` and `design.rst_hold`. It has three counts:
- `reset_vector`: cells at a hold vector of rho (`gcd_vec_census`). The condition is exact there
  (`gcd_hold_exact`);
- `per_cell_model`: cells that bind in Bfw's two-phase model (`gcd_reset_vec2`; `newHoldL`,
  `newHold_exact`);
- `network`: 0 under Rst2's global hold H_HOLD_LONG (`gcd_reset_vec_of_net`).

| row | reset_vector | per_cell_model | network |
|---|---|---|---|
| bd_c2 | 8 of 153 (ufork0, ucond_br9/10/11_j, ucmpi3.ujoin, umux21.uj0/1/2) | 19 (+ the 11 `newHoldL`) | 0 |
| bd_c2n (+ c2n_set) | 175 of 186 (174 link/pipe controllers + uenv1) | 175 | 0 |
| bd_c3 | 0 of 10 | 0 | 0 |
| bd_c4 | 3 of 14 (uori2/3/4.ujoin) | 3 | 0 |
| design.rst_hold | 195 of 414 (the rows above + 9 arbiter ustate O6) | 206 | 0 |

The 11 `newHoldL` cells bind only if the rst skew W >= dminP, which is 1 to 3 steps.

I checked that the 11 `newHoldL` nodes are `I_c2` by grepping `ResetGcdNet.lean`
(n66, n309, n311, n346, n381, n628, n718, n847, n937, n1400, n1491).

Citation roles:

| role | theorems |
|---|---|
| instance | `gcd_vec_census`, `vec2_census` |
| definition | `holdL`, `newHoldL` |
| sufficient | `gcd_reset_vec`, `gcd_reset_vec2` |
| exact | `gcd_hold_exact`, `newHold_exact` (both contain `↔`, per cell, at the cell's vector) |
| context | `wave_cells_order` (W < dminP: released before the data moves) |
| counter_trace | `counter_uori2` (bd_c4, rst_hold), `counter_br9` (bd_c2, rst_hold), `link_boundary_x` (bd_c2n) |
| non_vacuity | `nonvac_hold` (bd_c2n) |
| redundancy | `gcd_reset_vec_of_net`: the per-cell width is implied by the global hold in the GMW model |

NOT covered:
- every count is in model terms on Rst2's elaborated RTL network, not a routed netlist;
- the exactness of the "or T1 + Dhi <= Tw" branch is not proved;
- the network count assumes the GMW bounds (D, W model steps). A routed rst skew or loop delay
  outside them makes the per-cell row the check again. The field's `network.detail` says so.

Exactness fields are unchanged on these rows.

## Bk2's kappa_check.patch

Not applied. I re-tested it on scratch copies of the final generator and validator with
`patch -p0`:
- it still applies: hunk 2 at offset +980, and hunk 3 with fuzz 2 (its trailing context is the
  conventions `exactness` line);
- the patched generator runs: 131 entries, each with `kappa_check`, including `bd_ctree.node_loop`;
- the patched validator (REPO pointed at the repo) gives 472 errors, all "ConstraintsKappa.lean is
  untracked". None of them is from the new `binds_at` check.

As before, regenerate the patch rather than hand-apply it.

# Update (probe Bj5, 2026-10-29): KleeneBox, Necessity3*, kappa, LinkExact; exact rows checked against their iffs

Files changed: `formal/out/cell_constraints.json` and `formal/out/cell_constraints.validate.py`.
No Lean changed.

The generator `cell_constraints.gen.py` and the md entry table were NOT changed: neither was in
this probe's write set. So the generator alone no longer reproduces the JSON. What does reproduce it
(checked byte for byte) is the generator followed by the patch script:
`python3 -I cell_constraints.gen.py tmp.json && python3 -I /tmp/claude-0/probes/Bj5/bj5.py tmp.json cell_constraints.json`.
The script is written as one pass, so it can be pasted into the generator as a "probe Bj5" section.
The md table still shows the Bj4 labels. Do both before the next generator run, or this update is lost.

## Checks

| check | result |
|---|---|
| `python3 -I cell_constraints.validate.py cell_constraints.json` | 132 constraints, 10 hypotheses, 1956 Lean references in 88 files, strict 68, strict_pending 17, binds_at 5, rows with corner.kappa 124, **errors: 0** |
| negative control (scratch JSON, 5 faults: node_loop given back its strict +1, H_X_UNIFORM removed from a KleeneBox row, "exact" in a kappa result, a 1C row without corner.kappa, a misspelt KleeneBox name) | 5 errors, one for each fault |
| the new validator on the PRE-Bj5 JSON, kappa errors aside | exactly the 4 mismatches below (node_loop, uxa_loop, uxa_rtz, uya_rtz) |

Every cited name resolves through the validator's declaration grep, and every cited file is
git-tracked. The prose names were also grepped against the Lean (e.g. the `verdict_*_κ*`
names use κ). The one name that is not in this repo, `P7kAudit.s1c2_gap_unsafe_at_200`, is on
origin/claude/audit and is quoted as the auditor's.

New validator checks, and why each was needed:
- `strict` may be backed by `KleeneBox.lean`. Before, only CElemStrict counted, and KleeneBox is
  the backing of the six select rows.
- A row whose strict source is KleeneBox must list H_KLEENE_LUT and H_X_UNIFORM in its new
  `hypotheses` field.
- STRICT_IFFS (audit P8): an `exact` row that carries a strict +1 must cite as `exact` an iff
  that states the +1 form. That is a Kleene X-window iff, listed explicitly, not only a binary
  `<=` iff. This check found the 4 mismatches below on the old JSON.
- `hypotheses` must be a list of strings.
- Every 1C / 1C_both row needs `corner.kappa`, whose `see` must be a hypothesis id.
- No `corner.kappa.results` text may call a threshold exact (audit row 18).

## Counts

|  | before | after |
|---|---|---|
| entries | 131 | 132 (+ `bd_link.stage`) |
| proved / unproved | 130 / 1 | 131 / 1 |
| exact | 32 | 33 |
| sufficient | 31 | 24 |
| sufficient+necessary_at_boundary | 31 | 38 |
| strict (+1) / strict_pending | 64 / 18 | 68 / 17 |
| hypotheses_not_inequalities | 8 | 10 |
| citations with role `exact` / `exact_inner` | 132 / 118 | 177 / 116 |

## 1. KleeneBox (Bkx, B-kleene-box.md)

These six rows are now `strict`: margin_ps + 1 on forms[0], and the +1 is written into the
inequality.
- `bd_steer.bundled_s_setup`, `bd_steer.bundled_s_hold`: backed by `steer_strict_K`.
- `bd_mux.bundled_s_setup`, `bd_mux.bundled_s_hold`: backed by `join_strict_K`.
- `bdc_muxn.s_setup`, `bdc_muxn.s_hold`: backed by `muxn_edges_K` at a + c = 1.

The three hold rows lose `strict_pending`.

Each inequality now states both coordinate systems:
- In binary-edge times, under H_KLEENE_LUT + H_X_UNIFORM with w = 1, the form is `+1`. It is
  exact (`*_edges_K`, `*_strict_K`).
- In definite-window times the binary `<=` form is exact (`*_box_exact`, `*_box_exact_K`).

`hypotheses` = [H_KLEENE_LUT, H_X_UNIFORM, H_PIN_READ]. The new hypothesis row
"H_KLEENE_LUT / H_X_UNIFORM" carries audit P8's caveats:
- lutK is the hazard-free, OPTIMISTIC ternary extension, and its silicon fidelity is
  unverified;
- w = 1 is the grid minimum;
- with unequal splits only the definite-window form applies.

bdc_muxn: the K3 results cover the SELECTED join only. The unselected joins' Cover is binary
(`unsel_box_exact`), and exact_scope says so.

The nine bd_latch rows also cite `latch_edges_uniform` / `latch_strict_uniform`, the any-split
form, and list their hypotheses.

## 2. Necessity3* (Bsx3, B-necessity3.md)

These rows move from `sufficient` to `sufficient+necessary_at_boundary`. Each has, for its one
hypothesis or for each of its forms, an explicit run that misses that hypothesis or form by 1
tick and refutes the shipped claim:
- `bd_pipe.boundary_I` (`I_false`), `boundary_H` (`H_false`), `data_lead` (`L_false`: the Lean
  DataN form; the classic form stays not necessary) and `output` (`out_false`). All are N = 2
  runs with a unit control and point windows.
- `bd_pipe.lat_lumped` (`lat_false`, N = 1). The note records that the run refutes `<=` at
  slack 1, so the JSON's +1 form is 2 ps from the refuted point.
- `bd_arbcell.grant_skew`: both forms (`formA_false`, `formB_false`). The skew bound of
  `opposite_sense_exclusion` is cited as context, because it is tight too.
- `bdc_amerge.bundled_idx_ack_g` (`gack_counter`, general; `gack1_false`, one run). Its
  edge_sampling_consumer_only necessity_scope is kept.

`bd_pipe.rst_lines` stays `sufficient`. Its `necessity_scope` says what is covered:
- the loop term (H_RST_LONG) and the request-line term are necessary at the boundary
  (`long_false`, `lines_false`);
- the DACK, guard and per-pin H_RST_SEL terms have no necessity result.

Each new citation uses one of these roles: sufficient (`*0`), counter_trace (`*_false`),
numbers (`*_viol`, `*_exc`, `*_overlap`), or counter_run (`dataS_*`, `timing_*`, `*_sat`,
`W2G_run`).

## 3. kappa (ConstraintsKappa, OnNetlistArbKappa, OnGcdArbKappa)

The new hypothesis row "H_SHARED_CORNER / H_SCATTER (kappa)" covers H_ENDPOINTS, H_AFFINE,
H_SHARED_CORNER and H_SCATTER kappa. It records that kappa is UNMEASURED and that the 0.311
was withdrawn. It cites:
- the CornerNat definitions;
- `allOK_of_gen`, `allOK_iff_gen` (H_DISJ + H_DIV), `sandwich` and `allOK_cancel`;
- the counter-examples `box_unsound_with_kappa`, `one_corner_unsound_with_kappa`,
  `slow_only_unsound` and `endpointNat_not_sufficient`.

Its check text also carries the audit's remark: in the `lit` reading, small-kappa safety
assumes that the within-corner spread is die-wide correlated.

All 124 rows in mode 1C / 1C_both now carry `corner.kappa`: the hypotheses, "unmeasured", the
GenOK check, and `see`. Their shared `corner.rule` was wrong in two places and is rewritten:
- it said "box ... is always sound", which is false in A's model for kappa > 0;
- it required a SLOW_MAX-only guard, which belongs to H_WIRE_RATIO only.

`conventions.corner_rule` and a new `conventions.kappa` say the same. Bk2's per-entry
`kappa_check` patch (a GenOK formula for every form) is still not applied; this update records
the model, not per-form formulas.

Per-row results (`corner.kappa.results` plus citations with role `corner`):
- `bd_arbiter.a0_fork_client1/2` (OnNetlistArbKappa, link_arb). Safe for kappa <= kappa*.
  Unsafe is proved only for kappa >= kappa* + 6/(E+L), and the gap is NOT decided, so kappa*
  is NOT called exact (audit row 18; the audit's in-gap violation is quoted as the auditor's
  theorem). At 1/11 all 16 cases are safe; at kappaE only s1 c2 cons fails.
- `a0_fork_client1/2`, `rt1`, `rt1b`, `rt2_*`, `rt2b_*` (OnGcdArbKappa, gcd_hw):
  - safe for kappa <= kappa* (`row_safe`);
  - unsafe at the ARC-FORM level only, from kappa_u, with the gap < 1e-4 (`rows_gap`);
  - the design value 0.0443 (`lit_min`, `design_lit_safe`, `design_gate_lit`), and 0.0802
    with the server credited;
  - the cons rows that fail at kappa = 0 (`cons_neg`);
  - per-condition minima, quoted from the note's table.
  ArbPin2's h12/h21/o1x/o2x have no JSON row.

## 4. Exact rows: does the inequality equal the Lean iff's form?

All 32 exact rows were checked. Four mismatches were found and fixed:

| row | mismatch | fix |
|---|---|---|
| `bd_ctree.node_loop` (audit P8) | inequality `... + 1 <=`, but `tree_box_exact` is the binary `<=` form; the scope did not name the monotone restriction | inequality now `<=` (margin 1 -> 0); the +1 moves to `strict_pending` (not proved for the tree); exact_scope names H_PIN_FIFO (TreeOK quantifies over Mono read maps) and H_ACK (relative to the ideal root edge: open loop; the closed loop is argued, not proved); `hypotheses` added |
| `bd_merge.uxa_loop` | the same: `uxa_box_exact` is `<=` with `Mono pa`, `Mono pb` | the same fix (margins on forms 0-3: 1 -> 0, `strict_pending`, H_PIN_FIFO in exact_scope) |
| `bd_mux.uxa_rtz`, `bd_mux.uya_rtz` | inequality `+1`, but exact_scope cited only the binary fixed-delay pair `rtz_exact_safe` / `rtz_counter` (`<=` form) | the inequality is kept, because it IS CElemStrict's `box_iff` / `clean_iff` at wa = 1 for the bd_c2 race at uxa's pins (te = tb + wb, tr = slo + wa); `box_iff`'s role goes exact_inner -> exact, `clean_iff` is added, and exact_scope says which theorem gives which form (the composed mux is not re-proved in K3) |

Checked and consistent (no change, or a scope note only):
- `bd_c{2,2n,3,4}.pulse_width`: the +1 is `box_iff` at wa = 1. exact_scope was added to say so,
  and that the binary exact form is `>= Dmax`.
- The 9 bd_latch rows: `box_exact_edges` / `strict_edges` carry the `we`.
- `bd_delay_gated.gate` (exact_under).
- `bd_arbiter.a0_fork_client1/2` (`<=`, strict_pending).
- `bd_arbiter.rt1`, `rt1b` and `bd_arbcell.handover_overlap`: there is no iff, and exact_scope
  already says so.
- The bd_mux, bd_steer and bdc_muxn select rows (section 1).
- `bdc_muxn.no_third_branch`, `gcd_rig.idx_setup`, `bd_ctree.ack_wait` (reachable-set iff,
  scope stated).

Judgement call: for node_loop and uxa_loop I made the inequality equal the exact `<=` form
rather than keep the +1 and weaken the label. A checker that wants the extra 1 ps guard can
apply strict_pending's +1; that is sufficient but not shown necessary.

## 5. LinkExact (Blink, B-link-exact.md)

New row `bd_link.stage`:
- exact; informational, with refers_to the five per-cell rows it composes, because `no_cross`
  shows the per-cell conditions at the substituted times are all the stage needs; forms: none;
- inequality: the six conjuncts, `<=` in definite-window times and strict in binary-edge times
  (`strict_edges`);
- exact_scope and hypotheses record the scope Wf: the ordered windows, H_RST_EARLY,
  H_RST_EARLY_ACK and H_ACK_ORDER, none of which is in Conj;
- also recorded: Split (H_REL_SPLIT), needed only for H_RACE_UP's necessity, which is undecided
  at the tie; the en = c data path; and that it is open loop with one token;
- citations: `exact`, `no_cross`, `strict_edges`, `sufficient`, `need_*`, `Wf`, `Split`,
  `witness`, `Pv_one_tick`, `Pv_breaks`, `out_port`.

The five referred rows (`bd_c2n.reset_width`, `bd_c2n.env_latency`, and `bd_latch[odd]`'s
setup_pulse, setup_data and hold) cite `LinkExact.no_cross` as context, with the scope in its note.

## Not done

- The generator and the md table (outside the write set; see the top of this section).
- Bk2's per-form `kappa_check` formulas.
- No Kleene result for node_loop / uxa_loop.
- No K3 Cover for bdc_muxn's unselected joins.
- No closed-loop or several-token LinkExact.

# Update (probe Bj6, 2026-10-29): Necessity4Mux*, Necessity5*, KleeneWin, KleenePess, OnGcdArbKappaTight

Files changed:
- `formal/out/cell_constraints.bj5.py`: a new "probe Bj6" section at its end, before the final
  `json.dump`. `cell_constraints.gen.py` is unchanged, because it already runs bj5.py after its own
  pass.
- `formal/out/cell_constraints.validate.py`: new checks (below).
- `formal/out/cell_constraints.json` and the md entry table, both regenerated with
  `cd formal/out && python3 -I cell_constraints.gen.py cell_constraints.json cell_constraints.md`.

No Lean changed and nothing was hand-edited. A second generator run into a scratch file gives the
same JSON byte for byte.

Sources: B-necessity4.md, B-necessity5.md, B-kleene-win.md, B-kleene-pess.md and
B-gcd-arb-kappa-tight.md. B-lutfb-bridge.md was read too, but no row of this file concerns C's
LutFb / FbFirst premises, so nothing was added for it.

## Checks

| check | result |
|---|---|
| validator on the regenerated JSON | 137 constraints, 10 hypotheses, 2833 Lean references in 101 files, strict 71, strict_pending 18, 71 rows with strict.x_window, 72 rows with kleene_dependence, **errors: 0** |
| negative control (scratch JSON with 6 faults: x_window removed, H_X_UNIFORM removed, kleene_dependence removed, a bad `needs` value, an unknown replacement_rows id, a misspelt Necessity5Arb name) | 6 errors, one per fault |
| new validator on the pre-Bj6 JSON | 190 errors, all from the new x_window / H_X_UNIFORM / kleene_dependence checks |

The validator resolves every cited name through its declaration grep, and every cited file is
git-tracked. The Lean-like names in the section's prose were also grepped (mux_ok, dc_capture,
lit_srv_min, strict_clean, orn_hold_true, ...), and all of them are declared.

New validator checks, and why each is needed:
- **x_window and H_X_UNIFORM.** A strict +1 row must carry `strict.x_window` and an `H_X_UNIFORM...`
  entry in `hypotheses`. KleeneWin shows the +1 is H_X_UNIFORM at w = 1, not a property of the
  cells, so a later pass must not silently drop that dependence.
- **kleene_dependence.** Every K3-model row (H_KLEENE_LUT, H_MUX_KLEENE, or a strict +1) must carry
  `kleene_dependence`, with `needs` taken from a fixed vocabulary.
- **replacement_rows.** It may appear only on a not_necessary entry and must contain its
  `replacement`. Each listed row must be known and must not itself be not_necessary. The existing
  check takes only a single id.
- **replacement_scope.** It may appear only on a not_necessary entry.

## Counts

|  | before | after |
|---|---|---|
| entries | 132 | 137 (+5 new rows) |
| exact | 33 | 40 |
| sufficient+necessary_at_boundary | 38 | 42 |
| sufficient | 24 | 12 |
| not_necessary | 6 | 11 |
| structural (new label) | 0 | 1 |
| strict / strict_pending | 68 / 17 | 71 / 18 |
| rows with `hypotheses` / with corner.kappa | 24 / 124 | 85 / 129 |
| citations with role exact / exact_inner | 177 / 116 | 190 / 299 |
| Lean references (files) | 1956 (88) | 2833 (101) |

## 1. Necessity4Mux* (Bnx4)

- `bd_mux.uj_env_latency_req`: sufficient -> **not_necessary**. This holds in the box sense:
  `mux_ok_staticN` proves the max form sufficient over every run, and at `pass8`'s parameter point
  the shipped S_J0_X fails by 3 (by 4 in strict form) while every run passes.
  - `replacement` is the uj0 row; `replacement_rows` lists both new rows.
  - New row `bd_mux.uj0_env_latency_req_max`: sufficient+necessary_at_boundary (`fail10`,
    `claimX1_false`). It is tight on the z_ack branch only.
  - New row `bd_mux.uj1_env_latency_req_max`: sufficient. The symmetric uj1 run was not built.
  - Each new row has two forms with `combine: any`: (a) the shipped j branch, (b) the z_ack branch
    j -> uor -> line -> server -> z_ack -> ack C-element. One row per join is needed because the old
    row's `combine: all` spans both joins.
- `bdc_muxn.uj_env_latency_req`: -> **not_necessary** (`Nec4.pass8`). Replacement: the new row
  `bdc_muxn.uj_env_latency_req_max`, sufficient only (`muxn3_ok_staticN`; no boundary run for
  muxn).
- `bd_mux.uj_env_latency_ctl`: -> **sufficient+necessary_at_boundary** (`claimC1_false` against the
  shipped `mux_ok_static`). Only the S_J0_C form; S_J1_C is not built.
- All of these are binary `<=` results. The JSON forms keep the Bs strict +1, so a refuted point at
  slack 1 lies 2 ticks from the JSON form. Every row says this.

## 2. Necessity5* (Bnx5)

- `bd_arbcell.grant_skew`: -> **exact**. `grant_skew_exact`, `formA_iff` and `formB_iff` hold over
  the whole transport model, and supersede Bsx3's boundary label. exact_scope lists what is not
  covered: Kleene X on q, q-branch skew, request routing skew, and involution channels.
- `bd_arbcell.settled_exclusion`: -> **exact** on its precondition (`settled_iff`). The inequality
  field now states the precondition, and the hypothesis H_SAME_Q is recorded.
- `bd_delay[FASTRISE].ack_flush`: -> **not_necessary** (`flush_not_necessary`, `dack3_clean`).
  - necessity_scope: exact at DACK = 2 (`two_exact`, boundary run `dack2_glitch`); not necessary
    for DACK >= 3.
  - Replacement: new row `bd_delay[FASTRISE].ack_succ`, **exact** at line level with point delays
    (`pulse_iff`, Succ).
  - The replacement's exact_scope says that Succ is NOT proved sufficient for window delays (keep
    H_ACK_FLUSH there), and that no PipeTimedN theorem takes Succ as a hypothesis.
- `bd_pipe.rst_lines`: stays **sufficient**.
  - Its necessity_scope now names all four PipeTimedN terms as boundary-tight: H_RST_LONG and the
    request line (Bsx3), plus DACK and guard (`dack_false`, `guard_false`).
  - The row's representative form is the per-pin H_RST_SEL term, which has no necessity result.
    That is why the label stays sufficient.
- `bd_link_dc.rule_K_corrected` and `rule_L_corrected`: -> **sufficient+necessary_at_boundary**
  (`k1_false`, `l1_false`). This is binary `<=` at guard 0.
- `bd_flink.qfb_first`: -> **sufficient+necessary_at_boundary** (`q1_false`). The JSON's strict +1
  is not addressed.
- `bd_mem.setup` and `bd_mem.hold`: -> **exact** in the event model (`setup_exact`, `hold_exact`).
- `bd_mem.rdata_before_ack`: -> **exact** for the `tCO <= dcLo` part only (`rdata_exact`).
  exact_scope says the H_RDATA_ROUTE term is not in the Lean, so with it the row is sufficient only.
- `bd_mem.clk_high_width`: -> **not_necessary** (`clk_high_not_necessary`). Replacement: new row
  `bd_mem.clk_high_width_exact`, `tPWH <= dcLo + dsLoF`, **exact** (`clk_high_exact`). Its twin
  `clk_low_exact` is cited as context.
- Reclassifications that need no new Lean:
  - `bd_merge.reset_first`: -> **not_necessary**. Replacement H_NO_RETURN, with a new field
    `replacement_scope`: it replaces only the H_RST_EARLY form; the loop and wire terms (form 0)
    stay required. The H_NO_RETURN step is cell level (`early_request_ok`), and the note says that
    no merge-level theorem uses H_NO_RETURN.
  - `gcd_rig.token_static`: -> **structural**. This is a new exactness label, added to
    conventions.exactness.

## 3. KleeneWin (Bxw)

Every strict +1 row (71 rows) now has:
- `strict.x_window`: the +1 is H_X_UNIFORM at w = 1.
  - With per-edge windows the exact term is c(first) + a(after).
  - Without the uniform split, "+1, strict" is neither necessary nor sufficient
    (`steer_split_matters`, `steer_ct_split_x`).
  - Without the split, a sufficient form is +W under H_W_BOUND. W is unmeasured (board test XW-1).
- An H_X_UNIFORM entry in `hypotheses`.
- Citations by row type:
  - every strict row: `steer_split_matters` (context) and `steer_win_uniform` (reduction);
  - select rows: `steer_win_exact`, `join_win_exact` or `muxn_win_exact` (role kleene);
  - latch rows: `latch_win_exact` and `latch_fbwin_iff`;
  - own-feedback rows: `cel_env_iff`, `cel_env_win_iff` and `clean_iffW` (exact_inner),
    `c2_fbwin_hazard` (context) and `loopW_exists`.
- On 65 own-feedback and latch-loop rows, the hypothesis "H_FB_WIN: wq = 0 assumed (= H_FB_PURE)".
- On exact strict rows, exact_scope now says the +1 form is exact only under H_X_UNIFORM, with
  wq = 0 on a feedback pin.

## 4. KleenePess (Bpess)

The new field `kleene_dependence` = {needs, basis, inferred} is on 72 rows: every strict row plus
bd_link.stage. Its convention is in conventions.kleene_dependence.

| needs | rows | basis |
|---|---|---|
| pass0 | 2 | bd_steer select rows: `steer_edges_weak1` survives; `steer_fails_M` |
| pass(reset value) | 6 | bd_c*.reset_width, design.rst_hold (`c2M_rst`; inferred except bd_c2), bd_latch_rst.reset (`rstM_reset`) |
| both | 64 | bd_mux select rows (`join_fails_weak1`, `join_fails_weak0`); latch rows and bd_link.stage (`latch_pin_ok_M`, `latch_fails_M`); own-feedback races (`c2M_restore`, `c2M_11x`, `c2nM_restore`; inferred except bd_c2 / bd_c2n); bdc_muxn select rows and latch_facts loops (inferred) |

Safety and exclusion results need nothing (`transfer`, `excl_M`, `arb_acks_safe`). The arbiter
rows are binary and carry no field. This is recorded in the H_KLEENE_LUT / H_X_UNIFORM hypothesis
entry, which also cites `bracket`, `lutP_definite` and `strict_iff`. The H_LUT_FIFO entry notes
that the NMOS-only tree is weak1.

## 5. OnGcdArbKappaTight (Bkx19)

`bd_arbiter.rt1b`'s corner.kappa.results gain the following, with 22 citations:
- The binding row is bracketed to 1.3e-12: safe up to 33176.932320/749546, unsafe from
  33176.932321/749546 (`rt1b_safe`, `rt1b_unsafe`, and the bridge `A_rt1b_safe`, `A_rt1b_unsafe`).
- The gate-level counterpart is `rt1b_gate_unsafe`. Its caveat: the overlap needs zero server,
  zero A0 route to ustate and zero ustate O6 arc. Credited, the threshold is 0.651 and the design
  minimum is 0.0802, so 0.0443 is the server-free form's number.
- The lit reading needs H_SPREAD_CORRELATED; under H_SPREAD_INDEP the row fails at every kappa.

The word "exact" is avoided in the results text (the audit row 18 check), and the threshold is
called bracketed. The other 11 arbiter kappa rows get one sentence (lit verdicts carry
H_SPREAD_CORRELATED, the gap is unchanged) and that hypothesis. The kappa hypothesis entry states
H_SPREAD_CORRELATED / H_SPREAD_INDEP and the T_SPREAD test.

## Not done / judgement calls

- **bd_mux.reset_first.** It has the same H_RST_EARLY / H_NO_RETURN situation as
  bd_merge.reset_first. It was not relabelled, because Bnx5 did not list it.
- **"The three reclassifications".** Read as bd_merge.reset_first, gcd_rig.token_static and
  bd_arbcell.settled_exclusion: the three B-necessity5 rows whose label changes with no new
  theorem about their inequality.
- **ack_succ's strict_pending.** The new row inherits it from ack_flush (input-against-input order).
- **No Lean-side check of the new forms.** The max-form JSON forms were transcribed from the Lean
  statements (`pass8`, `fail10`) and the notes, not checked against an emitter.

# Update (probe Bj7, 2026-10-29): OnNetlistArbKappaExact, OnGcdArbKappaSrv, self-audit 4, ContractBridge, LutFbBridge2

Files changed:
- `formal/out/cell_constraints.bj5.py`: a new "probe Bj7 (2026-10-29)" section at its end, before the
  final `json.dump`. `cell_constraints.gen.py` is unchanged.
- `formal/out/cell_constraints.validate.py`: the audit-row-18 check is narrowed, and three small checks
  are new (below).
- `formal/out/cell_constraints.json`, regenerated with
  `cd formal/out && python3 -I cell_constraints.gen.py cell_constraints.json cell_constraints.md`. The md
  entry table is unchanged, because no exactness label or rule verdict moved.

No Lean changed and nothing was hand-edited. A second generator run gives the same JSON and md byte
for byte (sha256 of the JSON 575c6447...145b4).

Sources: B-arb-kappa-exact.md, B-gcd-arb-kappa-srv.md, B-self-audit4.md, B-contract-bridge.md and
B-lutfb-bridge2.md, plus JOURNAL-B.md progress 12:10 / 12:50.

## Checks

| check | result |
|---|---|
| validator on the regenerated JSON | 137 constraints, 11 hypotheses, 2988 Lean references in 106 files, strict 71 / strict_pending 18, 2 kappa-exact rows, 6 rows with c_contract, 3 rows with boundary_point, **errors: 0** |
| negative controls (scratch copies, one fault each: "exact" in rt1's kappa results; an "exact" results string without the OnNetlistArbKappaExact citation on client 1; exact_s2c2_cons dropped from client 2; one "UNPROVED" removed from an x_window; arb_excl_not_derivable dropped from rt1's lean list while c_contract still cites it) | 5 runs, each fails with exactly the intended error |
| new validator on the pre-Bj7 JSON | 75 errors: 71 from the H_W_BOUND check, 4 from the two kappa-exact rows |

Every cited name is resolved through the validator's declaration grep, and the five new files are
git-tracked. The names used only in prose or in `boundary_point.refuted_by` were grepped by hand:
`Necessity4Mux.claimX1_false`, `Necessity4MuxC.claimC1_false` and `Necessity5Flink.q1_false` are all
declared.

Validator changes, and why each was made:
- **Audit-row-18 check (needed).** This check forbade "exact" in every `corner.kappa.results`.
  `KAPPA_EXACT_ROWS` now exempts exactly `bd_arbiter.a0_fork_client1` and `bd_arbiter.a0_fork_client2`,
  under three conditions:
  - the results string itself names OnNetlistArbKappaExact;
  - the row cites all 8 of its client's `exact_s{1..4}c{k}_{cons,lit}` iffs with role `exact`;
  - the row carries `corner.kappa.exact_source`.

  Every other results string on every row is still checked, including the gcd_hw strings on the same
  two rows. That is why the Bsrv text says "bracketed / violated from" and "7g's iff", never "exact".
- **H_W_BOUND (guard).** Any x_window that claims "+W under H_W_BOUND" must either sit on bd_steer
  and cite `SelfAuditB7.steer_win_bound`, or say UNPROVED.
- **c_contract (guard).** `status` must be one of derived, not_derivable or needs_extra_hypothesis,
  `extra` is required for needs_extra_hypothesis, and every cited name must also be in the row's
  `lean` list.
- **boundary_point (guard).** It may appear only on a strict +1 sufficient+necessary_at_boundary row,
  `ticks_from_row_form` must equal slack + 1, and `necessity_scope` must name the '<=' form.

## Counts

|  | before | after |
|---|---|---|
| entries / hypotheses | 137 / 10 | 137 / 11 (+ H_SEL_STABLE / H_PWR_SRC) |
| exactness labels | unchanged (exact 40, necessary_at_boundary 42, sufficient 12, not_necessary 11, ...) | unchanged |
| citations with role exact | 190 | 206 (+16 exact_*) |
| Lean references (files) | 2833 (101) | 2988 (106) |
| x_window "+W under H_W_BOUND" | 71, unqualified | 2 proved (bd_steer), 69 UNPROVED |

## 1. Exact link_arb A0-fork thresholds (Bkx18, OnNetlistArbKappaExact)

On `bd_arbiter.a0_fork_client1` and `bd_arbiter.a0_fork_client2`, `corner.kappa.results[0]` used to
describe OnNetlistArbKappa's undecided gap. It is replaced by that client's 8 exact thresholds:
- the model is A's whole-ps CornerNat model, gate level on both sides;
- each case cites `exact_sXcK_R` (role exact), `bracket_*`, `safe_antitone`, `not_safe1/2`,
  `verdict_κA` and `verdict_κE`; client 2 also cites `audit_s1c2_cons_200` and `interior_s1c2_cons`;
- s2c2 cons is the rational case (94/325, attained at the fast corner);
- the NOT-covered list is the note's.

The new field `corner.kappa.exact_source` marks these rows. conventions.kappa says that only these
16 cases are exact; gcd_hw stays bracketed.

## 2. gcd_hw arbiters, server credited (Bsrv, OnGcdArbKappaSrv)

All 12 bd_arbiter rows carrying the gcd_hw kappa text gain one results string and 6 citations
(`design_gate_srv`, `design_srv_tight`, `design_gate_held`, `design_held_tight`, `design_nonvacuous`,
`cons_srv_neg`). The string gives:
- **D1:** gate-level safe for kappa <= 0.080163500491 and violated from 0.080163500492. The
  counterexample is the bare cell, which as a 7j run (`h21_7j_bare`) is not four-phase.
- **D2:** held four-phase forms, safe for kappa <= 0.216552148868 and violated from 0.216552148869
  (fork2, through 7g).
- Whether gcd_hw ever runs the bare race (H_SETTLED) decides which of the two applies. That
  question is open.
- **cons:** h21 and o1x fail at kappa = 0, so D1 has no safe kappa under cons. D2's 0.1288 is not
  decided.

Further citations: rt1b also cites `h21_*` and `g2m3_held_rt1bs`, and a0_fork_client2 cites
`fork2_*`.

## 3. Self-audit 4 (Bsa4, SelfAuditB7)

- **bd_arbiter.rt1b.** The row-level hypothesis "server-free form (smin, A0 route to ustate, ustate
  O6 not credited)" contradicted the row's inequality (`... + smin + wa0s + qr + ...`). It is
  replaced by H_SERVER_MIN, which names the three credited terms.
  - A new results string says that the server-free numbers (0.0443, Bkx19's bracket,
    rt1b_gate_unsafe) belong to OnGcdArbKappa's server-free ARC FORM, not to this row's inequality.
  - Bkx19's "The whole kappa_ex - kappa* (~3.9e-6) is the 1 fs grid" now reads "NOT proved"
    (self-audit finding 3; it was in the JSON too).
- **Superseded sentences removed.**
  - bd_mux.uj_env_latency_req: "No counter-run."
  - bd_mux.uj_env_latency_ctl: "Sufficient; necessity not shown (...)."
  - bdc_muxn.uj_env_latency_req: ", not probed for muxn".
  - bd_flink.qfb_first: "no flink counter-trace". The self-audit's JSON table also lists this one
    as stale, so four sentences are removed, not three.
- **boundary_point** (new field) on bd_mux.uj0_env_latency_req_max, bd_mux.uj_env_latency_ctl and
  bd_flink.qfb_first:
  - the refuted point is the binary '<=' form at slack 1;
  - it is 2 ticks from the row's +1 form;
  - necessity of the +1 form itself is not shown;
  - `refuted_by` names claimX1_false / claimC1_false / q1_false;
  - `necessity_scope` gets the same sentence.
- **H_SPREAD_CORRELATED.** The kappa hypothesis entry now says it IS the lit model
  (`SelfAuditB7.spread_corr_iff`, cited): a renaming, not an independent hypothesis.
- **+W under H_W_BOUND.** On the 2 bd_steer rows this is now PROVED (`steer_win_bound`,
  `steer_win_bound_witness`, cited). On the other 69 x_window rows it is UNPROVED (by analogy only).
- **FASTRISE ack_flush.** The row is not necessary for every DACK >= 3
  (`SelfAuditB7.flush_not_necessary_all`, cited, role not_necessary). Before, it was shown only for
  DACK = 3.

## 4. H_ARB_EXCL (Bbr, ContractBridge)

The new field `c_contract` is set to `{field: H_ARB_EXCL, status: not_derivable}`, citing
`arb_excl_not_derivable` (counter_trace) and `arb_excl_of_window` (partial). It is on the four
grant-exclusion rows: bd_arbcell.settled_exclusion, bd_arbcell.handover_overlap, bd_arbiter.rt1 and
bd_arbiter.rt1b. The basis text says that the window form covers one arbitration only, and that C's
amerge_inv needs H_ARB_EXCL at every tick.

## 5. H_SEL_STABLE, H_PWR_SRC (Bfb2, LutFbBridge2)

- **bd_mux.bundled_s_setup / bundled_s_hold.** These rows get `c_contract`: C's LutFb for uj0 / uj1
  needs H_SEL_STABLE. Citations: `muxJ0_lutFb`, `muxJ1_lutFb`, `gated_phases`, and
  `sel_glitch_breaks_uj0` (counter_trace). The basis text says that no Lean theorem derives
  H_SEL_STABLE from these rows' pin setup / hold.
- **bd_src.** It has no row in this file. So both hypotheses go into a new hypotheses entry,
  "H_SEL_STABLE / H_PWR_SRC (C-bridge LUT premises)", citing `src_lutSI`, `src_witness` and
  `muxJ0_witness`.

## Not done / judgement calls

- **Other +1 boundary rows.** Many other sufficient+necessary_at_boundary rows also carry a strict +1
  (bd_latch_rst, bd_pipe.lat_lumped, the rt2 / amerge3 cascade rows, uxa/uya_rtz_env,
  bd_merge.isochronic_forks, bd_mlink.qfb_first). Bsa4 did not check them, so they get no
  boundary_point.
  - Some rely on CElemStrict's strict boundary_x and may be fine.
  - bd_mlink.qfb_first looks like flink's twin and should be checked next.
- **Rows that get c_contract.** H_ARB_EXCL is recorded on the four grant-exclusion rows only, not on
  the rt2 ack-exclusion rows or bdc_amerge*. H_SEL_STABLE goes on the select setup / hold rows, not on
  the join env_latency rows.
- **D2's cons minimum.** 0.1288 is quoted as the script's relaxation kappa*. It is not decided in Lean.
