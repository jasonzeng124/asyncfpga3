# B-cell-constraints (probe P2): the cells' exact timing conditions as machine-readable data

Shard B, Phase 2 item B, 2026-10-27. Outputs:
- `formal/out/cell_constraints.json` (schema `cell_constraints/1`, 84 entries plus 4 global
  hypotheses);
- `formal/out/cell_constraints.md` (a short companion with a table of every entry).

**Updated by probe P4 (same day): see the last section.** The counts and the
"unproved" list below are P2's; the current ones are 87 entries, 82 proved,
1 partial, 4 unproved.

No Lean was edited and no route or measurement was made. No git command that changes
anything was run.

## Problem statement

**Assumed.** The obligations, inequalities, exactness claims and rule mappings in
`formal/notes/B-obligations.md`, and in the B-*.md notes it cites, are correct as written.
I re-read the Lean statements for the arbiter (ArbHeldTimed/2 `RT1`, `RT1b`, `RT2`, `RT2b`,
`A0Fork2`), the BRAM port (`MemPort`) and mlink `H_QFB_FIRST`, and transcribed them from
the source. Everything else is transcribed from the notes.

**Produced.** For every cell obligation shard B has found, the JSON gives:
- the inequality as two paths of arcs in A's `EndpointOK` shape:
  `sum(hi over a data path) + margin <= sum(lo over a request path)`, from a stated common
  launch event;
- the Lean theorems that justify it, with each theorem's role;
- its exactness;
- whether it needs per-pin site delays, and for which pin roles;
- the project rule that approximates it, and how;
- the corner rule.

**Checked.**
- The JSON parses (`python3 -I -m json.tool`).
- A validator checked all 316 Lean references: each name is declared (`theorem`, `def`,
  `structure`, ...) in the cited file, and that file is git-tracked. The one reference to
  another branch was checked with `git show origin/claude/audit:...`.
- The validator also checked the schema fields and the arc kinds, and that every `proved`
  entry cites at least one sufficient or exact theorem.
- 0 errors.
- Negative control: a misspelt theorem name, a name in a file that does not declare it,
  and a bogus arc kind were each reported (3/3).

**NOT covered.**
- No Lean was re-run. "Proved" means the name exists in a tracked file and the source note
  says it checks clean.
- The path decomposition (which arc goes on which side) is my transcription. No Lean
  statement is about the JSON.
- That the JSON form of an entry equals its Lean hypothesis is checked by reading, not by
  machine. Nothing ties the JSON to Lean, unlike C's `extract.py` instances.
- No routed number is new. The `evidence` strings quote B/C notes (nextpnr
  9c732bc6303458df routes).

## Schema (summary; the full conventions are in the JSON's `conventions` block)

```
{ schema, produced_by, routed_numbers_provenance,
  conventions: { form, combine, names, arc_kinds{...}, corner_rule, status, exactness,
                 rule_verdicts, check_scope, guards_in_rules, tcheck_mapping },
  cells_pin_maps: { module: "INIT and logical pin roles" },
  constraints: [ {
     id, cell, [bit_kind | variant], also_applies_to?, catalogue_row,
     obligation, inequality (text, Lean variable names),
     combine: "all" | "any",
     forms: [ { launch, data_paths: [[arc]], request_paths: [[arc]], margin_ps, note? } ],
     provides?, refers_to?,
     lean: [ {file, name, role, note?, branch?} ],
     status: "proved" | "unproved",
     exactness, exactness_note,
     site_pins: { needed, roles[] },
     rule: { rule, source?, verdict, missing?, detail? },
     corner: { mode: "1C" | "1C_both_corners_required" | "n/a", rule, note? },
     check_scope, evidence? } ],
  hypotheses_not_inequalities: [ {id, statement, lean, check} ] }
arc = { kind: lut_arc | site_pin | wire | feedback_wire | line | env | cell_param,
        from, to | name, spec, [edge, path], pin_role?, lean_sym?, note? }
```

### Format decisions and why

**The form is A's EndpointOK.** A-substrate section 2 recommends exactly this. The form is
also the same race as shard C's 10a/tcheck instance (`inst / setup / req / data / arc`,
C-10e):
- node 0 = launch;
- every path is a chain of arcs;
- the data nodes are the ends of the data paths;
- req is one node that every request path ends in (earliest change);
- setup = `margin_ps`.

C had not defined a cell-constraint schema; C-10e says this file "does not exist yet". So
the JSON is a template one level above C's `.tc` format: cell-relative pins that a front
end (like `extract.py`) instantiates per routed instance.

**`env` arcs.**
- Many exact conditions compare a cell's own loop with its environment's answer: `E`,
  `ER`/`EA`, `Won`, `smin`, `Td`/`Toff`.
- I kept those as named `env` segments with a spec, and did not invent paths. A checker
  resolves them by walking the routed netlist when the neighbour is inside the design (as
  C-10d's RT_FB does). Otherwise they remain environment hypotheses.
- `check_scope` says which applies.

**Site pins are explicit arcs.**
- The Lean statements often lump the site pin into a wire (`dwmax`; in the arbiter every
  `w*` is "route including the physical pin's site delay").
- I split them out as `site_pin` arcs with a `pin_role`, so that a checker with only the
  SDF sees exactly which terms it is missing.

**Same element on both sides** (setup_pulse, ctree node_fork).
- The enable wire's or the leaf path's hi and lo both appear. That is the exact form
  (`ehi - elo` is the spread).
- Under C's FixedRun reading it is CPPR-pessimistic, as C-10a's `corr` example shows.
- This is noted in `tcheck_mapping`.

**One entry per obligation per cell.**
- C-elements are split by module (`bd_c2`, `bd_c2n`, `bd_c3`, `bd_c4`), because the
  feedback pin and the theorems differ.
- Latch bits are split by bit kind (odd, pair.O5, pair.O6, `_rst`), because the feedback
  pin is I2 or I4 and the O5 arcs differ.
- Composite instances (arbiter ua_k, merge uxa) point to the base entry with `refers_to`.

## Coverage of the brief

All present:
- C-element: Dmax pulse width (exact), env-latency fork (sufficient + necessary by the
  audit's `drop_env_latency_cex`, on origin/claude/audit `audit/lean/B/W_CElem.lean`), and
  per-pin H_SEL_ORDER.
- Latch: setup data part with the feedback (I2/I4) arc and SP[fb]; setup pulse part
  (H_PW); hold (rule H).
- Delay lines: symmetric chain; FASTFALL uniform H_FLUSH plus the exact per-stage form
  with rule F's in-flight term; FASTRISE/DACK `H_ACK_FLUSH`.
- Link/pipe: the 6f/6g contract per boundary (`H_SELORD i`, lumped `H_LAT i`, `H_I b`,
  `H_H b`, `H_PW`, reset/flush lines, data lead, output).
- ctree (5f): the per-node static fork, rewritten per path as
  `P_hi + fmax <= P_lo + dist_min + E`, which equals the Lean `Spread` form.
- Arbiter:
  - rule J exact form, both clients, with site pins (and J');
  - RT1 and RT1b as `any` of race and structural;
  - RT2/RT2b, all 8 fields;
  - request separation, as `not_static`.
- mux H_MUX_RTZ, cell and env form.
- merge.
- mlink/flink H_QFB_FIRST.
- bd_mem's BRAM boundary: setup, hold, rdata, clock width.
- Also: bd_link_dc rules K'/L' (RulesKL), dctl H_LT_FIRST, and bd_arbcell grant skew /
  overlap / BBM.

**Status counts (P2; superseded, see "Update (probe P4)").** 65 proved, 19 unproved.

The unproved entries, and why:
- `bd_c2/c3/c4.sel_order`: FifoFidelity/PipePerPin use only `INIT_c2n`.
- `bd_latch_rst.*` (3): no timed theorem for the `_rst` INIT. `rst0_kleene` makes it the
  latch mux when rst = 0, but nothing composes that with `capture`.
- `bd_delay[FASTFALL].flush_per_stage`: stated in B-bundling as exact; only the uniform
  form is proved.
- `bd_delay_gated.gate`: Kleene only.
- `bd_link_dctl.lt_first` and `bd_mlink/flink.qfb_first`: untimed schedule restrictions.
  The inequality is the Lean doc's physical reading.
- `bd_mux.bundled_s_setup/hold`, `bundled_z`, `isochronic_forks`, `bd_merge.bundled_z`,
  `bd_merge.isochronic_forks`: hypotheses of untimed proofs.
- `bd_mux.uya_rtz_env`: mirror of the uxa theorem.
- `bd_mem.clk_high_width`: the width bound is proved; the comparison with tPWH is not.

**Rule mapping counts.**
- 59 entries have no rule at all.
- 10 have missing_term: I ×4 bits, F ×2, K, L, `boundary_I`, C.
- 5 are H "conservative in arcs, missing site pins".
- 2 are J "exact in arcs, missing site pins".
- 70 of 84 need site pins in their exact form.

## Corrections and caveats found while transcribing

- **`B-obligations.md` row P7 is stale.** It says "NOT FORMALISED in B: rule K is not
  formalised". Probe Bk (`RulesKL.lean`, commit 96664a6) has since proved K'/L' sufficient
  (`setup_of_KL`) and the coded K and L insufficient (`counter_K`, `counter_L`). The JSON
  uses RulesKL.
- **`B-obligations.md` marks CTreeTimed/PipePerPin as [untracked].** They are tracked now
  (commit 718f5a0 for 5f). The validator found every cited file tracked.
- **`B-obligations.md` gives `RT1b` only via the ArbCorners names.** The JSON uses the exact
  Lean definition (ArbHeldTimed2 l.263):
  `wr2g + g2f <= wr2s + Rf2 + smin + wa0s + qr + wq + g1rq ∨ g2f <= g1rq`.
  The RT2b fields and `A0Fork2` (`wa01 <= wa0s + qr + wq + g1rq + wg1`) are from l.351-361.
- **The Lean arbiter models are written in the 7e rise/fall OR channel** (`qr`/`qf`,
  `c1r`/`c1f`).
  - ArbCorners evaluates them with rise = fall within one column.
  - The JSON names the edge in `lean_sym`, but each arc is to be read from ONE corner
    column.
  - It must never be read as "rise = FAST, fall = SLOW" (`prj_is_mix`).
- **The lumped `env_latency` (from the inputs, with LUT spread `dlmax - dlmin`) and the
  per-pin `sel_order` (from the node edge, no LUT spread) are different reference
  instants.**
  - C's RT_FB is the node-edge form.
  - A checker should evaluate `sel_order` where pins are known, and `env_latency` only
    when they are not.
- **`bd_mem.setup`'s `tPay` is at the RAM pins.**
  - The payload route skew is the requester's bundling (H_FOUR_PHASE_ENV), not in
    `setup_ok`.
  - `rdata_before_ack`'s route-skew terms are added in the JSON and are NOT in the Lean
    theorem; the entry says so.

## Reproduction

The generator and the validator are scratch files, not in the repo (the brief allows only
the three output files):

    /tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/p2/gen.py
    /tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad/p2/validate.py

They will not survive the session. If the JSON is to be maintained, they should be
committed under `formal/tools/` by someone with that write scope. Until then, edit the
JSON directly and re-validate with `python3 -I -m json.tool` plus a name grep.

## What would make it stronger

1. A Lean `structure CellConstraint`, with the JSON emitted from Lean, so that each form is
   definitionally a cited hypothesis. About 1 day. This closes the "transcription by
   reading" gap.
2. A per-instance front end (an `extract.py` extension) that instantiates `forms` on a
   routed design, starting with:
   - `sel_order` / `env_latency`, the most likely to bite (C-10f);
   - `setup_data` with the feedback arc;
   - rule J'.

   tcheck already runs the resulting race instances.
3. Prove the five unproved per-INIT extensions (sel_order for bd_c2/c3/c4, bd_latch_rst
   timing). Each is a small instantiation of an existing proof.

## Update (probe P4): the P3 / Bg2 theorems folded in

Edited: `formal/out/cell_constraints.gen.py` (now the committed generator beside
the JSON; the scratch paths under "Reproduction" are obsolete), the regenerated
`cell_constraints.json`, `cell_constraints.md` and this note. No Lean edited, no
route, no measurement, no git command that changes anything.

Reproduce:

    python3 -I formal/out/cell_constraints.gen.py formal/out/cell_constraints.json
    python3 -I formal/out/cell_constraints.validate.py formal/out/cell_constraints.json

Validator: 87 constraints, 5 hypotheses, 448 Lean references in 40 files,
**0 errors**. Negative control: renaming one cited theorem
(`gflush1_of_lat` -> `gflush1_of_latX`) in a scratch copy gives exactly 1 error
naming it. The validator also requires each cited file to be git-tracked, so
the untracked `Formal/Cells/OpsTimed.lean` is not cited (no B note on it yet).

Sources: `B-constraints-more.md` (P3), `B-gcd-cells.md` (Bg2),
`B-arb-overlap-race.md` (Bov) and `B-ternary-on-bits2.md` (Bx2), the B notes
committed after the P2 JSON. No `B-ops-timed.md` or `B-amerge.md` exists.

**Counts.** 87 entries: 82 proved, 1 partial, 4 unproved. The validator knows
only `proved` / `unproved`, so the partial entry is `status: unproved`,
`exactness: partial` (the vocabulary in `conventions.exactness` now lists it).
Site pins needed: 74 of 87. Rule verdicts: none 60, missing_term 11 (adds
bd_delay_gated's rule F term), exact_structure_missing_site_pins 2.

Per entry (theorem names are in the JSON and checked by the validator):

| entry | was | now | main theorems | exactness |
|---|---|---|---|---|
| bd_c2/c3/c4.sel_order | unproved | proved | ConstraintsSel.sel_phase_gen + isC_c*; sel_order_of_lat_gen; sel_runt_gen; ce_c*_sel_order_fails, ce_c*_not_fifo; cjG_clean | sufficient+necessary_at_instance |
| bd_latch_rst.setup_data | unproved | proved | ConstraintsLatchRst.capture_rst; counter_rule_I_rst | sufficient+necessary_at_boundary |
| bd_latch_rst.setup_pulse | unproved | proved | capture_rst_from_request | sufficient |
| bd_latch_rst.hold | unproved | proved | capture_rst; counter_rule_H_rst | sufficient+necessary_at_boundary |
| bd_latch_rst.reset (new) | none | proved | reset_loads, reset_holds, capture_rst (H_RST_DONE) | sufficient |
| bd_delay[FASTFALL].flush_per_stage | unproved | proved | ConstraintsFastFall.slow_not_early_ps; flush_stage_of_uniform; ruleF_counter_violates_stage | sufficient (necessity on rule F's witness only) |
| bd_delay_gated.gate | unproved | proved | ConstraintsFastFall.gated_not_early/gated_fast_edge/gated_dip_glitch; GcdCells.no_early, gflush1_of_lat, gflush_of_lat, fast_fall, rises, rise_by; flush_needed | sufficient |
| bd_mux.uya_rtz_env | unproved | proved | ConstraintsMux.mux_rtz_env_safe_uya | sufficient (as uxa) |
| bd_mux.bundled_s_setup/hold | unproved | proved (join pins) | uj0/uj1_unsel_low_timed, uj*_selected_c2, j*_sel_is_c2, j0_s_x_hazard | sufficient |
| bd_mux.bundled_z, bd_merge.bundled_z | unproved | proved (classic) | bundled_z_capture, dm_settles (+ usel_high/low for merge) | sufficient |
| bd_mlink.qfb_first | unproved | proved | ConstraintsMore.mlink_qfb_first_timed, qfb_clean_form; qfb_counter / qfb_clean | sufficient+necessary_at_boundary |
| bd_flink.qfb_first | unproved | proved | flink_qfb_first_timed, qfb_clean_form | sufficient |
| bd_mem.clk_high_width | unproved | proved | MemPort.clk_high_ok (+ clk_low_ok) | sufficient |
| bd_link_dctl.lt_first | unproved | partial | ult_kleene, lt_settles, lt_first_window, lt_opposite_x | partial (LUT level; link to ltFirst open) |
| bd_mux/bd_merge.isochronic_forks | unproved | unproved | (untimed only) | note lists the per-pin partial coverage |
| bd_steer.bundled_s_setup/hold (new) | none | unproved | LibCtlMergeMux steer_*, Net/OpsSteer.steer_op (untimed) | sufficient+necessary_untimed |

Forms changed to match the theorems:
- `qfb_first`: the strict `<` (margin 1 ps) is now `<=` (margin 0), per
  `qfb_clean_form` (`fhi <= wlo + elo`), tight by one tick on `qfb_counter`.
  uq's I2 and I1 arcs and ux's I0 arc are now explicit arcs, since the Lean
  windows include them.
- `flush_per_stage`: the LUT2 pin arcs (I0 on the data side, I1 on the
  request side) are now explicit: each Lean window includes its arc. They
  cancel only with prjxray's flat O6 arc at one corner, which the old note
  assumed.
- `bd_mux.bundled_s_*`: the uj pin arcs added for the same reason
  (Gate windows = route + site pin + arc). The inequality is unchanged.
- `bd_delay_gated.gate`: two forms (stage 1 behind the ungated `uor` and
  `g[0]` hops, GcdCells.gflush1_of_lat; stage i >= 2, gflush_of_lat). Rule
  F's verdict is now `missing_term` `(p i).hi - (q i).lo`.
- `bd_mux.uya_rtz_env`: the symbols are now uya's (`Wuy`, `wuy`, `dl0` of
  uj0). Before, they were copied from uxa.
- `bd_mux/bd_merge.bundled_z`: the JSON form (from the join edge) is kept. The
  Lean hypothesis is the consumer-side `Tz + zhi <= Ton + ehi`. Getting from one
  to the other needs the request path's lower bound, which is a composition
  and not one theorem; the note says so.
- `bd_latch_rst.reset`: H_RST_DONE's form charges the enable at its lo bound,
  where Lean has hi. That makes the form stronger (conservative), and the note
  says so.

Other additions:
- `bd_arbcell.handover_overlap` now also cites ArbOverlapRace `grant_cap`,
  `cell_cap_consistent`, `cell_cap_box` and `cell_never_203`. For any digital
  trace, the grant overlap is at most |O5 - O6 arc of q's pin|: <= 33 ps at a
  consistent corner, <= 112 ps in the box.
- New global hypothesis H_LUT62_SHARED_READ: `TernaryOnBits2.SiteSync`,
  `ArbOverlapRace.Decomp` (H_SHARED_Q_PIN) and `b_cancel`.
- `cells_pin_maps` has new rows for bd_steer and for bd_delay_gated as bdc
  instantiates it.

Still open:
- isochrony needs a timed mux/merge trace model (1-2 days);
- dctl needs a timed model to link H_LT_FIRST_T to `ltFirst` (about 1 day);
- general necessity of H_FLUSH_STAGE;
- a select-level theorem for bd_steer on INIT `8888_8888_2222_2222`, small,
  in the style of `FifoFidelity.sel_phase`.

None of the proved entries is checked on a route by any rule.

