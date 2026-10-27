# B-cell-constraints (probe P2): the cells' exact timing conditions as machine-readable data

Shard B, Phase 2 item B, 2026-10-27. Outputs:
- `formal/out/cell_constraints.json` (schema `cell_constraints/1`, 84 entries plus 4 global
  hypotheses);
- `formal/out/cell_constraints.md` (a short companion with a table of every entry).

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

**Status counts.** 65 proved, 19 unproved.

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
