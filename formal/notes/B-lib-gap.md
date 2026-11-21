# B-lib-gap: library coverage audit, and `bd_steer`'s select timing made exact

Probe Blt (shard B, Phase 2), 2026-10-27. New Lean file:
`formal/lean/Formal/Cells/LibGapSteer.lean` (core Lean only). JSON drafts
(not merged; the JSON and its generator were not edited):
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Blt/draft_entries.json`
(made by `draft_entries.py` in the same directory). No route, no board, no toolchain run.

## 1. `bd_link_dctl.lt_first` is deprioritised

`bd_link_dctl` is reached only through `bd_link_dc`, `bd_pipe_dc`, or `bd_link`
under `` `define BD_LINK_DC ``. Nothing shipped turns that on: `bdc/emit.py`
never emits `bd_link_dc` or `bd_pipe_dc`, `cells/hw/build_hw.sh` does not set
`BD_SYN_DEFS`, and the only places that pass `-DBD_LINK_DC` are the opt-in
`BD_SYN_DEFS` hooks (`cells/flow.sh:278`, `bdc/fusion_bench.py:268`).
B-gcd-cells.md re-emitted gcd_hw with `BD_LINK_DC` undefined, so its 46
`bd_link` instances are `bd_link_ctl` (= `bd_c2n`) plus `bd_latch`. The cell's
own header calls it "an experiment, and on xc7 a failed one ... not a
production option". So the row stays `unproved` / `partial`. I did not work
on it, and nothing in gcd_hw depends on it.

## 2. Coverage table (every module in `cells/rtl/*.v`)

"Spec" = a handshake or function theorem in `Formal/Cells` (C's `Formal/Net`
operator files are named where they are the only spec). "Rows" = entries in
`formal/out/cell_constraints.json` (with their exactness). gcd = instance count
in gcd_hw (B-gcd-cells.md).

| cell | spec theorem | timing rows (exactness) | gap | gcd |
|---|---|---|---|---|
| bd_c2 (+_set, _norst) | CElemFn, CElemTiming, CElemCore | 4: pulse_width exact; env_latency s+n; sel_order s+n@inst; reset_width s | reset_width necessity | 153 |
| bd_c2n (+_set) = bd_link_ctl | CElemFn, LinkHandshake | 4 (same as bd_c2) | as bd_c2 | 184+2 |
| bd_c3 (+_norst), bd_c4 | CTree, CTreeTimed | 4 each (as bd_c2) | as bd_c2 | 10, 14 |
| bd_ctree | CTree.reachable_eq_flat | node_fork s; ack_wait exact | tree-level necessity | 3 |
| bd_fork | none in Cells (C: OpsFork.fork_op; Gen) | **none** | delegated: ctree rows + consumer bundling rows. Draft row `bd_fork.delegated` | 52 |
| bd_join | none in Cells (C: OpsJoin.join_op) | **none** | as fork. Draft row `bd_join.delegated` | 38 |
| bd_steer | LibCtlMergeMux, OpsTimed.steer_ok, C OpsSteer | bundled_s_setup and _hold: **s only, lumped arcs** | **closed here: exact, per pin** | 38 |
| bd_bd2dr | LibCtlMergeMux.bd2dr_t/f | none (also_applies_to of the steer rows) | LibGapSteer applies verbatim (same INIT, d for s) | 0 |
| bd_dr2bd | LibCtlMergeMux dr_* | **none** | no timing row (bdc never emits it) | 0 |
| bd_src, bd_snk | LibEndMemMlink src_K; Gen | none | none needed: constant data; src's pulse widths are the consumer's C1 | 4, 16 |
| bd_latch | Latch, Bundling | 10 (setup/hold s+n@boundary; setup_pulse s) | setup_pulse necessity | 184 |
| bd_latch_rst | Latch, ConstraintsLatchRst | 4 | reset necessity | 0 |
| bd_delay | Bundling, PipeTimedN | 4 (sym s+n@boundary; FASTFALL, FASTRISE s) | flush necessity | 287 |
| bd_delay_gated | GcdCells, ConstraintsFastFall | gate: **s** (one counter-run) | general necessity (see section 5) | 29 |
| bd_datamux | LibCtlMergeMux, ContractsMux | none of its own (bd_mux.bundled_z_data) | none | 21 |
| bd_link | LinkHandshake, LinkTimed | via the 7 bd_pipe rows | as bd_pipe | 46 |
| bd_pipe | PipeTimed(N), PipePerPin | 7 (sel_order s+n@inst, rest s) | necessity of lat/boundary rows | 63 |
| bd_link_dctl | LinkHandshake.dctl_ok0/1 (untimed) | lt_first **unproved, partial** | not shipped (section 1) | 0 |
| bd_link_dc | RulesKL | 2 s | not shipped | 0 |
| bd_pipe_dc | **none** | **none** | not shipped | 0 |
| bd_arbcell | ArbBinary, ArbKleene, ArbInvolution, ... | 5 (req_separation s+n; grant_skew, bbm s) | grant_skew/bbm necessity | (9 inside bd_arbiter) |
| bd_arbiter | ArbHeldTimed(2), ArbA0Fork, ... | 15 (2 s+n; rest s) | as listed in JSON | 9 |
| bd_mux | LibCtlMergeMux, MergeMuxSI, OpsTimedMux, MuxRtzTimed | 14 (bundled_s_* **s, lumped**) | per-pin exact select (uj0/uj1 have feedback; the ctl_req fork is rule K, C pending) | 21 |
| bd_merge | MergeMuxSI, OpsTimedMux | 8 | none for gcd | 0 |
| bd_mlink(_ctl) | LibEndMemMlink | qfb_first s+n@boundary | none for gcd | 0 |
| bd_flink(_ctl) | ConstraintsMore | qfb_first s | necessity (not shipped in gcd) | 0 |
| bd_mem | LibEndMemMlink, ConstraintsMore | 4 s | necessity (not in gcd) | 0 |
| generated bdc_amerge2/3, bdc_muxn3 | AMerge*, MuxN3* | 5, 9, 7 | (generated, not cells/rtl) | 7, 1, 1 |

The largest gap for gcd_hw was `bd_steer`. It sits on every loop exit
(38 instances), and gcd_hw_hypotheses.md lists its H_SEL_PIN hold half as
unchecked. Its rows were sufficient-only, with the per-pin arc difference left
out of the model and charged as margin. `bd_fork` and `bd_join` (90 instances)
have no row, but they have no LUT of their own, so their timing belongs to the
C-tree and consumer rows (draft `*.delegated` rows). I added no theorem for
them because one would be vacuous.

## 3. What `LibGapSteer.lean` proves

Problem statement. **Assumed:**
- **H_PIN_READ.** Each steer output O_b (O5 = req0, O6 = req1) at time t is the
  REAL INIT function (`req0B/req1B`, proved `req && !s` / `req && s`) of `req`
  read at `pr.σ t` and `s` read at `ps.σ t`. Each read map lies in its own
  window `[t - hi, t - lo]`, which includes the wire, the site pin and that
  pin's own arc to that output. Read maps need not be monotone.
- **H_REQ_PULSE.** One token: `req` at its driver is high exactly on `[R, F)`.
- **H_S_STABLE.** `s` at its driver equals the token's condition `v` on
  `[S0, S1)`. Outside that window it is arbitrary (binary, or X in the Kleene
  form).

**Spec `SpecOK`:** `O_b t = req(pr.σ t) && (v == b)`. This is OpsSteer's `lut`
field for one token: the selected branch is the request read through its pin,
and the unselected branch is 0.

**Proved:**
- `steer_box_exact` (headline): take a nonempty box, `pr` in [Rlo, Rhi] and
  `ps` in [Slo, Shi], with R < F. Then SpecOK holds for every read-map pair in
  the box and every admissible s **iff** `S0 + Shi ≤ R + Rlo` (H_SETUP_PIN) and
  `F + Rhi ≤ S1 + Slo` (H_HOLD_PIN).
- `steer_pin_exact`: the same iff with fixed per-pin delays `dr`, `ds`. Use it
  per corner realisation, under a correlated corner model.
- `steer_pin_ok`: the sufficient half for any read maps. `steer_both`: both
  outputs together, four inequalities. `steer_tokens`: any number of tokens,
  with per-token windows. `steer_pin_ok_K`: the Kleene form, where s may be X
  outside its window and the outputs stay definite (through `req0K/req1K`).
- `setup_needed` / `hold_needed`: if either inequality fails, SpecOK fails on
  EITHER output, at `R + dr` or `F - 1 + dr`. The select used is `sAdv`, which
  really changed at S0 and S1.
- Counter-traces: `spurious_token` (setup short by 100 ps, so the UNSELECTED
  branch O5 rises: a token goes down the wrong loop exit) and
  `late_hold_glitch`.
- Non-vacuity: `witness_box`, `witness_run` (the selected O6 is low at 1200,
  high at 1400 and low at 3400, while O5 stays low) and `witness_hyps`.

**NOT covered:**
- the `uack` OR (OpsTimed.steer_back, H_ACK_SKEW);
- data bundling at the receivers (their latch rows);
- where S0 and S1 come from: S1 is the library contract,
  OpsTimed2.steer_hold_of_ackfall;
- a mid-rail select inside the NMOS mux tree (H_KLEENE_LUT, grade B);
- internal mux-tree delay, which is folded into the per-pin arcs;
- correlated pin delays: box necessity assumes the two pins independent.

What it changes. The JSON's exactness for `bd_steer.bundled_s_setup/_hold`
can move from `sufficient` (lumped) to `exact` (per pin). The "per-pin margin"
arcs become part of the checked inequality: `ps_b` = wire + SP[I1] + arc(I1→O_b)
and `pr_b` = wire + SP[I0] + arc(I0→O_b), per output. Rule E (setup, no site
pins) is optimistic by up to SP[s pin].hi − SP[req pin].lo plus the arc
difference. In the box with s on A1 and req on A6 that is 516 − 2 + 152 − 44 ps
(SLOW_MAX of A1's site pin, FAST_MIN of A6's, O5 arcs from the prjxray columns
quoted in the JSON conventions; a box bound, not a measured route).

## 4. Check

`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/LibGapSteer.lean`
prints `[bchk] OK: formal/lean/Formal/Cells/LibGapSteer.lean`. `#print axioms`
on all ten main theorems shows only `propext`, `Quot.sound`, and `Classical.choice`
(the exact/box theorems, by contradiction). There is no sorry, admit,
native_decide or declared axiom.

## 5. Left open (ranked for gcd_hw)

1. `bd_mux.bundled_s_*`, 21 instances: the same per-pin exact form at
   uj0/uj1. It is harder because those LUTs feed back to themselves, and the
   ctl_req fork is C's rule K, which is failing.
2. `bd_delay_gated.gate`, 29 instances: general necessity. A stale 1 left at
   stage i propagates through every later AND while the gate is high, so each
   per-stage H_GFLUSH is plausibly necessary when the chain was full at the
   gate's fall. This is not proved: "early" must be defined against T + L N,
   and a large tap delay can make it vacuous.
3. Necessity rows for the `s`-only entries in the table.
