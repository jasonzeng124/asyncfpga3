# cell_constraints.json: the cells' exact timing conditions, as data

Shard B, Phase 2 item B (probe P2, 2026-10-27). Companion to
`cell_constraints.json` (schema `cell_constraints/1`). No new Lean, route or
measurement: every entry is transcribed from `formal/notes/B-obligations.md`
and the B-*.md notes, and every cited Lean name was checked to be declared in
the cited, git-tracked file (316 references, 0 missing; one is on
`origin/claude/audit`). Details and limits: `formal/notes/B-cell-constraints.md`.

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
- `status`: `proved`, or `unproved` when the inequality is not a Lean
  statement (extrapolated, the physical reading of an untimed result, or no
  theorem at all).
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

## Entries (84, plus 4 global hypotheses that are not inequalities)

| id | status | exactness | site pins | rule: verdict |
|---|---|---|---|---|
| `bd_c2.pulse_width` | proved | exact | yes | none |
| `bd_c2.env_latency` | proved | sufficient+necessary | yes | none |
| `bd_c2.sel_order` | unproved | unproved | yes | none |
| `bd_c2.reset_width` | proved | sufficient | yes | none |
| `bd_c2n.pulse_width` | proved | exact | yes | none |
| `bd_c2n.env_latency` | proved | sufficient+necessary | yes | none |
| `bd_c2n.sel_order` | proved | sufficient+necessary_at_instance | yes | none |
| `bd_c2n.reset_width` | proved | sufficient | yes | none |
| `bd_c3.pulse_width` | proved | exact | yes | none |
| `bd_c3.env_latency` | proved | sufficient+necessary | yes | none |
| `bd_c3.sel_order` | unproved | unproved | yes | none |
| `bd_c3.reset_width` | proved | sufficient | yes | none |
| `bd_c4.pulse_width` | proved | exact | yes | none |
| `bd_c4.env_latency` | proved | sufficient+necessary | yes | none |
| `bd_c4.sel_order` | unproved | unproved | yes | none |
| `bd_c4.reset_width` | proved | sufficient | yes | none |
| `bd_ctree.node_fork` | proved | sufficient | yes | none |
| `bd_ctree.ack_wait` | proved | exact | no | none |
| `bd_latch[odd].setup_data` | proved | sufficient+necessary_at_boundary | yes | I (also K, L for bd_link_dc): missing_term |
| `bd_latch[odd].setup_pulse` | proved | sufficient | yes | none |
| `bd_latch[odd].hold` | proved | sufficient+necessary_at_boundary | yes | H: conservative_arcs_missing_site_pins |
| `bd_latch[pair.O5].setup_data` | proved | sufficient+necessary_at_boundary | yes | I (also K, L for bd_link_dc): missing_term |
| `bd_latch[pair.O5].setup_pulse` | proved | sufficient | yes | none |
| `bd_latch[pair.O5].hold` | proved | sufficient+necessary_at_boundary | yes | H: conservative_arcs_missing_site_pins |
| `bd_latch[pair.O6].setup_data` | proved | sufficient+necessary_at_boundary | yes | I (also K, L for bd_link_dc): missing_term |
| `bd_latch[pair.O6].setup_pulse` | proved | sufficient | yes | none |
| `bd_latch[pair.O6].hold` | proved | sufficient+necessary_at_boundary | yes | H: conservative_arcs_missing_site_pins |
| `bd_latch_rst.setup_data` | unproved | unproved | yes | I (also K, L for bd_link_dc): missing_term |
| `bd_latch_rst.setup_pulse` | unproved | unproved | yes | none |
| `bd_latch_rst.hold` | unproved | unproved | yes | H: conservative_arcs_missing_site_pins |
| `bd_latch.loop_bound` | proved | hypothesis | yes | none |
| `bd_delay[sym].pulse_width` | proved | sufficient+necessary_at_boundary | yes | A/B/C/D/E (edge window via SDF): none |
| `bd_delay[FASTFALL].flush_uniform` | proved | sufficient | yes | F: missing_term |
| `bd_delay[FASTFALL].flush_per_stage` | unproved | unproved | yes | F: missing_term |
| `bd_delay[FASTRISE].ack_flush` | proved | sufficient | yes | none |
| `bd_delay_gated.gate` | unproved | unproved | no | F: none |
| `bd_pipe.sel_order` | proved | sufficient+necessary_at_instance | yes | none |
| `bd_pipe.lat_lumped` | proved | sufficient | no | none |
| `bd_pipe.boundary_I` | proved | sufficient | yes | I: missing_term |
| `bd_pipe.boundary_H` | proved | sufficient | yes | H: conservative_arcs_missing_site_pins |
| `bd_pipe.rst_lines` | proved | sufficient | yes | none |
| `bd_pipe.data_lead` | proved | sufficient | yes | A: conservative |
| `bd_pipe.output` | proved | sufficient | no | consumer's own rule (I at the next stage; B/D/E at an edge-sampling consumer): different_condition |
| `bd_link_dctl.lt_first` | unproved | untimed_schedule | yes | none |
| `bd_link_dc.rule_K_corrected` | proved | sufficient | yes | K: missing_term |
| `bd_link_dc.rule_L_corrected` | proved | sufficient | yes | L: missing_term |
| `bd_arbcell.req_separation` | proved | sufficient+necessary | no | uncheckable_statically |
| `bd_arbcell.grant_skew` | proved | sufficient | no | none |
| `bd_arbcell.handover_overlap` | proved | exact | no | none |
| `bd_arbcell.bbm` | proved | sufficient | no | uncheckable_statically |
| `bd_arbcell.settled_exclusion` | proved | exact | no | none |
| `bd_arbiter.a0_fork_client2` | proved | exact | yes | J: exact_arcs_missing_site_pins |
| `bd_arbiter.a0_fork_client1` | proved | exact | yes | J: exact_arcs_missing_site_pins |
| `bd_arbiter.rt1` | proved | exact | yes | none |
| `bd_arbiter.rt1b` | proved | exact | yes | none |
| `bd_arbiter.rt2_pulse` | proved | sufficient+necessary_matched_fork | yes | none |
| `bd_arbiter.rt2_g1` | proved | sufficient | yes | none |
| `bd_arbiter.rt2_forkA` | proved | sufficient | yes | none |
| `bd_arbiter.rt2_forkG` | proved | sufficient | yes | none |
| `bd_arbiter.rt2b_pulse2` | proved | sufficient+necessary_matched_fork | yes | none |
| `bd_arbiter.rt2b_g2` | proved | sufficient | yes | none |
| `bd_arbiter.rt2b_forkA2` | proved | sufficient | yes | none |
| `bd_arbiter.rt2b_forkG2` | proved | sufficient | yes | none |
| `bd_arbiter.server_min` | proved | hypothesis | no | none |
| `bd_arbiter.alternation` | proved | sufficient+necessary | no | none |
| `bd_arbiter.ack_celements` | proved | see_refers_to | yes | none |
| `bd_mux.uxa_rtz` | proved | exact | yes | none |
| `bd_mux.uxa_rtz_env` | proved | sufficient | yes | none |
| `bd_mux.uya_rtz` | proved | exact | yes | none |
| `bd_mux.uya_rtz_env` | unproved | unproved | yes | none |
| `bd_mux.bundled_s_setup` | unproved | sufficient+necessary_untimed | yes | E (skew.py), D (screen): exact_structure_missing_site_pins |
| `bd_mux.bundled_s_hold` | unproved | sufficient+necessary_untimed | yes | none |
| `bd_mux.bundled_z` | unproved | hypothesis | yes | A: rule_is_the_check |
| `bd_mux.isochronic_forks` | unproved | sufficient+necessary_untimed | yes | none |
| `bd_merge.seq` | proved | sufficient+necessary | no | none |
| `bd_merge.bundled_z` | unproved | hypothesis | yes | A: rule_is_the_check |
| `bd_merge.isochronic_forks` | unproved | sufficient+necessary_untimed | yes | none |
| `bd_merge.uxa_feedback` | proved | sufficient | yes | none |
| `bd_mlink.qfb_first` | unproved | untimed_schedule | yes | none |
| `bd_flink.qfb_first` | unproved | untimed_schedule | yes | none |
| `bd_mem.setup` | proved | sufficient | yes | B: conservative_partial |
| `bd_mem.hold` | proved | sufficient | no | none |
| `bd_mem.rdata_before_ack` | proved | sufficient | yes | C: missing_term |
| `bd_mem.clk_high_width` | unproved | sufficient_by_arithmetic | no | none |

Global hypotheses (`hypotheses_not_inequalities`): H_LUT_FIFO / H_PIN_FIFO /
H_TREE_FIFO (C4), metastability with no deadline (C8/R3), H_RF_ASYM and
H_WIRE_RATIO.

## Read first

- **Unchecked by any rule, and on routed evidence the most likely to bite.**
  - `bd_c*.env_latency` and `sel_order`: C-10f RT_FB fails 4-12 of 64 (mean 7.2, 8 seeds, nextpnr 9c732bc6303458df) Muller-pipeline
    muller stages at slowE.
  - `bd_latch[*].setup_pulse`: the binding environment constraint on the Bt2
    routes.
  - `bd_mux.uxa_rtz_env`: about -6 ps once the guard is applied, at adversarial
    fast.
- **A project rule exists but misses a term.**
  - Rule I, K and L: the feedback-pin arc and the site-pin terms
    (`bd_latch[*].setup_data`, `bd_link_dc.rule_*`).
  - Rule F: the in-flight hop.
  - Rule H and rule J: site pins.
  - Rule C: the consumer's route skew.
- **unproved** (19): sel_order for bd_c2, bd_c3 and bd_c4 (extrapolated from
  bd_c2n); all of bd_latch_rst; the per-stage FASTFALL form; bd_delay_gated;
  dctl `H_LT_FIRST`; mlink/flink `H_QFB_FIRST`; the mux and merge bundling and
  isochrony readings; `uya_rtz_env`; the BRAM clock-width comparison.
