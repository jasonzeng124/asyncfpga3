# B-constraints-more (probe P3): timed theorems for the unproved entries of `cell_constraints.json`

Shard B, Phase 2, 2026-10-27. This probe proves the 19 entries that
`formal/out/cell_constraints.json` marks `unproved`. It does not edit the JSON;
the lead updates it from the table below. No git command that changes anything
was run. No existing Cells file was edited. One olean was compiled:
`MuxRtzTimed.olean`, which was missing. No import broke during the
concurrent Prelim -> Core port, so no wait was needed.

## Files and check command

All five files are claimed, Core Lean only, with no `sorry`, `admit`, `axiom` or
`native_decide`. Each checks clean in under 5 s:

```
cd formal/lean
for m in ConstraintsSel ConstraintsLatchRst ConstraintsFastFall ConstraintsMux ConstraintsMore; do
  PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/$m.lean
done
```

| file | imports | content |
|---|---|---|
| `Formal/Cells/ConstraintsSel.lean` | FifoFidelity | per-pin H_SEL_ORDER for bd_c2 / bd_c3 / bd_c4 |
| `Formal/Cells/ConstraintsLatchRst.lean` | Bundling, Latch | bd_latch_rst capture, reset, counter-traces |
| `Formal/Cells/ConstraintsFastFall.lean` | Bundling | exact per-stage FASTFALL flush, bd_delay_gated |
| `Formal/Cells/ConstraintsMux.lean` | MuxRtzTimed, Bundling | uya H_RTZ_ENV, H_BUNDLED_S_PIN at the joins, H_BUNDLED_Z |
| `Formal/Cells/ConstraintsMore.lean` | Bundling, LibEndMemMlink, LinkHandshake | timed H_QFB_FIRST (mlink/flink), BRAM widths, dctl ult |

`#print axioms` was run on 37 main theorems. Every one depends only on
`propext`, `Classical.choice` and `Quot.sound`, or on a subset of them.

Shared defs I added: these live in my own files only. Nothing was added to Prelim.
- `ConstraintsSel`: `IsCElem`, `CPinLut`, `exSelG`, `exPinG`.
- `ConstraintsFastFall`: `FastLineP`, `fallBound`, `Lo`, `Hi`, `riseBound`, `holdBound`.
- `ConstraintsLatchRst`: `IsRstLatch`, `RstGate`.
- `ConstraintsMux`: `JoinGate`, `DmRel`.

## Results per JSON entry

Exactness vocabulary:
- **exact-witness**: sufficient for every behaviour of the model, and a
  concrete run of the real INITs shows the inequality cannot be weakened
  (equality or one tick).
- **sufficient**: no necessity shown.
- **partial**: a weaker statement than the entry.

### `bd_c2.sel_order`, `bd_c3.sel_order`, `bd_c4.sel_order`: PROVED, exact-witness

INITs and pin maps are verbatim from `cells/rtl/bd_ce.v`:
- c2 `00E8...`: `I0 a, I1 b, I2 q, I3 rst`;
- c3 `0000FE80_0000FE80`: `I0..I2` inputs, `I3 q`, `I4 rst`;
- c4 `00000000_FFFE8000`: `I0..I3` inputs, `I4 q`, `I5 rst`.

Lemmas:
- `c3_eq` and `c4_eq` prove the INITs equal `~rst·(all + q·any)` by `lutB`
  enumeration (32 and 64 rows).
- `isC_c2`, `isC_c3`, `isC_c4` (and `isC_c2n` as a sanity check) prove the three
  C-element properties of `IsCElem`.

Model: `CPinLut n g x rst O qp`. It is FifoFidelity's `PinLut` generalised to
`n` inputs. Every pin has its own FIFO site-pin map (`H_PIN_FIFO`), and the mux
tree plus output stage is one FIFO read (`H_TREE_FIFO`).

Theorems:
- `sel_phase_gen hC P v α α' κ κ' R …` (H_SEL_ORDER: `∀ i, pq.fst κ ≤ (p i).fst (α' i)`;
  H_SEL_KEEP). Under H_SEL_ORDER the select-level excitation is `v` from the
  last arrival to the last departure, with the arrival order of the inputs
  free. Apply it with `isC_c2/3/4`.
- `sel_runt_gen`: if any input has left at its select while the feedback has
  not yet arrived at its select, the excitation is the old value `!v`. This is
  necessity at the select level.
- `sel_order_of_lat_gen` gives the JSON's arithmetic form,
  `K + pq.hi ≤ D + (p i).lo` for every departing pin, where
  `K = τ + w_hi` and `D = τ + E_τ ≥ 1`. This form implies H_SEL_ORDER.
- Counter-trace for every cell:
  - `ceG`, `ceG_runt`, `ceG_not_fifo`, `cjG`, `cjG_clean`;
  - per-cell instances `ce_c{2,3,4}_sel_order_fails` and
    `ce_c{2,3,4}_not_fifo`.

  With all other inputs held high, every INIT reduces to `a || q`, so
  FifoFidelity's run (`eI`, `OC`, `qpC`) is a run of each cell. Feedback site
  pin 6 ticks, departing pin 1 tick:
  - H_SEL_ORDER fails (`pq.fst 14 = 20 > (p 0).fst 16 = 17`);
  - the node rises at 13, falls at 19 and rises again at 22 (it oscillates);
  - no FIFO read with `hi ≤ 18` of the pin-level excitation reproduces it.

  With every pin at 1 tick the same environment gives one clean edge (`cjG_clean`).

### `bd_latch_rst.setup_data`, `.setup_pulse`, `.hold`: PROVED, exact-witness

INITs `RST0 = 00B8_00B8...` and `RST1 = FFB8_FFB8...`, pins
`I0 d, I1 en, I2 q, I3 rst`, model `Bundling.Gate` with rst as a fourth
windowed pin `[rlo, rhi]`.

- `rst_latch_on`: when rst reads definitely 0, the bit is `LatchRel` (the
  Kleene mux).
- `capture_rst`: the conclusion of `Bundling.capture` for the resettable bit,
  for both polarities. Hypotheses:
  - H_SETUP `max(Ton+ehi, Td+dhi) + fhi ≤ Toff + elo`;
  - H_HOLD `Toff + ehi ≤ Tnew + dlo`;
  - H_RST_LOW: rst low from `Rl`;
  - H_RST_DONE `Rl + rhi ≤ max(Ton+ehi, Td+dhi)`.

  This covers `setup_data` and `hold`.
- `capture_rst_from_request` covers `setup_pulse`:
  `ehi + fhi ≤ W + elo` together with the data part
  `Td + dhi + fhi ≤ Tr + Rlo + W + elo` (via `setup_from_request`).
- New theorems on the reset itself:
  - `reset_loads`: rst high on `[R0, R1)` gives `q = rv` on `[R0+rhi, R1+rlo)`.
  - `reset_holds`: the initial token holds after release, until the next
    enable rise reaches the bit. It needs:
    - H_RST_PW `R0 + rhi + fhi ≤ R1 + rlo` (the pulse fills the loop);
    - H_EN_CLOSED_AT_RELEASE `E0 + ehi ≤ R1 + rlo`.

    Nothing is assumed about rst after `R1`: the INIT's consensus makes rst a
    select between equal legs.
- Exactness: `counter_rule_I_rst`, `counter_rule_H_rst`, `counter_rules_rst0`
  and `counter_rules_rst1`. Bundling's rule-I and rule-H transport
  counter-traces are runs of both resettable INITs with rst tied low
  (`rst{0,1}_bin_odd`). In each one, H_SETUP (missing the I2 arc) or H_HOLD
  fails by the stated margin, and the bit ends wrong.

### `bd_delay[FASTFALL].flush_per_stage`: PROVED sufficient; necessity on rule F's witness

The model is `FastLineP s tap N lo hi tlo thi init c`: every hop `i` and every
tap `i` has its own window, and the tap net is a parameter (`s 0` for
`bd_delay`, `gate` for `bd_delay_gated`). The real INITs are `2'h2` and `4'h8`
(`fastfall_lineP`). `fallBound` is the latest fall at each stage output:
`fallBound 1 = Fa + hi 0`, `fallBound (i+1) = min (Ft + thi i) (fallBound i + hi i)`.

- `slow_not_early_ps`. Hypothesis, for each side stage
  `1 ≤ i < N`: **H_FLUSH_STAGE i** `fallBound i + hi i ≤ Tt + tlo i`.
  Conclusion: every stage `i` holds the fast value on
  `[fallBound i, Ta + Lo i - 1]`, so `z` cannot rise before
  `Ta + Σ lo` (the matched delay). This is the JSON form
  `fall_i + hop_hi(i→i+1) ≤ T + tap_lo(i+1)`.
- `slow_arrives_ps` (rise arrival, per-stage bounds `riseBound`/`holdBound`) and
  `fast_edge_ps`.
- `flush_stage_of_uniform`: Bundling's uniform H_FLUSH implies every per-stage
  condition (`fastLineP_of_uniform`). `flush_stage_strictly_weaker` is a
  numeric case where every per-stage condition holds and H_FLUSH fails.
- `ruleF_counter_violates_stage`: in `Bundling.ff_counter_ruleF` (rule F's
  premise holds, the rise skips the chain), H_FLUSH_STAGE 1 fails
  (`13+3 > 12+1`).
- Necessity in general (any violated stage implies a skip) is NOT proved; it
  is shown only on that witness.

### `bd_delay_gated.gate`: PROVED (timed), sufficient

`gated_line` instantiates `FastLineP` with the taps on `gate`.

- `gated_not_early`: the rise is not early under H_FLUSH_STAGE, measured
  against the gate's rise `Tg`. It also uses the header contract
  H_A_FOLLOWS_GATE (named in the doc comment), which enters as the separate
  stability windows of `a` and `gate`.
- `gated_fast_edge`: `z` falls one gate-tap hop after `gate`.
- `gated_dip_glitch` is the timed form of `gated_dip_flushes`: `gate` low on
  `[F, F']` puts `z` low on `[F + thi, F' + tlo]` even while `a` stays high.

### `bd_mux.uya_rtz_env`: PROVED, exact at the cell (as uxa)

`mux_rtz_env_safe_uya` is the mirror of `mux_rtz_env_safe`, with `uj0`'s real
INIT `0000AE08_0000AE08` (`uj0_eq`; `uj0_blocked`: a low `ctl_req` pin holds
it at 0) and uor's pins swapped (`H_J1_OR`).

Hypothesis: **H_RTZ_ENV**
`te + dlmax + dwmax ≤ Tzf + (wzc+dc+wcr+dl0+wjo+dlo+dz+ds) + wuy`, all MIN
delays.

Conclusion: `y_ack` is low on `[te+dlmax, t2+dlmin]`.

Cell-level exactness: `rtz_safe` and `rtz_counter`/`rtz_inertial_lost` are
stated for a generic `bd_c2` loop with `a` held at 0, so with `a = j1` they
apply to uya verbatim. There is no separate theorem for that; this is stated
in a comment.

### `bd_mux.bundled_s_setup`, `bd_mux.bundled_s_hold`: PROVED at the join pins, sufficient + Kleene necessity

- `j1_sel_is_c2` and `j0_sel_is_c2` check all 81 Kleene rows: while `s` reads
  definitely at the selecting value, the join's gate IS `bd_c2` on
  `(req, ctl_req)`, so all C-element results apply to it. Timed forms:
  `uj1_selected_c2` and `uj0_selected_c2`.
- `unsel_low` and `unsel_low_timed` (instances `uj0_unsel_low_timed`,
  `uj1_unsel_low_timed`): the unselected join stays low until the next
  `ctl_req` rise. Hypotheses:
  - **H_BUNDLED_S_SETUP_T** `Ts + shi ≤ Tc + clo`: `s` settled at the I2
    select before `ctl_req`'s earliest rise arrives;
  - **H_BUNDLED_S_HOLD_T** `Tcf + chi ≤ Ts' + slo`: `s` held until
    `ctl_req`'s latest fall has arrived;
  - the join was low for one loop window.
- `j0_s_x_hazard`: if `s` is mid-edge while `req` and `ctl_req` are high, the
  closure is `x`. This is necessity at the select. It is the per-pin form of
  `mux_needs_bundled_s_hazard`, not a full trace counterexample.
- What is NOT covered: the composition with the rest of the mux (`mux_ok` is
  still untimed).

### `bd_mux.bundled_z`, `bd_merge.bundled_z`: PROVED, sufficient (classic form)

- `dm_odd_kleene`, `dm_pair_o5_kleene` and `dm_pair_o6_kleene` cover the
  `bd_datamux` INITs `E4` and `FFAA_5500_E4E4_E4E4`. Each output is the Kleene
  mux of its own bit's pins, for all inputs.
- `dm_settles`: `z` is the selected value from `max(Ts+shi, Td+dhi)`.
- `usel_high` and `usel_low`: the merge's `usel = x_req | x_ack` (`4'hE`).
- `bundled_z_capture`: the consumer bit captures the selected value. Hypotheses:
  - **H_BUNDLED_Z_T** `Tz + zhi ≤ Ton + ehi` (rule A's form);
  - H_PW;
  - H_HOLD.

  It is sufficient but not exact: the exact condition is H_SETUP against the
  enable fall (`Bundling.setup_not_classic`).
- What is NOT covered: the request path lower bound (`Ton ≥` join edge + uor +
  line + C-element) is left as the reader's composition with
  `Bundling.sym_edge`/`slow_not_early_ps`. It is not a single theorem.

### `bd_mlink.qfb_first`, `bd_flink.qfb_first`: PROVED, exact-witness (mlink); sufficient (flink)

Real INITs:
- mlink: `uq` = `B8B8...`, `ux` = `F9`;
- flink: `uq` = `E2` (transparent while `ck = 0`), `uck` = `06`.

Supporting lemmas:
- `capture_gap`: Bundling.capture where the enable may be undefined between
  its last-high and first-low instants.
- `ux_open` and `uck_open`: the enable LUT keeps the latch open until `wlo`
  after `done` first shows the new value.
- `flink_uq_latch`: `E2` is `LatchRel` with enable `!ck`, via `winK_not`.

The theorems are `mlink_qfb_first_timed` and `flink_qfb_first_timed`.
Hypotheses:
- **H_QFB_FIRST_T** `max(Ton+ehi, Td+dhi) + fhi ≤ Tq + wlo + elo`, where `Tq`
  is the instant up to which `done` still shows the old value;
- H_ACK_STABLE;
- H_GAP;
- H_HOLD.

Conclusion: `done` captures and holds the new token, with no runt.

`qfb_clean_form`: when `done` makes one clean edge (`S ≤ Tq`), the hypothesis
reduces to the JSON's `fhi ≤ wlo + elo`:
- `fhi` = done→uq.I2 max, including the site pin and arc;
- `wlo` = done→ux.I0 min + ux arc min;
- `elo` = en→uq.I1 min.

Exactness: `qfb_counter` is a closed-form transport run of the whole mlink
request-bit loop (latch + ux, real INITs, `ack = 0`), with `fhi = 3` and
`wlo + elo = 2`. `done` rises at 6, falls back at 8 and oscillates with
period 3 forever: the timed form of `mlink_runt`/`mlink_cycle`. `qfb_clean` is
the same environment with `fhi = 2 = wlo + elo`, and it has one clean edge.
So equality is safe and one tick more is not.

The JSON's strict `<` can be relaxed to `≤`, in this discrete model.

There is no flink counter-trace. NOPEN > 1 (the `uz` path) is not modelled.

### `bd_mem.clk_high_width`: PROVED, sufficient

- `MemPort.clk_high_ok`: `tPWH + dsHi ≤ dsLo + dcLo + dsLoF` implies
  `tClkR + tPWH ≤ tClkF`.
- `MemPort.clk_low_ok`: `tPWL ≤ dcLoF + dsLo` implies
  `tClkF + tPWL ≤ tClkR2`.

These are arithmetic on the existing `clk_high_width` / `rtz_serialised`.

### `bd_link_dctl.lt_first`: PARTIAL (LUT level only)

- `ult_kleene`: `INIT_DLT` is the Kleene NOR.
- `lt_settles`: stable inputs give a settled `lt` after the window.
- `lt_first_window`. Hypotheses:
  - H_ROUND_TRIP: the next change of any `ult` input comes no earlier than
    `T + R`;
  - **H_LT_FIRST_T** `H + wlt_hi ≤ R - 1 + L + wlt_lo`.

  Conclusion: every consumer pin reads the settled `lt` before the next input
  change can arrive.
- `lt_opposite_x`: opposite edges of `b` and `a` inside the window give `x`.
  With one input high, the other's edge is masked.
- **Not proved:** that timed runs satisfying H_LT_FIRST_T obey the untimed
  schedule `ltFirst`, which `dctl_ok0/1` need. That needs a timed model of the
  whole dctl controller and its two neighbours. Status: unproved as an
  inequality ⇒ hazard-freedom theorem.

### `bd_mux.isochronic_forks`, `bd_merge.isochronic_forks`: NOT PROVED

The JSON reading, "branch skew < half a handshake" or "< one environment round
trip", is about the untimed mux/merge proofs (`mux_needs_iso_*`,
`merge_needs_iso_*`). A timed statement needs a timed model of the whole
mux/merge with its environment, which does not exist. Partial coverage is
already in this file:
- the `ctl_req → {uj0, uj1}` fork is covered per pin by the H_BUNDLED_S
  timed theorems above (each join's `ctl_req` pin has its own window);
- the `z_ack → {uxa, uya}` fork is covered by the two H_RTZ_ENV theorems
  (each with its own `wux`/`wuy` and `Wux`/`Wuy`).

What is missing is the "same transition seen consistently" property between
the branches. Estimate: 1–2 days, with a timed mux trace model.

## Summary table for the lead

| entry | status | main theorem(s) | exactness |
|---|---|---|---|
| bd_c2.sel_order | proved | ConstraintsSel.sel_phase_gen + isC_c2; sel_order_of_lat_gen; sel_runt_gen; ce_c2_sel_order_fails; ce_c2_not_fifo | exact (select-level runt + witness) |
| bd_c3.sel_order | proved | same + isC_c3; ce_c3_* | exact (same) |
| bd_c4.sel_order | proved | same + isC_c4; ce_c4_* | exact (same) |
| bd_latch_rst.setup_data | proved | ConstraintsLatchRst.capture_rst | sufficient; necessity witness counter_rule_I_rst |
| bd_latch_rst.setup_pulse | proved | capture_rst_from_request | sufficient (as the odd bit) |
| bd_latch_rst.hold | proved | capture_rst; counter_rule_H_rst | sufficient + witness |
| (new) bd_latch_rst.reset | proved | reset_loads, reset_holds | sufficient |
| bd_delay[FASTFALL].flush_per_stage | proved | ConstraintsFastFall.slow_not_early_ps; flush_stage_of_uniform; ruleF_counter_violates_stage | sufficient; necessity on witness only |
| bd_delay_gated.gate | proved | gated_not_early, gated_fast_edge, gated_dip_glitch | sufficient |
| bd_mux.uya_rtz_env | proved | ConstraintsMux.mux_rtz_env_safe_uya | as uxa (cell-level exact) |
| bd_mux.bundled_s_setup | proved (join pins) | uj0/uj1_unsel_low_timed, uj*_selected_c2, j0_s_x_hazard | sufficient + Kleene necessity |
| bd_mux.bundled_s_hold | proved (join pins) | same | same |
| bd_mux.bundled_z | proved (classic) | dm_settles, bundled_z_capture | sufficient, not necessary |
| bd_merge.bundled_z | proved (classic) | usel_high/low, dm_settles, bundled_z_capture | sufficient, not necessary |
| bd_mlink.qfb_first | proved | ConstraintsMore.mlink_qfb_first_timed, qfb_clean_form, qfb_counter, qfb_clean | exact on witness (tight by 1 tick) |
| bd_flink.qfb_first | proved | flink_qfb_first_timed, qfb_clean_form | sufficient |
| bd_mem.clk_high_width | proved | MemPort.clk_high_ok (+ clk_low_ok) | sufficient |
| bd_link_dctl.lt_first | partial | lt_settles, lt_first_window, lt_opposite_x | LUT level only; link to ltFirst unproved |
| bd_mux.isochronic_forks | unproved | — | — |
| bd_merge.isochronic_forks | unproved | — | — |

So 16 of the 19 entries are proved, 1 is partial and 2 are unproved.

## Fidelity per primitive

- **C-element LUTs (bd_c2/c3/c4).** Modelled as a per-pin LUT: each pin goes
  through its own FIFO site-pin map (H_PIN_FIFO), then the zero-time Boolean
  function of the REAL INIT at the selects, then one FIFO output map
  (H_TREE_FIFO, which contains the static-hazard assumption). Feedback is the
  node's own output read through the feedback pin's map. In the counter-trace
  the feedback wire is a fixed delay; in `ceG` it is folded into `qpC`.
- **Latches (`bd_latch_rst`, mlink `uq`, flink `uq`), the joins, the datamux,
  `ult`, `usel`, and the delay-line stages.** Modelled with Bundling's window
  `Gate`: each pin is read over `[lo, hi]` (route + pin arc), and the output is
  constrained only where the Kleene closure of the REAL INIT is definite
  (H_KLEENE_LUT). Feedback is a routed wire with its own window
  (H_LOOP_POS `1 ≤ flo`). Inertial filtering is not modelled. Transport
  counter-traces satisfy `Gate` via `transport_gate`.
- **The uya race.** Uses CElemTiming's `Loop`/`FLoop` (LUT window + feedback
  window channels, REAL INITs).
- **BRAM.** Datasheet parameters only (`MemPort`); it is not a gate.

## Verdict

**Works.** 16/19 entries now have timed Lean theorems with real INITs. Of
those, sel_order ×3, latch_rst and the mlink qfb_first have counter-traces that
make them exact on witnesses. The priority entries (sel_order for bd_c2,
latch_rst, FASTFALL per stage, uya_rtz_env) are all done.

To finish:
- (a) a timed dctl model to link H_LT_FIRST_T to `ltFirst`: about 1 day;
- (b) a timed mux/merge trace model for the isochrony entries: 1–2 days;
- (c) general necessity of H_FLUSH_STAGE, from any violated stage to a
  constructed skip: about half a day.

What it buys: every JSON constraint that bdc's emitted designs rely on
(C-element feedback order, the loop's initial token, the FASTFALL request
lines, the mux return-to-zero race, the MOUSETRAP request bit) is backed by a
theorem whose inequality is the JSON form.

For the extract/tcheck front end, the per-stage FASTFALL form and the per-pin
sel_order are the two that differ from what the rules check today:
- rule F has no in-flight term;
- the SDF charges a flat site-pin delay.
