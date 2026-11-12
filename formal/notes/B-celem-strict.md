# B-celem-strict: the own-feedback race in a per-pin Kleene mux-tree LUT (X2)

File: `formal/lean/Formal/Cells/CElemStrict.lean` (core Lean, imports CElemFn
and Latch). Check:
`scratchpad/bchk.sh formal/lean/Formal/Cells/CElemStrict.lean` gives `[bchk] OK`
with no warnings. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Verdict

**Works.** In B's per-mux Kleene model, run in time with one trace per pin,
the own-feedback race on the real bd_c2 INIT is clean **iff** the departing
(release) pin's select starts moving no earlier than the tick at which the
feedback pin's select has settled. The condition is exact (`clean_iff`).

In B's binary-edge terms, a trace value counts as new from the tick it has
settled. The condition then reads `dlmax + dwmax + wa ≤ dlmin + E`, where
`wa` is the X window of the departing select (`env_latency_iff`).

- Under H_MUX_KLEENE a moving select is X for at least one tick, so on the
  ps grid `wa ≥ 1`. B's `≤` must become `<`, a margin of one tick
  (`env_latency_strict`).
- At equality there are concrete traces on the real INIT: bd_c2 reads 1 at
  tick 419 and X at tick 420 (`boundary_x`), and bd_c2n gives X on C-8g's
  transition (`boundary_x_c2n`).
- If the release lands before the feedback has moved, the result is a full
  binary glitch back to 0 (`binary_glitch`).

**Equality is safe exactly when `wa = 0`** (`env_latency_atomic`,
`atomic_equality_clean`), that is, when select edges are instantaneous. Three
existing models make that assumption:
- B's atomic LUT (A's H_ATOMIC_LUT);
- B's binary per-pin FIFO (FifoFidelity, ConstraintsSel);
- the Kleene window model of Bundling when `lo = hi`.

C's results differ only in this assumption:
- C-12c's closed transport bound is the zero-width case. Its strict inertial
  bound, and C-8g's function hazard (a sub-tick order inside the tree), are
  the `wa > 0` case.

The tree order does not matter. `lutK` is the mux tree, and
`MuxTree.Tree.evalK_order_indep` shows that every pin order gives the same
value. So the result holds for every mux-tree layout of the pins.

**Physical margin.** One tick is the smallest margin the grid allows. It is
not a measured bound. The faithful margin is the X width (the slew at the
select) of the departing pin.
- With SDF 50% arrival times, the X windows straddle the arrival instants.
  The margin is then half the sum of the two select slews.
- This model does not measure that width. A rule that adds `+1 ps` is the
  model's minimum. A rule that adds the slew is the physical requirement.

## Model and hypotheses

- **H_TREE.** `G t = F (i t) (qp t)`, where `F` is `lutK` of the real INIT.
  - bd_c2: `c2K`. I0 = a, I1 = b, I2 = q (the feedback), I3 = rst held at 0,
    I4 = I5 = 0.
  - Each pin is its own trace at its own select, so each pin has its own
    arrival time.
  - `G` is the root value. `O` is `G` delayed by `dl`.
- **H_MUX_KLEENE.** A pin edge reads `old` before `s`, `x` on `[s, s+w)`, and
  `new` from `s+w`.
- **H_FB_PURE.** `qp t = G (t - D)` for `t ≥ D`, and the settled `v` before
  that. `D ≥ 1`, and `D = dl + dw`.
- **H_IN_PHASES.** The input phases are `I0`, then `IX` on `[tb, tb+wb)`, then
  `I1` on `[tb+wb, s)` (the cell must follow to `n`), then `RX` on
  `[s, s+wa)`, then `R1` (the cell must hold `n`).
- **H_ACK_ORDER.** `tb + wb ≤ s`.
- **Spec.** `G` is one clean edge: `v`, then `x` only during the follow
  pin's own window, then `n` forever.

## Theorems

| name | assumed | proved |
|---|---|---|
| `prefix_ok` | Loop, Facts, D ≥ 1 | the spec holds before the release, whatever the race |
| `clean` | + `tb + D + wb ≤ s` | spec for all t (follow, then hold, no X, no glitch) |
| `hazard` | + H_ACK_ORDER, `s < tb + D + wb` | `G s ≠ n` while the spec says `n` |
| `clean_iff` | Loop, Facts, D ≥ 1, H_ACK_ORDER | spec ↔ `tb + D + wb ≤ s` |
| `loop_exists`, `sim_loop` | D ≥ 1 | non-vacuity: every parameter choice has a behaviour (simulator `simG`) |
| `box_iff` | D ∈ [Dlo, Dhi], s ≥ slo | safe for all ↔ `tb + Dhi + wb ≤ slo` |
| `env_latency_iff` | B's form, `wa ≤ dlmin + E` | safe ↔ `dlmax + dwmax + wa ≤ dlmin + E` |
| `env_latency_strict` / `_atomic` | wa = 1 / wa = 0 | ↔ `<` / ↔ `≤` |
| `c2_all` | — | the Facts hold on the real bd_c2 INIT for all 8 cycles (rise or fall × follow pin a or b × release pin a or b) |
| `c2n_c8g` | — | the Facts hold on bd_c2n for C-8g's transition (1,0,0)→(1,1,1) |
| `latch_facts` | — | the Facts hold on the bd_latch odd bit (data edge while en = 1, then the en fall) |
| `boundary_x`, `boundary_x_c2n`, `binary_glitch` | concrete, D = 420 | the counter-traces |
| `strict_clean`, `atomic_equality_clean` | concrete | the strict side, and the wa = 0 equality, are clean |

**Not covered:**
- A feedback-select X window of a width other than `G`'s (a slew stretched
  by the wire). The condition then reads "release X start ≥ feedback settle
  tick" with that settle tick.
- Inertial filtering.
- rst as the release pin, and bd_c3/bd_c4. Those Facts were not decided; the
  generic theorem applies once they are.

## Change list (do not edit; for the owner)

The Lean theorems are **not wrong**. Each one is proved in a model with
instantaneous selects, and strict implies `≤`, so each still applies under
the strict form.

What must change:
- the checked constraints (`formal/out/cell_constraints.json` and the rules
  that evaluate them) must gain `+ wa`, with `wa ≥ 1` tick;
- each theorem's fidelity line should name the assumption (H_ATOMIC_LUT or
  zero-width selects).

### JSON entries: own-feedback race, so `L ≤ R` becomes `L + 1 ≤ R` (that is, `L < R`)

**Backed by `c2_all`:**
- `bd_c2.env_latency`, `bd_c2.sel_order`, `bd_c2.pulse_width`. The last one
  becomes held `≥ Dmax + 1`.

**Backed by `c2n_c8g`:**
- `bd_c2n.env_latency`, `bd_c2n.sel_order`, `bd_c2n.pulse_width`.

**Same mechanism, Facts not decided here:**
- the reset width: `bd_c2.reset_width` and the c2n/c3/c4 `reset_width`
  entries become held `≥ Dmax + 1`;
- the c3 and c4 entries for `env_latency`, `sel_order` and `pulse_width`;
- `design.rst_hold`.

**Backed by `latch_facts`** (pair O5 and O6 are the same mux by
`Latch.pair_o5_kleene` and `pair_o6_kleene`):
- `setup_data` and `setup_pulse` for `bd_latch[odd]`, `[pair.O5]`,
  `[pair.O6]` and `bd_latch_rst`;
- the first part of `bd_latch_rst.reset`: `R0 + rhi + fhi + 1 ≤ R1 + rlo`.

**Instances of the bd_c2 or bd_c2n race:**
- `bd_ctree.node_fork`;
- `bd_pipe.sel_order` (both halves), `bd_pipe.lat_lumped`, and the loop
  terms of `bd_pipe.rst_lines` (`L_i.hi + wh_i`, `out.hi + wh + pq.hi`);
- `bd_mux`: `uxa_rtz`, `uya_rtz`, `uxa_rtz_env`, `uya_rtz_env`,
  `isochronic_forks` (both), `uj_env_latency_req`, `uj_env_latency_ctl`,
  `uxa_join_latency` (both), and the loop terms of `reset_first`;
- `bd_merge`: `isochronic_forks` (the first two parts; the third is
  bundling), `uxa_feedback` (both), `uxa_req_latency` (both), and the loop
  terms of `reset_first`;
- `bdc_muxn`: `rtz`, `iso_ctl`, `iso_zack` (all three), `uj_env_latency_req`;
- `bd_arbiter`: `rt2_pulse`, `rt2_g1`, `rt2b_pulse2`, `rt2b_g2`; and
  `bdc_amerge3`: `rt2_cascade_pulse`, `_g1`, `_pulse2`, `_g2` (the ua_k
  C-element's loop against the A0 re-rise). `bd_arbiter.ack_celements`
  inherits;
- `bd_mlink.qfb_first`, `bd_flink.qfb_first`: `fhi + 1 ≤ wlo + elo`.

**Already strict:**
- `bd_link_dctl.lt_first` (`R - 1`);
- `bd_arbcell.req_separation` (`>`);
- `bd_link_dc.rule_K_corrected` and `rule_L_corrected` carry a `guard`; they
  are strict if `guard ≥ 1`.

**Input-against-input orders (outside this theorem).** At equality the same
X-window mechanism applies whenever the function is not constant across the
two moving selects:
- `bd_latch*.hold`, where `Latch.ct2_hold_violation_x` already shows the X;
- `bd_steer.bundled_s_hold` and `bd_mux.bundled_s_hold`;
- the `bd_delay` flush rules;
- `bd_arbiter.a0_fork_*`;
- the fork fields `rt2_forkA` and `rt2_forkG`.

These need their own check before they are made strict.

### Lean hypotheses that use the non-strict form

Keep these as they are. Add the strict corollary, or name the fidelity
assumption, in the doc of each:
- `CElemTiming.c2_four_phase` (:408) and `CElemCore.c2_four_phase` (:193);
- `CTreeTimed` at :256, :459 (`c3_four_phase`) and :492 (`c4_four_phase`),
  and `H_ENV_STATIC` at :1226;
- `OnNetlistTimed.c2n_four_phase` (:146). Its numeric instances at
  :424, :440, :456 and :472 change from `524 ≤ E`, `793 ≤ E`, `915 ≤ E` and
  `545 ≤ E` to `525 ≤ E`, `794 ≤ E`, `916 ≤ E` and `546 ≤ E`;
- `LinkTimed` `Ctl.H_ENV_LATENCY` (:171, :337);
- `MuxRtzTimed` (:381);
- `PipeTimedN` `H_LAT` (:430) and `H_RST_LINES`;
- `ConstraintsSel` `H_SEL_ORDER` (:237) and `sel_order_of_lat_gen` (:272);
- `FifoFidelity` `sel_phase` (:178) and `sel_order_of_lat` (:214);
- `ConstraintsMore` `H_QFB_FIRST_T` (:214);
- `Bundling.capture` `H_SETUP`.

`OpsTimedMux` `S_J_REQ` and `ContractsTruncCel` inherit `bd_c2.env_latency`.
