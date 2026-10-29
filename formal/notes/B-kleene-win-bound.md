# B-kleene-win-bound: `+W` under H_W_BOUND, sufficient and needed (probe Bwb)

File: `formal/lean/Formal/Cells/KleeneWinBound.lean`. Core Lean; imports only KleeneWin.
Check: `/tmp/claude-0/btools/bcheck.py Formal/Cells/KleeneWinBound.lean` gives `OK`, no
warnings. No sorry, admit, axiom or native_decide. Axioms of every headline: propext,
Classical.choice, Quot.sound, or a subset (`races_*`, `cel_win_bound`, `cel_win_ct`,
`cel_win_clean_at`, `c2_win_*` use propext and Quot.sound only).

## Question

KleeneWin gives exact per-edge iffs: every race pair gains `c(first) + a(after)`. The JSON
(`cell_constraints.json`, `strict.x_window`) says "+W under H_W_BOUND (c_e + a_l ≤ W for
every race pair)" is sufficient without knowing the split. Lean had this only for bd_steer
(`SelfAuditB7.steer_win_bound`), and had no necessity side for any cell. The JSON marks the
other 69 rows' claims UNPROVED.

## Answer

**One generic lemma.** Every KleeneWin iff has the same shape: the cell is safe iff
`X_i + s_i ≤ Y_i` holds for each race `i`, with `s_i` the exact window term (`Races l`).
* `races_suff`: if every `s_i ≤ W`, then binary-edge margins of `+W` are sufficient.
* `races_need`: if one `s_i = W`, a binary-edge margin below `W` on that race is unsafe.
  The counter-trace is the necessity half of the iff: some read map and trace in the box
  violates the spec.

Each cell gets a `*_races` lemma (its KleeneWin iff written as a race list). The bound
theorems below follow from it.

| cell | `+W` sufficient | `+W` needed (margin `W - 1` unsafe when the term `= W`) | witness (safe at `W`, unsafe at `W - 1`) |
|---|---|---|---|
| bd_steer | `steer_win_bound'` (= SelfAuditB7's) | `steer_win_need_setup`, `steer_win_need_hold` | `steer_bound_pair_witness` (W = 2) |
| bd_mux join | `join_win_bound` | `join_win_need_setup`, `join_win_need_hold` | `join_bound_pair_witness` (W = 2) |
| bdc_muxn selected join | `muxn_win_bound` (4 pairs) | `muxn_win_need` (any of the 4 pairs) | `muxn_bound_witness` (k = 1, W = 2) |
| bd_latch | `latch_win_bound` (pulse, data, hold) | `latch_win_need_pulse`, `_data`, `_hold` | `latch_bound_pair_witness` (W = 3) |

Every witness uses a non-uniform split, and the race term is exactly `W` on the race that is
then made one tick short.

**Which bound, exactly.** It depends on what H_W_BOUND says. There are three readings.
1. **Pair** (the JSON's): `c_e + a_l ≤ W` for each race pair. Then `+W` is sufficient and
   tight (table above).
2. **Width** (H_W_EDGE: each window `[T - a_T, T + c_T)` contains its binary edge,
   `0 ≤ a_T, c_T`, and has width `a_T + c_T ≤ W`). Then a pair term can reach `2W`: the
   first edge's window lies entirely after its edge and the second's entirely before.
   So `+2W` is sufficient (`join_edge_bound`, `latch_edge_bound`) and needed
   (`join_edge_need`, `latch_edge_need`, split `c_e = a_l = W`).
3. **Width only, halves free in sign** (KleeneWin allows a window that does not contain its
   binary edge). Then no finite margin is sufficient. `join_width_unbounded`: for every `M`,
   a split with every window of width 0 makes binary margins of `M` unsafe.
So "every edge's window has width ≤ W" is NOT enough to give `+W`. The JSON must state the
pair form (1), or the width form with non-negative halves (2, giving `+2W`).

**C-element own-feedback race (any `Facts` cycle, H_FB_WIN).** The exact term is
`cf + wq + ar`: the follow pin's trailing half, the feedback pin's own window, and the
release pin's leading half (`cel_env_win_iff`). `wq` is not part of any race pair. So:
* Pair reading plus a feedback-window bound `wq ≤ Wq`: the bound is **`+W + Wq`**.
  `cel_env_win_bound` (sufficient, in B's terms `dlmax + dwmax + W + Wq ≤ dlmin + E`);
  `cel_env_win_need` (tight: for any split with `cf + ar = W`, a margin below `W + Wq` is
  unsafe).
* `+2W` is the special case where H_W_BOUND also bounds the feedback window (`Wq = W`):
  `cel_env_win_bound_2W`.
* Width reading: `+2W + Wq`, which is `+3W` at `Wq = W` (`cel_env_edge_bound`, and
  `cel_env_edge_need` for tightness).
* Per run: `cel_win_bound` (`Tf + D + W + wq ≤ Tr` gives a clean edge).
* Explicit counter-run, for every split, every loop delay `D = d + 1` and every `wq`, on any
  `Facts` cycle: `cel_win_ct`. The simulated loop (`simGW`) with binary-edge margin
  `cf + ar + wq - 1` is wrong at the release window's start. `cel_win_clean_at` is clean one
  tick later.
* On the real bd_c2 INIT (`c2_win_ct` / `c2_win_clean`): follow `(af, cf) = (0, 1)`, release
  `(ar, cr) = (1, 0)` (so `W = 2`), `wq = 1`, `D = 420`. The edge is clean at margin 3 and a
  hazard at margin 2.

**Consequence for the JSON.** The ~51 rows whose `+1` is the C-element race say "+W". That
is sufficient only under H_FB_PURE (`wq = 0`; `cel_env_win_bound` with `Wq = 0`). With a
feedback window they need **`+W + Wq`** (`+2W` if `Wq ≤ W` is assumed).

## Row families for the next JSON pass (do not edit here)

Families are taken from each row's `strict.backing` and its current `x_window` tail.

* **bd_steer.bundled_s_setup, .bundled_s_hold**: sufficient `SelfAuditB7.steer_win_bound`
  (or `steer_win_bound'`); needed `steer_win_need_setup` / `_hold`; witness
  `steer_bound_pair_witness`.
* **bd_mux.bundled_s_setup, .bundled_s_hold**: `join_win_bound`; `join_win_need_setup` /
  `_hold`; `join_bound_pair_witness`. Width reading: `join_edge_bound` / `join_edge_need`
  (`+2W`).
* **bdc_muxn.s_setup, .s_hold**: `muxn_win_bound`; `muxn_win_need`; `muxn_bound_witness`.
* **bd_latch[odd | pair.O5 | pair.O6].setup_pulse / .setup_data / .hold** (9 rows):
  `latch_win_bound`; `latch_win_need_pulse` / `_data` / `_hold`; `latch_bound_pair_witness`.
  Width reading: `latch_edge_bound` / `latch_edge_need` (`+2W`). These rows' loop with its
  own feedback window is `latch_fbwin_iff` (`+wq`), as before.
* **Own-feedback race (Facts backing: c2_all, c2n_c8g, c3_all, c4_all, latch_facts)**, 51
  rows: `bd_c2|c2n|c3|c4.{pulse_width, env_latency, sel_order}`, `bd_ctree.node_fork`,
  `bd_latch_rst.{setup_data, setup_pulse, reset}`, `bd_pipe.{sel_order, lat_lumped,
  rst_lines}`, `bd_arbiter.{rt2_pulse, rt2_g1, rt2b_pulse2, rt2b_g2}`,
  `bd_mux.{uxa_rtz, uxa_rtz_env, uya_rtz, uya_rtz_env, isochronic_forks, uj_env_latency_req,
  uj_env_latency_ctl, uxa_join_latency, reset_first, uj0_env_latency_req_max,
  uj1_env_latency_req_max}`, `bd_merge.{isochronic_forks, uxa_feedback, uxa_req_latency,
  reset_first}`, `bdc_amerge3.rt2_cascade_{pulse, g1, pulse2, g2}`,
  `bdc_muxn.{rtz, iso_ctl, iso_zack, uj_env_latency_req, uj_env_latency_req_max}`,
  `bd_mlink.qfb_first`, `bd_flink.qfb_first`, `bd_fork.{branch_data, branch_data_edge}`.
  * Backing: `cel_env_win_bound` (`+W + Wq`; `+W` only at `Wq = 0`), `cel_env_win_need`,
    `cel_env_win_bound_2W`, per run `cel_win_bound`; counter-runs `cel_win_ct` / `c2_win_ct`.
  * Caveat (not proved here): that each row's inequality IS an instance of the `Facts` race
    (which edge is the follow, which is the release, what `E` is). That mapping is the row's
    existing backing. Composite rows (arbiter rt2, amerge3 cascade, isochronic forks,
    reset_first) carry it only as far as their existing mapping does.
  * `bd_fork.branch_data` says it "is bd_latch.setup_data"; by that description,
    `latch_win_bound` applies to it as well.
* **Reset rows backed by `*_rst_dec`** (`bd_c2|c2n|c3|c4.reset_width`, `design.rst_hold`):
  NOT backed. `*_rst_dec` are Boolean reset-release decisions, not `Facts` cycles, and no
  per-edge reset iff exists. Their "+W" stays UNPROVED.

## NOT covered

* The values of `W` and `Wq` (unmeasured; board test XW-1 in B-kleene-win.md).
* Whether H_W_BOUND (in any reading) holds on the fabric.
* The `*_rst_dec` reset rows.
* That each C-element-backed row instantiates the `Facts` race (see the caveat above).
* bdc_muxn's unselected joins.
* Correlated corners.
* Windows chosen per token by the box adversary (as in KleeneWin).
* The necessity sides for steer, join, muxn and latch are existential: some behaviour in the
  box fails, through the iff. Only the C-element has an explicit parametric counter-run
  (`cel_win_ct`).
