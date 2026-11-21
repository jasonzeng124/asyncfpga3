# B-necessity: necessity for gcd_hw's sufficient-only rows (reset family, mux RTZ env)

Probe Bsx (shard B), 2026-10-27. New files (core Lean only):
`formal/lean/Formal/Cells/NecessityReset.lean`,
`formal/lean/Formal/Cells/NecessityMuxRtz.lean`. JSON drafts (not merged,
JSON untouched): `/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bsx/draft_exactness.json`.
No route, board or toolchain run. Rows other probes own (bd_steer, bd_mux
select, bd_delay_gated, bd_latch setup/hold, bdc_muxn, arbcell) were not
touched.

## 1. Reset width (NecessityReset)

**Model.** This is B's per-pin model, as in LibGapSteer and LibGapMux.
- H_PIN_READ (`LoopEq`): for t >= 0 the output is the real INIT applied to two
  reads and a constant vector:
  - rst, read at `pr.σ t`, with `pr` in [Rlo, Rhi] (wire + site pin + I_rst arc);
  - the cell's own output, read at `pq.σ t`, with `pq` in [Qlo, Qhi] and
    Qlo >= 1 (feedback arc + feedback wire + site pin);
  - the other pins, held at a constant non-enabling vector (H_IN_HELD).
- Read maps need not be monotone.
- H_RST_PULSE: rst is high at its driver exactly on [0, W).
- The power-up value is arbitrary.

**Spec:** the output holds the reset value from Rhi on, for ever.

**Proved:**
- `reset_box_exact`: ResetOK holds for every pair of read maps in the box,
  every trace and every power-up **iff** `Rhi + Qhi <= W + Rlo`. The sufficient
  half is `reset_ok`. The necessary half is `reset_fails`: with `prAdv`, rst's
  rise is seen through Rhi and its fall through Rlo. Every trace that starts
  from the non-reset value shows that value again at some t >= Rhi.
  `runB_loopEq` shows such a trace exists.
- `reset_pin_exact` (fixed delays, one corner): exact iff `loop <= W`. The rst
  path delay drops out.
- Real INITs (`cells`, decided):
  - bd_c2, bd_c2n, bd_c2n_set, bd_c3 and bd_c4;
  - bd_mux.uj0 and uj1;
  - bd_latch_rst with RESET_VALUE 0 and with RESET_VALUE 1.
  
  Each has its own `*_box_exact`. Every held vector satisfies the cited
  sufficient theorems' release hypotheses (for example `c2_reset`'s H_RELEASE).
- Counter-trace `c2_short_reset`. Take a loop of 400 ps, an rst path of 500 ps
  and rst held for 399 ps. The cell is 0 at 600 and 1 again at 899 (the
  reset is lost). With 400 ps, `c2_ok_reset` gives 0 for ever. Both traces
  exist (`c2_traces_exist`).
- Reset state: bd_c2n holds with every input at its reset value
  (`c2n_resetstate_holds`). bd_c2, bd_c3, bd_c4, uj0 and uj1 instead compute
  0 once every input reads 0, with no reset pulse at all (`inputs0_force`,
  `c2_inputs0_selfreset`). So at design level the width is needed for the 185
  bd_c2n plus 1 bd_c2n_set in their actual reset state. For the other cells it
  is needed only while some input is still away from its reset value.
- Kleene, pointwise (`kleene_release_harmless`, `kleene_rise_x`):
  - an X on rst at its FALL is harmless once the feedback reads the reset value;
  - at its RISE, while the feedback still reads the old value, the output is X.
  
  So the rows' strict +1 belongs to the rst rise window.
- H_RST_EARLY ("released before the first request") is **not necessary**:
  - `early_request_ok`: in a per-pin bd_c2 with all four pins read, a request
    that reaches its pin while rst is still read high, and stays, gets exactly
    the clean response.
  - `early_request_numbers`: a concrete case. The request is at the pin at 400,
    release is read at 1500, and the response is 0 at 2299 and 1 at 2300.
  - `returned_pulse_lost`: what is needed is H_NO_RETURN. An input pulse that
    rises and falls while rst is read high is lost: the cell stays 0.

**FINDING (design.rst_hold, box mode).** The form is
`w.hi + SP + dlmax + dwmax + SPfb + 1 <= W + w.lo + SP`. It charges the I_rst
arc only on the data side. In the per-pin box the exact condition is
`Rhi + Qhi <= W + Rlo`, and Rlo includes the arc's lo. The form is therefore
short by `arc.hi - arc.lo - 1`. The rows (bd_c*.reset_width) have the same
shape at the pin.
- `json_box_gap` / `json_box_gap_fails` give prjxray-shaped numbers: rst wire
  [200, 300], SP A4 [86, 284], O6 [45, 124], feedback wire [100, 150],
  SP A3 [107, 344].
- With these, W = 917 passes the form, but some admissible read maps and trace
  of the real bd_c2 break the reset. The exact box needs W >= 995.
- In 1C (one corner, flat O6) the form is exact plus its +1. The rows are
  marked "1C", but they also say "box is always sound", which is false here.
- Fix: put the I_rst arc (lo) on the request side, as `bd_latch_rst.reset`'s
  form 0 already does. That form is box-exact.

## 2. bd_mux RTZ env (NecessityMuxRtz)

- `RtzEnvClaim slack` is `MuxRtzTimed.mux_rtz_env_safe` with every
  hypothesis verbatim, except that H_RTZ_ENV is weakened by `slack`.
- `claim0` is the existing sufficient theorem.
- `claim1_false` / `claim1_false_1C` (uxa) and `claimY1_false(_1C)` (uya, real
  uj0) are explicit counter-runs, each violating H_RTZ_ENV by exactly 1 tick
  and satisfying every other hypothesis:
  - every chain stage is 1 tick: sender, ctl_req, the join (real INIT, request
    waiting), uor, the request line and the server;
  - uxa is the real bd_c2 with loop 6 (box run: the z_ack wire's fall is seen
    through 4, its rise through 1) or loop 9 (1C: every wire is one fixed delay);
  - in both runs x_ack is 1 again at 32, inside the window where the
    conclusion says it is 0 (`rtz_counter`).
- So H_RTZ_ENV cannot be weakened uniformly, in either corner mode. This is
  one parameter point per form: mux_ok's remaining hypotheses are not
  re-checked on the run.

## 3. Table

| row id | old | new (draft) | Lean |
|---|---|---|---|
| bd_c2.reset_width | sufficient | sufficient+necessary (width clause; release clause not necessary) | reset_box_exact, c2_box_exact, reset_pin_exact, c2_short_reset, early_request_ok, returned_pulse_lost |
| bd_c2n.reset_width | sufficient | sufficient+necessary (same) | c2n_box_exact, c2n_resetstate_holds |
| bd_c3.reset_width | sufficient | sufficient+necessary (same) | c3_box_exact |
| bd_c4.reset_width | sufficient | sufficient+necessary (same) | c4_box_exact |
| design.rst_hold | sufficient | sufficient+necessary_at_instance; box-form gap | cells, *_box_exact, c2_inputs0_selfreset, json_box_gap_fails |
| bd_latch_rst.reset | sufficient | sufficient+necessary (form 0 only) | latch_rst0_box_exact, latch_rst1_box_exact |
| bd_merge.reset_first | sufficient | sufficient (loop terms necessary; H_RST_EARLY not) | c2_box_exact, early_request_ok |
| bd_mux.reset_first | sufficient | sufficient (same) | uj0/uj1/c2_box_exact, early_request_ok |
| bd_pipe.rst_lines | sufficient | sufficient (loop term necessary in reset state) | c2n_box_exact |
| design.rst_release_skew | sufficient | not_necessary (exact replacement H_NO_RETURN, cell level) | early_request_ok, returned_pulse_lost |
| bd_mux.uxa_rtz_env | sufficient | sufficient+necessary_at_boundary | claim0, claim1_false, claim1_false_1C |
| bd_mux.uya_rtz_env | sufficient | sufficient+necessary_at_boundary | claimY0, claimY1_false, claimY1_false_1C |

## 4. Not done, with the analysis for the next probe

**bd_merge.uxa_feedback / uxa_req_latency** are probably NOT necessary.
- When z_ack is uxa's later input, the next z_ack edge is causally after
  ZA0 j itself:
  `ZA0(j+1) >= ZA0 j + Lxa.lo + Wxa.lo + Eo + Kz + Wzx.lo`.
- So the Wzx spread cancels, while S_XA_ZA charges it.
- For y-owned phases uxa does not move, so H_DEP_XA is spurious there. The
  exact condition is the CElemStrict race only where uxa moves.
- Proving this needs a sharper static theorem in the merge model. It is not
  done.

**bd_ctree.node_fork**: the same causality argument applies. In a FIFO run the
root fires after the node, so `Spread n` cancels and a min leaf-wire term is
missing on the right. With non-monotone windows the spread may come back. Not
proved either way.

## Check

- `/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/NecessityReset.lean formal/lean/Formal/Cells/NecessityMuxRtz.lean`
  prints `[bchk] OK`.
- `#print axioms` on 16 main theorems (`Bsx/ax.lean`) shows at most
  `propext`, `Classical.choice` and `Quot.sound`.
- There is no sorry, admit, native_decide or axiom.
