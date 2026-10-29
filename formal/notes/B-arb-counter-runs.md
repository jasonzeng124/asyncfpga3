# B-arb-counter-runs: constructed violating runs for rt1, handover_overlap and the re-request races (probe Bcr)

Files (core Lean, no Mathlib):
* `formal/lean/Formal/Cells/ArbCounterRuns.lean` (347 lines; imports `OnGcdArb`, `ArbCorners`):
  rt1 and handover_overlap.
* `formal/lean/Formal/Cells/ArbCounterRunsAM.lean` (748 lines; imports `ArbCounterRuns`,
  `ArbAMerge`): races Q, R, G (fall view), Q2, R2, G2.

Check: `/tmp/claude-0/btools/bcheck.py Formal/Cells/ArbCounterRuns.lean` and
`... Formal/Cells/ArbCounterRunsAM.lean`. Both **OK**, no warnings. Neither file has
sorry, admit, axiom or native_decide. `#print axioms` was run on the 12 headline theorems
from a temporary tail, since removed. Every one gives `[propext, Classical.choice, Quot.sound]`.
The lead must add both modules to `Formal.lean`.

Why: the Bj10 rule (`conventions.exactness`) gives a necessity label only for an iff or a
CONSTRUCTED violating run. These rows had counter-lemmas over supplied runs only. Each
theorem below builds the run, applies the existing counter-lemma to it, and is closed.

How the runs were made: an untrusted discrete simulator of 7h's `Run` (scratch,
`/tmp/claude-0/probes/Bcr/sim.py`, `conds.py`, `tgt.py`, `q2.py`, `gen_*.py`) produced the
traces and searched for the smallest delay records. Lean then CHECKS every gate relation
and the server relation for all `t ∈ ℤ` by `simp` + `omega`, the house pattern of
`SU_run` / `Wg_run`. The kernel checks the result. No `decide` runs over time.

## Per row: theorem names for the JSON pass

| row | new theorem(s) | what the run shows | proposed label |
|---|---|---|---|
| `bd_arbiter.rt1` | `ArbCounterRuns.rt1_counter_run`; other side `rt1_boundary_run` | The 7h record `D1V` lies in `OnGcdArb.BoxReal1` of the routed `gd_merge9_uarb1` (FMIN..SMAX box, worst point, `m1 = -395`), and every delay is nonzero (`AllPos`). Values: ustate O6 arc 124, A0 route 100, server `smin = 170`. RT1's race disjunct then misses by exactly 1 ps, and its structural disjunct fails too (`g1fq = 120 > g2r = 45`). `W1V` is a `Run` for all `t`, meets `Scn` for every horizon past 1781, and has a server answering in `smin`. `rt1_counter_minserver` gives both grants high at 1634 (a 1 ps overlap). At `smin = 171`, RT1 holds and `rt1_exclusion` holds on that record's constructed run `W1S`. | sufficient+necessary_at_boundary (race disjunct; structural disjunct not tight) |
| `bd_arbcell.handover_overlap` | `ArbCounterRuns.ho_cell`, `ho_overlap_iff`, `ho_counter_run`, `ho_boundary_run` | `ho_cell`: for EVERY 7e `Arcs` record and every `t0`, `hoTrace` is a `Cell` trace of the r2 → r1 scenario. `ho_overlap_iff`: on that constructed run, an overlap exists iff `qr + w + g1r_q < g2f`. `ho_counter_run`: SLOW_MAX, `w = wfb = 20`, O6 asymmetry `d6 = o5q + w + 1 = 171`. Both grants are high at `t0 + 294`, and `countTrue` = 1 ps (via `overlap_C`). `ho_boundary_run`: at `d6 = 170` there is no overlap. | sufficient+necessary_at_boundary. The row's "= 0 at every consistent corner" stays on `corner_no_overlap`, so the violating run needs H_RF_ASYM. |
| `bd_arbiter.rereq_Q` | `ArbCounterRunsAM.rereqQ_counter_run` | `cex_Q`: g2 falls while r2 is high (H_ARB2). | sufficient+necessary_at_boundary (for H_ARB2) |
| `bd_arbiter.rereq_R` | `ArbCounterRunsAM.rereqR_counter_run` | `cex_R`: z rises while neither grant is high (`zr`). The z-rise row is tight. | sufficient+necessary_at_boundary (for `zr`, z-rise row tight) |
| `bd_arbiter.rereq_G`, fall view | `ArbCounterRunsAM.rereqGf_counter_run` | `cex_G` with `Or.inr`: the fall view misses by 1 ps and the rise view holds (slack 0). g1 falls while r1 is high (H_ARB1). The rise view already has `cexG_run`. | both views now constructed |
| `bd_arbiter.rereq_Q2` | `ArbCounterRunsAM.rereqQ2_counter_run` | `cex_Q2`: g1 falls while r1 is high (H_ARB1). Also: A1 and A2 are both high on [51, 63). | sufficient+necessary_at_boundary (for H_ARB1) |
| `bd_arbiter.rereq_R2` | `ArbCounterRunsAM.rereqR2_counter_run` | `cex_R2`: `zr` fails. The z-rise row is tight. | sufficient+necessary_at_boundary (for `zr`) |
| `bd_arbiter.rereq_G2` | `ArbCounterRunsAM.rereqG2_counter_run` | `cex_G2`: g2 falls while r2 is high (H_ARB2). | sufficient+necessary_at_boundary (for H_ARB2) |

What every re-request run meets:
* **Start.** It runs from reset (`FromReset`: every signal low before 0, q = 1).
* **Delays.** Every route, arc and `smin` is nonzero (`AllPos`), and `dz ≥ 1`.
* **Hypotheses that hold.** `Run` for all t, `MB`, `E1`/`E2` on [12, Hz), `ZLine`,
  `Rows1`/`Rows2`, and the two other races in run form. It also meets H_HOLDQ(2),
  RT1/RT1b, RT2a and the A0 fork in run form. The four-phase client re-requests at its
  minimum, `u = T1 + 1`. The other `Arc1`/`Arc2` fields hold.
* **The race under test.** It misses by exactly 1 ps in BOTH the run form and its
  `Arc1`/`Arc2` field.

So each run meets every hypothesis of `e_fields`/`f_fields` except the one race.

The records start from `ArbMultiToken.Dw` (every arc 1, `smin` 3). Raised fields:
* Q: wfb 2, qf 2, Rr1/Rf1 2, and the server's re-rise is 1 ps slower than `smin`.
* R: qf 2, Rrq/Rfq 2, g2r/g2f 2.
* G fall view: wq 2, g1fq 2.
* Q2: wfb 4, Rr2/Rf2 2, c2f 2.
* R2: wq 2, Rrq/Rfq 3, g1rq/g1fq 2.
* G2: wq 3.

## Findings

* **Race Q needs `qf > qr` for an ending run.** At slack −1 the q runt sits in ustate's
  hold loop. With `qr = qf` it would circulate for ever. With `qf = qr + 1`, the
  rise-fast OR channel shrinks the low runt by 1 ps per lap, so it dies.
* **Race Q2 cannot use that fix.** `cex_Q2` itself assumes `qr = qf`. So the 4 ps high runt
  circulates with period `wfb + qr = 5` for as long as both clients request. The run is
  ended past the horizon (Hz = 52) by a legal four-phase continuation:
  1. A0 is high, so A2 latches on a g2 pulse (at 51).
  2. Client 2 then drops r2 (at 52).
  3. The server drops A0 on a low sample of R0 (at 60).
  4. q is forced to 1, and the run settles with client 1 holding.

  On the way, both acks are high on [51, 63). So race Q2 at slack −1 also breaks ack
  exclusion on this run. Lean proves this as the last conjunct.
* **G's fall view alone needs H_RF_ASYM.** It fails only with ugrant O5's q-pin rise and
  fall arcs differing (`g1fq = 2 > g1rq = 1`).
* **The rt1 counter-record is in the box but not at a consistent corner.** Its in-box
  fields are the routed numbers. The fields outside the box (A0 route, ustate O6, server)
  are free choices. The `m1 = -20` instance (`gd_merge6`) cannot give a run with a real O6
  arc, because `qf ≥ 45` alone covers the need there. That is why `gd_merge9` was used.
* **Handover overlap needs H_RF_ASYM.** The violating run needs a 171 ps O6 rise/fall
  asymmetry. At every consistent corner the overlap is 0 (`corner_no_overlap`). The run
  makes the inequality tight; it is not a claim about the board.

## NOT covered

* The re-request records are a 1 to 4 ps grid, not routed numbers.
* The rt1 run covers one box (`gd_merge9_uarb1`) and one direction. rt1b already has
  `OnGcdArbKappaTight.SU_run`.
* No run is chained into C's `AMerge`. That is still goal 2 of B-arb-amerge.md.
* The "sufficient" side of each race keeps its existing theorems (`e_fields` /
  `f_fields`, `early_nonvacuous`). No new slack-0 run was built for the races. For rt1 and
  handover_overlap, the slack-0 runs are `rt1_boundary_run` and `ho_boundary_run`.
