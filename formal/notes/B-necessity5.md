# B-necessity5: fifth necessity pass over the sufficient-only rows (probe Bnx5)

Shard B, 2026-10-29. Scope: the rows of `formal/out/cell_constraints.json`
still labelled "sufficient", except bd_mux / bdc_muxn / bd_steer (another
probe). The JSON is NOT edited; the table below is the proposed relabelling.

Lean (core only, every file checked with `/tmp/claude-0/btools/bcheck.py`, OK;
`#print axioms` on 29 headline theorems gives `propext`, `Classical.choice`,
`Quot.sound` or a subset; no sorry / native_decide / axiom):

- `formal/lean/Formal/Cells/Necessity5Arb.lean`: bd_arbcell grant_skew (iff), settled exclusion
- `formal/lean/Formal/Cells/Necessity5Delay.lean`: bd_delay[FASTRISE] ack_flush (line level)
- `formal/lean/Formal/Cells/Necessity5PipeRst.lean`: bd_pipe rst_lines, DACK and guard terms
- `formal/lean/Formal/Cells/Necessity5Link.lean`: bd_link_dc rules K' and L'
- `formal/lean/Formal/Cells/Necessity5Flink.lean`: bd_flink qfb_first
- `formal/lean/Formal/Cells/Necessity5Mem.lean`: bd_mem setup / hold / rdata / clk widths (iffs)

Axiom audit file (scratch, not delivered): `/tmp/claude-0/probes/Bnx5/Ax.lean`.

## Method

Same as Bsx / Bsx2 / Bsx3. `Claim s` is the row's shipped theorem with one
hypothesis weakened by `s`, every other hypothesis copied word for word;
`Claim 0` is proved from the shipped theorem; `¬ Claim 1` is an explicit run
(real INITs, gate relations for ALL t, the weakened hypothesis off by exactly
1, the others met, the conclusion false, the run live). That is
"necessary at the boundary": one parameter point. Where a row is marked
**exact**, the Lean statement is a real `↔` over the whole parameter space of
the model. Unless stated, results are for the Lean `≤` form; where the JSON
carries the strict +1 (Bs, Kleene X window at equality), a binary run off by
1 against `≤` is 2 from the JSON form, and the +1 is not addressed here.

## Bsx3's unmerged results (Necessity3Pipe / Necessity3PipeCtl / Necessity3Arb / Necessity3AMerge)

Re-checked (all four files `bcheck` OK at this head) and read. They are
boundary results (one parameter point per row, N = 2 unit control or N = 1),
not iffs; P8 item 1 audited `pipe_I` against the shipped `token` and
confirmed it. Decision: **sufficient+necessary_at_boundary**, not exact, for
every bd_pipe row they cover and for bdc_amerge.bundled_idx_ack_g. For
bd_arbcell.grant_skew this probe proves the iff (below), so that row is
**exact**.

## Table

| row id | old | new | form covered | Lean |
|---|---|---|---|---|
| bd_arbcell.grant_skew | sufficient | **exact** | JSON form = Lean form (margin 0, no strict) | Necessity5Arb.grant_skew_exact, formA_iff, formB_iff, formA_run, formB_run, nonvacuous (Bsx3's two points = bsx3_points) |
| bd_arbcell.settled_exclusion | sufficient | **exact (structural)**: the precondition "both grant outputs read the same q" is exact: overlap iff g1 reads q = 1 while g2 reads q = 0 (and r1 = r2 = 1) | Boolean | Necessity5Arb.settled_iff, settled_overlap_needs_both |
| bd_pipe.boundary_I | sufficient | s+n_at_boundary | Lean = JSON (no strict) | Necessity3Pipe.tok0, I_false, I_viol |
| bd_pipe.boundary_H | sufficient | s+n_at_boundary | Lean = JSON | Necessity3Pipe.tok0, H_false, H_viol |
| bd_pipe.data_lead | sufficient | s+n_at_boundary (Lean form; the classic request-after-data form stays not necessary) | Lean = JSON | Necessity3Pipe.tok0, L_false, L_viol |
| bd_pipe.output | sufficient | s+n_at_boundary | Lean = JSON | Necessity3Pipe.out0, out_false, O_viol |
| bd_pipe.lat_lumped | sufficient | s+n_at_boundary (N = 1 run; H_LUT_FIFO model, see sel_order) | Lean `≤`; JSON strict +1 not addressed | Necessity3PipeCtl.ctl0, lat_false, lat_viol, lat_exc |
| bd_pipe.rst_lines | sufficient | s+n_at_boundary for all four PipeTimedN terms (H_RST_LONG and the request-line, DACK and guard terms of H_RST_LINES); H_RST_SEL (PipePerPin per-pin, 6g) still sufficient | Lean `≤`; loop terms' strict +1 not addressed | Necessity3PipeCtl.long_false, lines_false; **Necessity5PipeRst.ctlA0, dack_false, guard_false, dack_viol, guard_viol, run_live** |
| bd_delay[FASTRISE].ack_flush | sufficient | DACK ≤ 2: **exact** at line level, point delays; DACK ≥ 3: **not_necessary**, exact replacement `Succ` (every copy but the slowest has a later copy at most w behind it) | line level, point delays (one corner); JSON form (margin 0) = Flush | Necessity5Delay.pulse_iff, flush_succ, two_exact, flush_not_necessary, dack3_clean, dack3_viol, dack2_glitch, dack2_viol, dack2_ok |
| bd_link_dc.rule_K_corrected | sufficient | s+n_at_boundary | Lean `≤` at guard 0 | Necessity5Link.claim0, k1_false (Bk's counter_K run, RuleK' off by 1, RuleL' met), witness |
| bd_link_dc.rule_L_corrected | sufficient | s+n_at_boundary | Lean `≤` at guard 0 | Necessity5Link.claim0, l1_false, l_stage, l_viol, l_k_ok, witness |
| bd_flink.qfb_first | sufficient | s+n_at_boundary | Lean `≤`; JSON strict +1 not addressed | Necessity5Flink.q0, q1_false, q_viol, f_runt, f_clean |
| bd_mem.setup | sufficient | **exact** (event model) | Lean = JSON | Necessity5Mem.setup_exact |
| bd_mem.hold | sufficient | **exact** (event model) | Lean = JSON | Necessity5Mem.hold_exact |
| bd_mem.rdata_before_ack | sufficient | **exact** for `tCO ≤ dcLo` (event model); the JSON's added H_RDATA_ROUTE skew term is not in the Lean | Lean part only | Necessity5Mem.rdata_exact |
| bd_mem.clk_high_width | sufficient | **not_necessary**; exact replacement `tPWH ≤ dcLo + dsLoF` | Lean = JSON | Necessity5Mem.clk_high_exact, clk_high_tight, clk_high_not_necessary (also clk_low_exact for clk_low_ok) |
| bdc_amerge.bundled_idx_ack_g | sufficient | s+n_at_boundary (+ general counter at the minimal capture) | Lean `≤` | Necessity3AMerge.gack0, gack_counter, gack1_false |
| bd_merge.reset_first | sufficient | not_necessary as written (reclassification from existing Lean): loop terms s+n_at_instance, H_RST_EARLY replaced by H_NO_RETURN, wire terms unanalysed | — | NecessityReset.c2_box_exact, early_request_ok, returned_pulse_lost (no new Lean) |
| gcd_rig.token_static | sufficient | structural (no inequality: decided on the elaborated netlist; nothing to weaken by 1) | — | unchanged (ResetGcd.gcd_frontier_fire, ResetContract.c2n_frontier) |
| bd_arbcell.bbm | sufficient | unchanged (not attempted: involution model, no static form) | — | — |
| design.rst_flush | sufficient | unchanged (not attempted, see below) | — | — |

## Plain-language statements of the new results

**grant_skew (Necessity5Arb).** Assumed: `ArbBinary`'s transport model of
bd_arbcell (real INITs, one q loop delay `L ≥ 1` to both LUTs' I2, grant arcs
d5, d6, H_INIT_SETTLED, H_REQ_SEP). Proved: for every delay triple,
"no trace meeting the hypotheses ever has both grants high" iff
`|d6 - d5| ≤ L`. The violating side is an opposite-sense handover with
request edges exactly `L + 1` apart, built for every violating triple (q
moves, so the run is a real handover). Not covered: Kleene X on q, skew
between the two I2 branches of the q net, request routing skew, inertial /
involution channels (bbm).

**Settled exclusion (Necessity5Arb).** With g1 reading `qa` and g2 reading
`qb`: exclusion for every request vector iff not (qa = 1 and qb = 0); an
overlap also needs both requests up. So the structural fact holds exactly
when the two grant outputs cannot read different q values, which is what
the q-branch skew (not modelled) would break.

**FASTRISE ack_flush (Necessity5Delay).** What the pipe needs from the DACK
line (`orn_hold_true`'s conclusion) is: a node high phase of width w comes
out as ONE stretch from the fastest copy's rise to the slowest copy's fall.
With point delays this holds iff each copy except the slowest has a later
copy at most w behind it (`pulse_iff`). H_ACK_FLUSH (total spread ≤ w)
implies that, and is exact with two copies (DACK = 2, `two_exact`), but from
three copies on it is not necessary: the real DACK = 3 chain at unit hops
(copies 3, 2, 1) with w = 1 violates H_ACK_FLUSH by 1 and still gives one
clean pulse (`dack3_clean`, real BUF / FR_SIDE INITs, all t). The boundary
glitch: DACK = 2, buffer 1 + chain hop 2 against tap 1, w = 1 (H_ACK_FLUSH
off by 1) gives two pulses, low at 12 (`dack2_glitch`). Not covered:
window (non-point) delays for the sufficiency of `Succ`; no pipe-level run
with the glitch (so `pipe_ctl` itself is not refuted), and the pipe's Won is
a lower bound of the phase width. gcd_hw's DACK placeholder is 6 and
tightened per route (0-5), so the DACK ≥ 3 case is live.

**rst_lines DACK and guard terms (Necessity5PipeRst).** Assumed: the
two-stage PipeTimedN run of `Wit` (real bd_c2n INIT, unit arcs, R = 4).
Proved: with boundary 1's DACK line reading stage 1's power-up value until 4
(`L1.hi + ahi1 = R + 1`), or with the line's relation in force only from
`Ag = R + 1`, stage 0's ack pin still reads 1 at release; stage 0 rises at 6
instead of 5 and the whole run is the nominal one shifted by one tick, for
ever. Every other hypothesis holds; `nodes_clean` fails at stage 0, t = 5.
Together with Bsx3's H_RST_LONG and request-line runs, every PipeTimedN term
of rst_lines is now boundary-tight. Not covered: H_RST_SEL (PipePerPin).

**bd_link_dc K' / L' (Necessity5Link).** Assumed: a whole bd_link_dc stage,
every LUT its real INIT as a transport gate (one corner), four-phase
environment, guard 0, feedback-pin arc 1. K: Bk's counter_K run verbatim:
RuleK' off by exactly 1, RuleL' met, every other `dc_capture` hypothesis met;
the bit sees D = 1 from 8 and holds 0 at 11. L: Bk's counter_L run with the
sender re-raising its request at 4 (after `a` fell at 3) and `req_in -> ub`
3, so RuleK' holds with equality and RuleL' is off by exactly 1; the bit
holds 0 at 9. Non-vacuity: the K stage with a 2-tick loop meets both
corrected rules and captures (`witness`, via the shipped theorem). Not
covered: guards > 0, wider windows, H_LT_FALL_K/L themselves.

**bd_flink qfb_first (Necessity5Flink).** The flink twin of P3's mlink
`qfb_counter`, now in Claim form: every other hypothesis of
`flink_qfb_first_timed` holds (A = B = 0, Tq = 6, Td = 5, Toff2 = 7,
Tnext = 9, H_GAP and H_HOLD met), H_QFB_FIRST_T is 9 ≤ 8 + 1 (off by 1), and
`done` rises at 6, falls at 8, period 3 for ever. Clean twin at fhi = 2.

**bd_mem (Necessity5Mem).** In the MemPort event model (line bounds,
four-phase environment, datasheet constants), for every port's numbers the
fastest access (`fast`) attains each bound, so setup, hold, rdata and the
clock-low width are iffs. The clock-high condition shipped by P3
(`tPWH + dsHi ≤ dsLo + dcLo + dsLoF`) is NOT necessary: the clock high
phase is measured from the clock's own rise, so it is at least
`dcLo + dsLoF` on every port (`clk_high_tight`) and the exact condition is
`tPWH ≤ dcLo + dsLoF`. Not covered: BRAM behaviour on violation (no gate
model), H_RDATA_ROUTE, payload routing skew.

## Findings for the cell owner

1. **H_ACK_FLUSH is the wrong form for DACK ≥ 3.** The total-spread
   condition over-constrains the FASTRISE line; the exact line condition
   only bounds consecutive copy gaps (one hop for a uniform chain). A
   checker using `ahi - alo ≤ Won` rejects lines that are clean. Whether the
   pipe needs more than the line condition is open (no pipe-level run).
2. **bd_mem's clock-high check is conservative by the setup line's rise
   spread** (`dsHi - dsLo`): `tPWH ≤ dcLo + dsLoF` is exact.
3. **Stray acks at release cost a tick, they do not corrupt** in the runs
   built here: the c2n controller only waits. The pipe's phase-timing
   conclusion breaks; data correctness under the delay was not examined.
4. grant_skew: the bound is exact over the whole parameter space of the
   transport model, so it cannot be relaxed anywhere, not just at L = 4.

## Not done

- design.rst_flush: the GMW bound `(m+1)(D+W+1)` is a statement during
  reset; a necessity question needs a lower-bound run on a rank-m chain in
  `TernarySound.Run` (each gate at its slowest, wires at W). Not built.
  The bound looks conservative by about one rank's `D+W+1`; not proved.
- bd_arbcell.bbm (involution, no static form).
- H_RST_SEL (PipePerPin per-pin model).
- Pipe-level counter-run for ack_flush.
- Kleene X strict +1 on any row (the binary runs do not address it).
