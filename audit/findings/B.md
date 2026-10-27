# Audit of shard B (cells: C-element, latch/link, arbiter) - claude/formal 71ee3e86

Checkout under test: `/home/user/wt-formal` (Lean 4.35.0, core Lean only for these files).
Claims audited: `formal/JOURNAL-B.md` (verdict table and findings), `formal/FEASIBILITY.md`, `formal/notes/B-*.md`.
RTL compared: `/home/user/wt-research/cells/rtl/*.v`; `cells/verify/tighten.py` for rules I and F.

All commands were run from `/home/user/wt-formal/formal/lean` as `lake env lean <file>`, one process at a time.
My files are in `/home/user/asyncfpga3/audit/lean/B/`:
- `Axioms.lean` / `.out`: `#print axioms` on 36 headline theorems.
- `W_CElem.lean`, `W_Data.lean`, `W_Arb.lean`, `W_LinkTimed.lean` (+ `.out`): non-vacuity witnesses and counterexamples where a hypothesis is dropped.
- `mut/`: 12 mutants, plus `results.txt` (controls and mutants).

All four witness files compile with rc=0 and no `sorry`.

## Verdict table (OVERSTATED first)

| # | theorem (file:line) | journal claim (quoted) | what the Lean statement actually says | verdict | evidence |
|---|---|---|---|---|---|
| 1 | `LinkHandshake.setup_iff` (LinkHandshake.lean:1051), with `latch_capture` :887, `pipe_data` :952, `setup_needed` :921 | "exact bundling inequality" | The `iff` is between `arr i + L + F ≤ c i` and its unfolding over the `max`-recursion `arr`. That is an arithmetic identity. SETUP itself is only shown sufficient (`latch_capture`, `pipe_data`). Its necessity is shown by one concrete trace (`setup_needed`, L=F=1). No theorem says that a violation always breaks capture. | **OVERSTATED** (minor) | `W_Data.lean: setup_not_necessary`: all other hypotheses of `latch_capture` hold, SETUP fails (7 > 5), and the conclusion still holds (the old token equals the new one). The condition is exact only as a worst-case-data condition. rc=0. |
| 2 | `CElemFn.c2_spec`..`c3_norst_spec` (CElemFn.lean:105-116), `c2_tied_dontcare` :124 | "8 INITs = spec" | For all Boolean inputs, `lutB INIT [pins per RTL]` equals `~rst·C(..)` / `rst+C(..)`. `cSpec` is an independent list-based C-element (all 1 → 1, all 0 → 0, else hold). The INIT is replicated across tied pins (binary and Kleene). | CONFIRMED | Script: every INIT constant in Cells/*.lean is present verbatim in the RTL (INIT_UNHELD is the inits.py variant). Pin maps checked by eye against bd_ce.v. Mutant M1 (bit 0 of INIT_c2) → 15 errors, including c2_spec. Mutant M1b (bit in the I4=I5=1 word) → caught only by `c2_tied_dontcare`, which is correct. |
| 3 | `CElemTiming.c2_follow_hold` :229 + `runt_oscillates` :331 | "enabling input >= LUT+feedback delay, tight" | Sufficient: with window-delay LUT and wire channels, `a=b=v` for `dlmax+dwmax` ticks, then never both `!v`, gives O=v on `[t0+dlmax, t2+dlmin]`. Tight only for fixed delays: any runt `w < dl+dw` oscillates forever (transport). | CONFIRMED | `W_CElem: follow_hold_hyps` (hypotheses hold on a non-constant square wave). `drop_pulse_cex`: with H_PULSE dropped (runt w=1 < D=2), all other hypotheses hold and the conclusion fails at t=7. rc=0. |
| 4 | `CElemTiming.c2_four_phase` :399 | "four-phase spec with new fork condition" / finding "environment must wait out the feedback wire (E >= dwmax + dlmax - dlmin)" | Under H_ALT..H_RESET_DONE and `dlmax+dwmax ≤ dlmin+E`, O = V k on `[c k+dlmax, c(k+1)-1+dlmin]` for every phase. The repo proves sufficiency only; the "must" (necessity) is asserted in notes, not proved. | CONFIRMED, and **strengthened by audit** | `W_CElem: four_phase_hyps`: all 9 hypotheses hold together for an infinite periodic run (dl=dw=1, E=1). `four_phase_applies` instantiates the theorem. **New:** `drop_env_latency_cex` (dl=1, dw=2, E=1) satisfies every hypothesis except H_ENV_LATENCY, and O glitches to 0 at t=7, inside the promised window. So the fork condition is necessary. Mutant M2 (latency weakened by 1) → proof breaks (omega). |
| 5 | `CTree.reachable_eq_flat` :796, `ctree_eq_flat` :880, `cex_noAck5` :960 | "tree = flat C-element, all shapes, under four-phase with ack wait" | For every tree whose root is a cell and whose cells start at 0: the reachable (phase, inputs, output) sets of the tree and of a flat C-element coincide. The model is speed-independent atomic firing (H_ATOMIC_CELL), and wires are allowed. Width 2..64 is checked by `decide` on the generate block, whose shape matches bd_ctree. Without the ack wait the equality fails. | CONFIRMED (state-set equality, atomic-cell model) | Generate-block recursion compared with bd_ce.v. Mutant M9 (INIT_C4 bit) → 4 errors. |
| 6 | `Latch.holds_value` :205, `hold_of_dack` :332, `link_latch_holds` :347 | "Latch (mux latch, setup/hold, DACK rule H sufficient)" | `holds_value`: the Kleene mux latch with a lumped loop delay ≤ L holds v if en is open L ticks and d=v whenever en≠f. `hold_of_dack` is an omega one-liner: it gives `E ≤ A+R` given en low forever from tc+E and d=v for all t < tc+A+R (from time 0). It covers a single close/transaction only. | CONFIRMED (rule-H part is shallow and single-transaction) | `W_Data: latch_hyps`: the hypotheses of both theorems hold together, with d switching to .f at the close. Mutant M8 (pin swap I0↔I2) → 3 errors. |
| 7 | `LinkHandshake.conservation` :453, `bounded` :467, `deadlock_free` :491, `di_pipe3` :742 | "four-phase refinement, token conservation, half-token bound, deadlock freedom for any N" | Interleaving model with atomic gates (H_FB_FAST) and isochronic forks (H_ISO_FORK): sends − receives = half-tokens in flight ≤ N+1, and some move is enabled in every state. Fork wire delays are covered only for N=1,2,3 (finite kernel check). | CONFIRMED in the stated model (for any N only with isochronic forks) | `Reach` is non-trivially inhabited (`W_Data`, plus the author's `pipe2_full`). Mutant M10 (bit 0 of controller INIT) → 8 errors. M10b (bit in the tied I4/I5 word) survives, which is harmless: those pins are tied to 0 in the RTL, and this file, unlike CElemFn, has no replication check. |
| 8 | `Bundling.capture` :597, `counter_rule_I` :693, `ff_counter_ruleF` :486 | "capture condition derived; rules I and F each miss a term" | `capture` gives q=v for windowed-Kleene latch gates under H_SETUP `max(Ton+ehi, Td+dhi)+fhi ≤ Toff+elo` and H_HOLD. Both counter-traces satisfy the gate relations with transport delays and fail. In Lean, rule I and rule F appear only as hand-transcribed numeric premises (`8+1+2 ≤ 10+1 := by decide`). | CONFIRMED (model level; transcription checked by me in tighten.py) | `tighten.py` ~l.1930: rule I data side = D-pin arrival + max D arc + `loop_wire` (wire only, no I2-pin arc); `audit_fastfall` (l.562) compares max stage-output fall with re-rise and has no in-flight wire term. `W_Data: capture_hyps`: all hypotheses hold with non-constant d and q. Mutant M7 (drop `fhi` from H_SETUP) → proof breaks. "Guardband covers both today" is not checked. |
| 9 | `ArbKleene.kleene_exclusion` :126, `grant_pairs` :137 | "exclusion for all 3-valued inputs; only (X,X) fails" | Over all 27 K3 inputs of ugrant (real INIT/pins, under H_KLEENE_LUT): never both `t`, and the reachable grant pairs are exactly {ff, tf, ft, xf, fx, xx}. It is a property of that one LUT only. | CONFIRMED | Exhaustive. Mutant M6 (GR_INIT bit 39) → 22 errors including exclusion. |
| 10 | `ArbHandover.header_16ps` :370, `overlap_duration_r2_to_r1` :256, `overlap_skew_r2_to_r1_le` :461 | "16 ps claim exact" | In the rise-fast transport channel `LutOut3`, the overlap equals `max 0 (g2f − (qr+w+g1r_q))` exactly. With the bd_prims_sim arcs (56/124, 52/150) and w=0 that is 16 ps. With skew it is capped at 72/94 ps. Model-specific: the numbers are simulator arcs, not silicon. | CONFIRMED (model-specific) | `W_Arb: header_16ps_hyps`: the `Cell` relation and all hypotheses hold over ℤ for t0=0 (closed-form traces), and the 16 is computed through the theorem. Mutant M4 (g1r_q 52→53) → 3 errors. |
| 11 | `ArbHandover.held_protocol` :703 | "held INIT meets the merge's counting precondition in all interleavings" | A kernel-checked inductive invariant (112 states) in a speed-independent, **zero-wire-delay** model, so the A0 fork is isochronic. ArbA0Fork shows the property depends on A0-fork ordering once wires have delay. | CONFIRMED in its model (caveat: the A0 fork is isochronic, which the table line does not mention) | Mutant M5 (held INIT → unheld INIT in `held_closed`) → kernel rejects. |
| 12 | `ArbA0Fork.no_early_ack_iff` :252, `client2_iff` :421, `client2_box` :435, `run_exists` :346 | "rule J's condition exact (iff, both clients, box version)" | For every run of the per-pin transport model (each net makes one transition): A_k never rises iff `wAC+pAC ≤ wSt+pSt+aSt+wQG+pQG+aG+wGC+pGC`. Box: safe on the whole box iff `hi.late ≤ lo.early`. Runs exist for every parameter set. | CONFIRMED | `W_Arb`: both sides of the iff are inhabited on real INITs (`pSafe`: run with A ≡ 0; `pBad`: false ack fires). Mutant M3 (drop `pGC` from `early`) → iff proof breaks. |
| 13 | `LinkTimed.stage_token` :510, `stage_forward` :537 | "stage contract" (6d) | For every token k and bit i: latch output = `val k i` on the stated window, under `CtlEnv` (bd_c2n Loop + timed four-phase env + reset) and `DataPath` (≈10 named timing hypotheses). | CONFIRMED; contract jointly satisfiable | `W_LinkTimed: ctlEnv`, `dataPath`: a concrete infinite periodic run of the real bd_c2n INIT (dl=1, dw=0, E=1) with a one-bit latch whose token value **alternates**. `token_alternates` derives `q(8k+3) = (k even)` from `stage_token`. rc=0. |
| 14 | `TernarySound.A_invariant` :389, `algB_bounded` :601, `arb_runt_opposite` :835, `arb_acks_quiet` :794 | "ternary-sim soundness (7f)" | Eichelberger A/B is sound for every binary GMW run with per-pin causal (unbounded, non-FIFO) wire reads. Algorithm B converges under gate/wire bounds D, W. The 7b arbiter scenarios become theorems on all such runs. These are binary traces: no physical mid-rail values. | CONFIRMED | `W_Arb: runt_hyps`: `Bounded`, `IdleServer` and the final-input hypotheses hold together on the unit-delay run of `arbNet` (inputs r2=1 from step 1). |

Not audited (outside my ~15): ArbBinary, ArbHeldTimed (RT1/RT2), TernaryPhases, MuxTree, analog 7c/7d.

## Axioms

Running `lake env lean audit/lean/B/Axioms.lean` → `Axioms.out`. All 36 headline theorems use only subsets of {propext, Classical.choice, Quot.sound}.

The witness files print axioms for each witness theorem; all are subsets of the same set.

Positive control: an intermediate draft of `setup_not_necessary` that had an error showed `sorryAx`, so the check does detect it.

Repo-wide grep: no `sorry`, `native_decide`, `axiom` or `implemented_by` in Formal/Cells.

## Mutation tests (`mut/results.txt`)

Controls: the unmutated sources of all 9 files compile standalone, rc=0.

| mutant | change | result |
|---|---|---|
| M1 | CElemFn INIT_c2 bit 0 | breaks (15 errors) |
| M1b | CElemFn INIT_c2 bit in the I4=I5=1 word | breaks (only the `tied_dontcare` checks, as intended) |
| M2 | CElemTiming H_ENV_LATENCY +1 | breaks |
| M3 | ArbA0Fork drop `pGC` from `early` | breaks |
| M4 | ArbHandover g1r_q 52→53 | breaks `header_16ps` |
| M5 | ArbHandover held → unheld INIT | kernel rejects |
| M6 | ArbKleene GR_INIT bit 39 | breaks (22 errors) |
| M7 | Bundling drop fhi in H_SETUP | breaks |
| M8 | Latch I0↔I2 pin swap | breaks |
| M9 | CTree INIT_C4 bit | breaks |
| M10 | LinkHandshake INIT_C2N bit 0 | breaks (8 errors) |
| M10b | LinkHandshake INIT_C2N tied-word bit | **survives** |

M10b is harmless: I4/I5 are tied to 0 in the RTL, so only the low word is ever addressed. No mutant of a used INIT bit, delay bound or pin map survived.

## Summary

- No headline claim is refuted.
- One is overstated (minor): the "exact" bundling inequality (`setup_iff`) is an algebraic unfolding of a sufficient condition. It is not necessary in general.
- Model caveats the journal table leaves out:
  - "deadlock freedom for any N" holds only with isochronic forks; the delay-insensitive check covers N ≤ 3.
  - "held arbiter in all interleavings" assumes zero wire delay (isochronic A0 fork).
  - "16 ps exact" uses the simulator's arcs.
  - CTree's equivalence is equality of reachable state sets.
  - Rule-H sufficiency is a one-line arithmetic consequence of single-transaction hypotheses.
- The audit adds one result: the C-element fork condition `E ≥ dwmax + dlmax − dlmin` is **necessary** (Lean counter-model `drop_env_latency_cex`). Shard B had only proved it sufficient.
