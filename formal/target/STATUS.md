# STATUS: hypotheses of the current best theorem about the target

**THE target since 2026-11-01 19:3x UTC (owner decision 1): `formal/target/gcd_ps_e6bb4aec.bit`** (BOARD-QUEUE #4,
full-width operands from the PS; README.md, gcd_ps sections). THE statement: `Spec.NetCorrectSeq DecodedPS.net
DecodedPS.boundary DecodedPS.arbs p T R su Δo` (owner decision 4: sequential environment).
Updated 2026-11-06 (shard A) from the 2026-11-02 journals of all three shards. Everything below is Lean-checked with
standard axioms unless marked; "C" / "B" name the shard whose file it is.

## COUNTEREXAMPLE (shard C, 2026-11-06; audit T28 confirms independently)
`Formal.Net.CexPS.not_netCorrectSeq : ∀ T su Δo, 36 ≤ T → Δo ≤ 3000 → ¬ NetCorrectSeq DecodedPS.net DecodedPS.boundary
DecodedPS.arbs ⟨1, 21/25⟩ T 400000 su Δo` (standard axioms). Plainly: at g = 1 and within-die scatter κ = 0.84 (fast corner,
w = 0) there is an admissible behaviour of THE target in which the pair (1071, 462) is accepted and no result ever comes
back (a C-element, umux16.uya, re-enabled mid-fall, emits ~6 ps runts). C then refuted it at κ = 18/25 = 0.72 too (`CexPS72.not_netCorrectSeq`, T ≥ 62, a quiet deadlock). So THE theorem's margin at g = 1 is below κ = 0.72;
B's sufficient race bound is κ ≤ 0.415, so the g = 1 frontier is in [0.415, 0.72) if both hold (the lower end is not a
theorem yet). By `SpecMono.seq_anti_p` the refutation carries to every (g, κ) with g ≥ 1 and κ ≥ 0.84 (`FrontierPS.not_seq_above`) and κ ≥ 0.72 with T ≥ 62 (`not_seq_above72`), Lean; under
H_RUNT(20 ps) it is open. Details: notes/C-cex-ps.md, FOR-RESEARCH C2.

## COUNTEREXAMPLE UNDER THE HEADLINE HYPOTHESIS H_RUNT(20) (shard A, 2026-11-07; Lean, standard axioms, check.sh OK)
`Formal.Target.CexRunt44.not_netCorrectSeqRunt20 : ∀ T su Δo, 123 ≤ T → Δo ≤ 3000 → ¬ NetCorrectSeqRunt 20 DecodedPS.net
DecodedPS.boundary DecodedPS.arbs ⟨1, 11/25⟩ T 400000 su Δo`; with `FrontierRunt.not_seqRunt_le20_above44`: false for every
g ≥ 1, κ ≥ 11/25 and every runt width w ≤ 20 (so also for the plain statement, w = 0). Witness: shard C's run (the 7 arcs
of SLICE_X32Y45.A6's feedback route, ulink_n_falseResult_85 stage 0, at the top of the window, all else at the bottom),
checked as a `BehavesRunt 20` behaviour by `CexRuntP.RBase` (every LUT pin skips every pulse narrower than 20 ps inside
its window). Shard B proved that race safe for κ ≤ 0.41 at g = 1 (`RaceCertPS.race_margin`). **So the g = 1 margin
of THE statement, with or without the runt filter, is below 0.44; the binding race is safe up to 0.41.**
**Guard axis (2026-11-07 11:3x, Lean):** `CexRuntG16.not_netCorrectSeqRunt20` / `FrontierRunt.not_seqRunt_le20_aboveG16`:
false for every g ≥ 8/5, κ ≥ 0, w ≤ 20, T ≥ 137 (same race; B's sufficient bound for it: g ≤ 1.56 at κ = 0).
**Wider filter (simulation, independently checked):** at w = 40 the same race deadlocks from κ ≈ 0.60 (correct at
0.52), so a wider runt filter buys ~0.15 of κ, no more. **Lean (13:3x):** `FrontierRunt40.not_seqRunt40_above60`:
false for every w ≤ 40, g ≥ 1, κ ≥ 15/25, T ≥ 88.

## THE target: what is proved (as of 2026-11-02, unchanged since)
| piece | theorem | plainly |
|---|---|---|
| decoded netlist | `DecodedPS.net_wf` (A) | the Lean netlist is well formed |
| H_DECODE | `FormalWit.RTPS.Data.roundtrip`, `o5_gates` (A, check.sh --wit) | every pip and LUT INIT bit of the netlist is in the read-back, and every read-back pip/INIT bit is a gate, each once; O5 = low half of its O6 |
| H_PRIM coverage | `Cells.PrimsPS.prim_cover` (B) | every gate is a constant, copy, 2:1 mux, CARRY4 output (A's tables) or LUT5/LUT6 table: nothing unmodelled |
| structure | `CViewPS.collapsed`/`view_complete`, `comb_ranked` (C) | the 19,878 logic gates read through checked copy chains; every loop passes one of 4,597 storage LUTs |
| zero pairs | `CViewPS.correct_n0_all` + `witness_n0` (C) | **`Correct` for n = some 0, every g > 0, 0 ≤ κ < 1, reset R ≥ ⌈(1+κ)g⌉·353 ns** (no H_ARB, no SeqEnv), and its hypotheses are satisfiable |
| one pair, one run | `CViewPS.w1_hyps_and_correct` (C) | a Lean-checked run of the decoded circuit meets EVERY hypothesis of NetCorrectSeq (n = 1, (12,18), g = 1, κ = 0, R = 400 ns, Δo = 3 ns, any T ≥ 220) and its conclusion (out0 = 6): the statement is not vacuous for n = 1 |
| races (S3 data) | `RaceTablePS.table_race_free`, `RaceFrontierPS.table_race_free_gk`, `RaceLinkPS.rows_linked` (B) | for 185 storage nodes, the simulated acknowledgement path is at least as slow as the node's routed feedback for every corner and admissible delay, up to (g, κ) on g²(1+κ)/(1-κ) ≤ 2.433 (g ≤ 1.56 at κ = 0; κ ≤ 0.415 at g = 1); 183 rows tied to the netlist's own arcs and wiring. The rows come from 112 simulated runs (untrusted) |
| switch rules | `SpecFbChain.cfb_switch`, `ArbCleanChain.cq_clean_set_gen` (B), `SpecLoop.*` (C) | a storage LUT (incl. an arbiter state LUT) switches cleanly through its routed feedback when its set condition lasts at least the loop's composite delay |
| token level (S5) | `GcdHw.Seq.gcd_hw_seq` (C) | bdc's gcd graph with a sequential env returns `ps.map gcd`, in order, for any number of pairs |
| parameters | `SpecMono.seq_weaken` (A, 2026-11-06) | the statement at (g', κ', T') and margins su, Δo implies it at every smaller g, κ, T and larger su, Δo: the margin is a down-set |

**NOT proved: NetCorrectSeq on THE target for any n ≥ 1.** Missing (shard C's route, notes/C-route-S4.md): S4 (cell
instances on the collapsed view, per-cell handshake theorems from the switch obligations, bundling windows per channel,
composition to CapNet's channel model and the token graph) and S6 (liveness for n ≥ 1).

## The list (must shrink): hypotheses of the best statement about THE target
For n ≥ 1 there is no theorem yet, so the "current best theorem" is the statement itself; its hypotheses and where
each stands:
| # | hypothesis | allowed? | status (2026-11-06) |
|---|---|---|---|
| 1 | H_DECODE (bitread/bit2fasm, prjxray tables) | allowed | Lean round trip of pips + INIT bits (RTPS); independent connectivity check vs nextpnr: 43,986/43,986 logic pins agree (2026-11-06, Python; it compares Lean pin index i with nextpnr's physical pin A(i+1), so it also confirms the pin order A1..A6 that Spec's `addr` and prjxray's INIT[b] indexing assume); open: wire-to-node merge in Lean, output-mux and carry selects now re-encoded in Lean (`FormalWit.RTPSSel.Data.roundtrip_sel`, 2026-11-06: leftovers 14,322 -> 9,017, every select re-encoded; the 9,017 left have no Spec meaning: FF configuration, LUTRAM DI routing, clock/IO), FASM parsing |
| 2 | H_DELAY(g, κ) (`Adm`) | allowed | stated; per-arc bands are the decoder's prjxray numbers (in the netlist) |
| 3 | H_PRIM (`GateOK`) | allowed | stated; every gate kind covered (PrimsPS) |
| 4 | H_ARB(T) (`ArbOK`) | allowed | stated; non-vacuous at T ≥ 220 for n = 1 (C's witness). Headline T: as LARGE as possible (`seq_anti_T`), at least the slowest state-LUT arc ((1+κ)·664·g ps) to avoid the residual vacuity (audit T5) |
| 5 | H_ENV (`Env`) + SeqEnv | allowed (owner decisions 1, 4) | stated; what it asks of the AXI slave: BOUNDARY-ps.md. Margins: smaller Δo, su are stronger (`seq_mono_Δo/su`); the board's end-channel sink needs **Δo ≤ (1-κ)·535/g ps** (BOUNDARY-ps.md finding 4), so the headline uses such a Δo (0 is strongest) |
| 6 | H_RUNT(w) (optional, owner decision 2) | allowed | `SpecRunt.NetCorrectSeqRunt w`, corrected 2026-11-06 to LUT pins only (audit T9). **2026-11-07: it does not raise the margin.** The statement with w = 20 (the owner's headline) is REFUTED at g = 1, κ = 11/25 and for every g ≥ 1, κ ≥ 11/25, w ≤ 20 (`CexRunt44.not_netCorrectSeqRunt20`, `FrontierRunt.not_seqRunt_le20_above44`, Lean): the binding failure is a race, not a runt. Witness check: `CexRuntP.RBase` (per-LUT-pin jump reads inside the delay window) |
| 7 | everything else | must be derived | restated (A, `AssemblyPS.the_of_plan`) as ONE per-pair hypothesis, a `Plan` (invariant, base, quiet, step) for every behaviour; the all-time bookkeeping of Correct is proved, the circuit argument is not reduced (Plan ≈ Correct per pair); S4 composition and S6 liveness for n ≥ 1: not done |

Previous target: `formal/target/gcd_hw_03e82630.bit` (README.md). Statement: `formal/lean/Formal/Target/Spec.lean`
(`NetCorrect`, pipelined env: expected FALSE for the target, see FOR-RESEARCH 2 / C1; `NetCorrectSeq`, sequential env: the statement to prove. Part I compiles and is frozen 2026-11-01 (changes since: ArbNodes inputs; `Adm` = g-scaled window, owner decision 3); part II, the Lean decoder, a stub).

**Theorems about the target so far (2026-11-01):** `Formal.Target.Decoded.net_wf` (the decoded netlist is
well formed). Shard C's 11g on the target (every read-back instance computes its yosys cell under rho). **Refuted:**
`FormalWit.V9V4.Refute.refuted_range : ∀ T Δo, 656 ≤ T → Δo ≤ 2999 → ¬ NetCorrect net boundary arbs pSlow T 20000 0 Δo`
(the owner's pipelined statement is false for the decoded target; hypotheses used: H_DECODE for `net`, the Spec's
model; standard axioms; `check.sh --wit`). For the sequential statement `NetCorrectSeq`, none. The list below is what `NetCorrect` on the decoded target would need, and where each piece
stands. It must shrink.

| # | hypothesis | allowed (one of the five)? | status |
|---|---|---|---|
| 1 | H_DECODE: prjxray maps the target's bits to features correctly (`bitread`/`bit2fasm`) | allowed | read-back exists; untrusted decoder (tools-A/target) with a Python round trip (0 invented features) and no undriven node in the kernel's cone (Python); C's 11g import agrees at instance level (same walker code as this decoder, so NOT an independent check); **independent**: every LUT/MUXF input pin's driver equals nextpnr's routed netlist (46685 pins incl. CARRY4; 3 don't-care A6 pins differ; out/xcheck_nextpnr.txt); **Lean round trip (pips + LUT6 INIT bits) checked**: `FormalWit.RT.All.roundtrip` (below, S1) |
| 2 | H_DELAY(g, κ): `Adm` in Spec.lean | allowed | stated; band tables from prjxray-db not generated |
| 3 | H_PRIM: `GateOK` in Spec.lean (Boolean, per-pin monotone read times) | allowed | stated; MUXF7/F8, CARRY4 as gates of this kind not yet decoded |
| 4 | H_ARB(T): `ArbOK` | allowed | stated; arbiter node list not generated |
| 5 | H_ENV: `Env` (broad four-phase data rule; margins `su`, `Δo`, reset length `R` as parameters) and, for `NetCorrectSeq`, `SeqEnv` | allowed (SeqEnv: a restriction of the owner's env, forced by the counterexample) | stated |
| 6 | everything else the proof needs | must be derived | the whole proof: cells, timing obligations, loops, composition, refinement to `gcd_hw_graph_computes_gcd`, pipelining (several pairs in flight) |

Existing results that a proof can reuse (not yet bridged to Spec.lean): shard C's FASM import of
the `--freq 100` gcd_hw routes (not this route), `gcd_hw_graph_computes_gcd` (one invocation, token
level), shard B's cell proofs, shard A's XAudit/E9 verdicts (each with hypotheses about the circuit's
own behaviour: ArbEnv, QQuiet, ArbOrd, which THE goal forbids as assumptions).

## What `NetCorrectSeq` on the target still needs (decomposition, 2026-11-01)
| # | obligation | owner | state |
|---|---|---|---|
| S1 | `net` is the target's configuration: Lean round trip of the decoder (features <-> gates) | A | **pip and LUT6-INIT layer checked in Lean** (`FormalWit/RT/All.lean` `roundtrip`, check.sh --wit): the 339,036 features re-encoded from 81,990 gates (73,065 pips, 8,925 LUT6 INITs) plus 16,090 listed leftovers are exactly the 355,126 read-back features, each once. Also `FormalWit.RT.OAll.o5_gates`: every O5 gate has its O6 gate, same name, the O6's first five pins, INIT = O6 INIT mod 2^32. The 16,090 leftovers: 5,460 output-mux selects and 3,206 carry selects (CY0/PRECYINIT) CARRY MEANING and are re-encoded only by roundtrip.py (from hop/carry gate provenance not in the Lean gates); 4,183 FF configuration (FFs are free in the Spec, so no meaning there), 3,084 SLICEM LUT DI routing (no LUTRAM in the design), 157 clock/IO/config. Open: wire-to-node merge (prjxray tileconn), the order of the O6's pins (A1..A6), the output-mux and carry selects in Lean, the leftovers' meaning (Python classes) |
| S2 | timing obligations generated from `net` and proved complete: every bundled link's data settles before its request (settle/hold windows) | C (`Timing/SpecSettle`, no loops yet) | started |
| S3 | the feedback cells (C-elements, latches, arbiters) as Spec gates with their loop timing derived from the bands | B (`ArbTSpec`, `ArbClean`) | started; `spec_double_ack` shows H_ARB alone is not enough: per-arbiter "q settled before A0" must be derived |
| S4 | composition of the cells over the whole decoded network and refinement to the token graph | C | not started on `net` |
| S5 | `gcd_hw_graph_computes_gcd` for any number of pairs under `SeqEnv` (one invocation exists) | C | token-level sequential runs correct in simulation (400/400) |
| S6 | liveness: every handshake completes and the circuit returns to idle under `SeqEnv` | C/A | not started |
Allowed hypotheses in the final statement: H_DECODE (bitread/bit2fasm + the prjxray tables the decoder uses),
H_DELAY(g, κ), H_PRIM (built into `GateOK`), H_ARB(T), H_ENV + SeqEnv. Everything in S1-S6 must be proved.

**Non-vacuity rule for T (audit T5, 2026-11-01):** `ArbOK T` is unsatisfiable once an arbiter's state inputs change and
hold, when T is below that state LUT's own delay (78/g..664·g ps on the target), so `NetCorrect`/`NetCorrectSeq` at such
T is vacuous. Any positive result must use T ≥ the largest state-LUT delay bound, or come with a witness behaviour.
