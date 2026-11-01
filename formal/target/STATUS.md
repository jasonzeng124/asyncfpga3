# STATUS: hypotheses of the current best theorem about the target

Target: `formal/target/gcd_hw_03e82630.bit` (README.md). Statement: `formal/lean/Formal/Target/Spec.lean`
(`NetCorrect`, pipelined env: expected FALSE for the target, see FOR-RESEARCH 2 / C1; `NetCorrectSeq`, sequential env: the statement to prove. Part I compiles and is frozen 2026-11-01; part II, the Lean decoder, a stub).

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
| S1 | `net` is the target's configuration: Lean round trip of the decoder (features <-> gates) | A | **pip and LUT6-INIT layer checked in Lean** (`FormalWit/RT/All.lean` `roundtrip`, check.sh --wit): the 339,036 features re-encoded from 81,990 gates (73,065 pips, 8,925 LUT6 INITs) plus 16,090 listed leftovers are exactly the 355,126 read-back features, each once. Open: wire-to-node merge (prjxray tileconn), O5/MUXF/CARRY4/output-mux layer, the leftovers' meaning (Python classes) |
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
