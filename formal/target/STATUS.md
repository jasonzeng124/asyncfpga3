# STATUS: hypotheses of the current best theorem about the target

Target: `formal/target/gcd_hw_03e82630.bit` (README.md). Statement: `formal/lean/Formal/Target/Spec.lean`
(`NetCorrect`, pipelined env: expected FALSE for the target, see FOR-RESEARCH 2 / C1; `NetCorrectSeq`, sequential env: the statement to prove. Part I compiles and is frozen 2026-11-01; part II, the Lean decoder, a stub).

**Current best theorem about the target: none.** No Lean theorem yet has the target's netlist in
it. The list below is what `NetCorrect` on the decoded target would need, and where each piece
stands. It must shrink.

| # | hypothesis | allowed (one of the five)? | status |
|---|---|---|---|
| 1 | H_DECODE: prjxray maps the target's bits to features correctly (`bitread`/`bit2fasm`) | allowed | read-back exists; untrusted decoder (tools-A/target) with a Python round trip, 0 invented features; Lean decoder data + round trip not written |
| 2 | H_DELAY(g, κ): `Adm` in Spec.lean | allowed | stated; band tables from prjxray-db not generated |
| 3 | H_PRIM: `GateOK` in Spec.lean (Boolean, per-pin monotone read times) | allowed | stated; MUXF7/F8, CARRY4 as gates of this kind not yet decoded |
| 4 | H_ARB(T): `ArbOK` | allowed | stated; arbiter node list not generated |
| 5 | H_ENV: `Env` (broad four-phase data rule; margins `su`, `Δo`, reset length `R` as parameters) and, for `NetCorrectSeq`, `SeqEnv` | allowed (SeqEnv: a restriction of the owner's env, forced by the counterexample) | stated |
| 6 | everything else the proof needs | must be derived | the whole proof: cells, timing obligations, loops, composition, refinement to `gcd_hw_graph_computes_gcd`, pipelining (several pairs in flight) |

Existing results that a proof can reuse (not yet bridged to Spec.lean): shard C's FASM import of
the `--freq 100` gcd_hw routes (not this route), `gcd_hw_graph_computes_gcd` (one invocation, token
level), shard B's cell proofs, shard A's XAudit/E9 verdicts (each with hypotheses about the circuit's
own behaviour: ArbEnv, QQuiet, ArbOrd, which THE goal forbids as assumptions).
