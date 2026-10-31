# Gate-level formalization of asyncfpga3: feasibility

Owner's question: can this project's circuits be formalized at gate level and
proved correct (in Lean 4 or similar), and how feasible is that?
Program: `formal/PROGRAM.md`. Shard A writes this file from all three shards'
journals (`JOURNAL.md`, `JOURNAL-B.md`, `JOURNAL-C.md`) and `formal/notes/`.

**Status: a verdict for every track (1–13). Updated as the 48-hour phases (PROGRAM.md) land.**

**2026-10-31 (lead), in one paragraph.** Whole-project `check.sh` OK (lake build, 64,216 library declarations,
standard axioms). The routed-timing verdict on the corrected arbiter core no longer assumes the refuted HARB7:
the arbiter is checked at its real LUTs, and what remains about it is named (ArbEdge: quiet start, settle bound,
edge windows, and QClean, now derived from quiet input reads; ArbOrd, the in-corner spread). Under those, every
checked premise holds on 10 of 16 rebuilt gcd_hw rows, and without ArbOrd on 10 ipow/xorshift rows. Not yet: a
link from this skeleton verdict to C's H_BUNDLE/H_CELLS, so gcd correctness on the routed design still rests
on C's capstone hypotheses.

## Short answer (provisional)

Yes for the logic and timing layers, with work: everything the probes have
tried so far at the cell level checks in Lean 4 with no `sorry`, no extra
axiom and no `native_decide`, in hours per probe rather than weeks. Gate-level
statements are cheap because a LUT is a finite object (`decide +kernel`
handles all 3^6 Kleene input vectors of one LUT6 in about 2.5 s). The hard and
expensive parts are not the proofs. They are (1) the **hypotheses about the
silicon** that every theorem needs (the Kleene behaviour of a LUT with a
mid-rail input, delay bands that are correlated across a die, the arbiter's
analog resolution), which no proof can discharge and which need GLS or board
experiments; and (2) **connecting** the proofs to the real routed design
(netlist import, delay numbers per arc), which is engineering.

## Status against the owner's three goals (2026-10-29 ~08:40 UTC; drafted by probe FeasDraft from all three journals and the audit, reviewed by the lead; A's rows updated 2026-10-31)

1. **A correct model of the chip.**
   - **Checked in Lean (A, this session):**
     - the LUT as an A6-rooted mux tree with per-pin transport (`Core/LutTree`, `Events2Pin`);
     - LUT6_2, MUXF7/F8, CARRY4 and the slice OUTMUX/site hops, with prjxray-db numbers generated
       per corner (`Core/Prims/{Xray,XrayData,Muxf,Carry,Lut62,Hops,GenCheck}`, PrimsComb, 1331
       decls). MUXF Kleene mux: a select change with equal data is glitch-free for any delays, and
       the select-rises-while-deselected-input-changes glitch is forced for every admissible delay
       pair. CARRY4: no single-pin hazard, and a two-pin (S0, DI0) hazard on CO0 whose order the
       prjxray bands allow at both corners;
     - pure, inertial, involution and SAF channels. New this session:
       - the full IDM trace semantics with chained cancellation (`Core/Delay/InvolutionTrace`, 321
         decls; the real exp/log instance is not checked);
       - the involution OR loop: a unique critical runt s*, unbounded resolution time near it, and
         s* > δ∞/2 strictly for symmetric channels (`Core/Delay/InvolutionLoop`, `crit_unique`; at
         orbit level, not yet every signal solution);
     - what a passing GLS run implies: `GLSPass`, fixed for autoImplicit=false, which answers audit
       `6863284` "GLSPass ... OK" REFUTED (not re-audited). For research's per-pin fid GLS:
       `GLSFid`, `GLSPass2`. One run fixes the final values past the STA horizon. The min and max
       runs bracket the band only for acyclic monotone nets with rising inputs;
     - the shared corner plus local scatter κ (`Corner`, `CornerDiff`, `CornerCode`, `CornerNat`).
       The value of κ is unmeasured;
     - flops and latches (`Core/Prims/Seq{Next,Flop,Latch,Xray,Gls,Sync}`, PrimsSeq, 845 decls):
       per-input setup/hold windows, X bounded by cqHi+res then definite (res = named
       H_FF_RESOLVE, no MTBF, a free parameter: so x_contained / sync_two_flop restate that
       assumption rather than derive it, audit `53d5cc9`), two-flop synchronizer; prjxray ships no fast-corner setup/hold
       (H_WINDOW_SLOW_ONLY). **2026-10-31:** the windows were SLICEL-only, and a SLICEM flop's D
       hold is 262 ps against SLICEL's 241 (unsafe side; audit `53d5cc9` P10b OVERSTATED). SLICEM
       numbers added (`SeqXray.regFFM/ff5M/latM`, site-selected `regFFAt`, `slicem_hold_longer`);
       the site type of a placed flop is the named H_FF_SITE.
     - DSP48E1 as ipow uses it (`Core/Prims/{Dsp,DspData,DspTimed}`, PrimsDSP, 700 decls): the combinational cascade = (a*b) mod 2^32 for all inputs; sound coarse X model; lumped settle bound (7267/3074 ps), tight to 1 ps only for a single generic stage, not for the composed 6-DSP cascade, and with zero cascade wire assumed (audit `8c97528` minor OVERSTATED);
     - xaudit sound in continuous time (`Core/XSimChan*`, `XAudit/Sound*`, XSound2, 1470 decls): transport channels, and inertial iff ρ ≤ (hi+1−lo)·q (the 'only if' is about the ChanCells cover property; an end-to-end wrong verdict is shown at one point only, audit `9e1499e`);
     - the arbiter loop at signal level (`Core/Delay/InvolutionLoop{Bridge,Signal,Rate}`, InvLoop2, 994 decls): for every solution q latches iff s > s*, loses iff s < s*, oscillates forever iff s = s*; laps to resolution between two logarithmic bounds under channel slope bounds;
   - **From shard B:**
     - `KleeneWin`: each binary edge gets its own X window, and every race gains c + a exactly. This
       drops the assumption H_X_UNIFORM;
     - `KleenePess`: a pessimistic bracket strict ≤ model ≤ H_KLEENE_LUT. Every safety and exclusion
       result transfers to it. Every result that needs a definite output (hold, restore, reset)
       needs pass(v) instead. This answers audit `abe7d25` KleeneBox: "H_KLEENE_LUT is the
       hazard-free extension (optimistic)".
   - **Open:**
     - RAMB18E1 is not modelled (bd_mem's BRAM is opaque in Gen; probe PrimsRam launched);
     - which channel the silicon LUT is (transport, inertial or involution) is a hypothesis, with no
       measured pulse-rejection figure;
     - per-edge windows have no data (prjxray has fast and slow corners only);
     - κ is unmeasured;
     - the research GLS's flop reads x on SR/CE as 0, and its resolver centre has no derivation
       (Fid3, [C]).

2. **A correct gcd.**
   - **2026-10-31 (from JOURNAL-B / JOURNAL-C, not re-checked by A):** B's driver-bound gate-level
     theorem `gcd_hw_safe_fin_netB` (every tied cell's pins driven by the netlist-named cell) now has a
     joint witness (`gcd_hw_fin_netB_witness`, one run a=12, b=18, unit LUT delay, wire delays 1-3, out0
     latches 6); C's H_OTHER for the 192 non-link operators is still a hypothesis. B withdrew "FEnv1
     derived" and "first joint witness" for Bfin2/Bfin3 (audit P12b). C repaired TxWin (audit P12a row 18:
     the old form forced infinitely many offers, so phys4/phys5 were vacuous on terminating runs) with a
     finite witness, and accepted "96 of 221 sampled channels checked against Formal.Gen, H_FN on
     H_ZD_BITS + H_WIDTH" (row 19). Claimed 8z5: H_NO_DEADLOCK'' narrowed to NoBlock (still open).
   - **Token level [L]:** bdc's gcd_hw graph returns `Nat.gcd a b` for a, b < 2^31 on every
     schedule, live and bounded without fairness (`Net/GcdHwLive.gcd_hw_graph_computes_gcd`,
     8i/8k).
   - **Circuit level, safety [L]: `Net/CapstoneWalk.gcd_hw_circuit_safe3`.** For a, b < 2^31, every
     out0 latch of the concrete 465-channel network is `Nat.gcd a b`, under three hypotheses:
     H_CELLS (the unit-time Ops gate models), H_BUNDLE (`Held`, on zero-delay traces) and
     H_START_ONCE. H_WALK is now a theorem (`gcd_hw_walk`, 8s).
     - Non-vacuity: `Net/CapstoneWitness3.gcd_hw_joint_witness3` (and `gcd_hw_witness3_consistent`,
       which applies `gcd_hw_circuit_safe3` to it): one run (a=12, b=18) that meets all three
       hypotheses and latches 6. The run is the 8t run of `CapstoneWitness.gcd_hw_joint_witness`
       (audit `299a16f` CONFIRMED: one input, one unit-delay schedule, sources offer once).
     - The audit `f4696cc` row on the capstone confirms it as SAFETY only. H_CELLS is not derived
       from the netlist, and the arbiter model assumes the grants never overlap.
   - **What is still open on the way to "the routed gcd_hw":**
     - **Cells → H_CELLS.**
       - B's own ledger (Bhyp2) found that no B cell hypothesis is a Lean hypothesis of any
         capstone theorem. B's rows enter only through unmechanised bridges.
       - Since then, B proved:
         - `LutFbBridge`/`LutFbBridge2`: C's LutFb/FbFirst premises follow from B's physical
           model plus a four-phase environment;
         - `Cells/LutFbBridge2Env.gcd_hw_safe_phys_links`: H_CELLS for the 175 links is replaced by
           B's physical link model. Its statement still takes H_CM_FORCED (read in the Lean), and
           each link's environment Env1 is assumed. The circle cell ← Env1 ← neighbours is not
           closed for the network;
         - `ContractBridge`: H_CTREE_ATOMIC, H_SEL_PIN (steer and mux) and ungated H_DELAY_LUMPED
           from B's models.
       - **H_ARB_EXCL as stated is not derivable from B's per-pin arbiter**
         (`ContractBridge.arb_excl_not_derivable`). It holds per arbitration only, inside B's
         QUIET/COMMIT window.
     - **Physical → zero-delay (C-8x).** B proved the cell half for one token
       (`ZeroDelayRefine`: a bd_link stage refines iff its six rows hold, `link_ref_iff`). Steer and
       mux are also covered. The network half and multi-token are open. C's 8x is running.
     - **Laps.**
       - H_START_ONCE is false over a rig run. First result only: `Net/CapstoneRig.gcd_rig_first`,
         and `Cells/RigSrc.gcd_rig_first_env` with the env cells.
       - B now has joint witnesses for the env form (`SelfAuditB6.rig_env_feeds`, degenerate in its
         delays; `RigSrcWitness.gcd_rig_first_env_joint`, lagging read maps, urdly 7). This answers audit `ae791b6, 824f130`
         UNVERIFIED (not re-audited).
       - Every result: `Cells/RigLaps.gcd_rig_every` holds under LapInv. It has no witness, and
         `lap_cut_fails` shows LapInv fails at a close when the p_end loop beats out0's return
         (H_PEND_FAST, expected on silicon).
     - **Liveness:** `Net/CapstoneLiveNdWalk.gcd_hw_live_final`. The first out0 token comes within
       (1168(8 Lrun+23)+1)(H+1) ticks, carrying gcd, under H_CELLS, H_BUNDLE, H_START_ONCE,
       H_BOUNDED_DELAY', H_START_ENV, H_ARB_UNCONTESTED_BOUNDED and the open H_NO_DEADLOCK'. Audit
       `fccbd1b` CONFIRMED it as conditional: there is no witness, because the 8t run violates
       H_BOUNDED_DELAY'. C's 8z2 is running.
     - **Reset:** `Cells/ResetCapstone.gcd_hw_safe_after_reset` connects B's GMW reset to C's safety
       from T0 = 23(D+W+1). H_MAP has no mechanised table, and B's self-audit 4 found MapOK too weak
       (it admits a non-wiring map). H_CELLS_AFTER is assumed.
     - **Routed timing:**
       - Per-obligation tcheck rows, matched to the Ops fields by hand (8w: 4500/4572 rows
         matched).
       - A's `Core/XAudit/Events8Beh.design_verdict8`: CLEAN at the slow and fast corners on the 4
         seeds, under SatPin, constant wires and reset, H_ARB (HARB7), SelOK, SelPart and HDsub. **2026-10-29: HDsub is discharged (`Events9.design_verdict9`), but H_ARB as encoded (HARB7) is FALSE on real uncontested bd_arbiter runs (`Core/XAudit/Events8Arb.unc_not_harb`: R0 can rise before the grant from ustate's own q read; the virtual grant is 2 steps late), and C's untimed `Unc 0` is not enough (`noFree_not_harb`). So the CLEAN verdict currently covers no real run. A corrected virtual core and the sufficiency proof are probe E8ArbFix.** **E8ArbFix (2026-10-29): with the corrected core (each reader of q gets its own pin band; R0 a merge of two shadow grants) the real cell is proved a behaviour of it at cell level under per-reader timing conditions B1/B2/C and a settle bound H (`Events9Arb.core_of_settle`, checked; audit P12c 2b: it leaves q free -- the real state LUT enters only through the settle bound hstall, which may be ~1e12, and four RdOK hypotheses; its non-vacuity witness has one client active; and `design_verdict9arb` takes HARB7 from HARB7' by projection, so the corrected core adds no soundness to the design verdict), and it fits 576/576 recorded arbiter runs; but xevents9 with it gives NO CLEAN gcd_hw row: 54 structural residuals per row (6 per arbiter, all relying on "R0 is a merge of the grants"), needing a new liveness rule (probe E9Par).** **Other hypotheses of the verdict (2026-10-29, claimed):** HDsub proved (`Events9`); SelOK at real pins derived from an H_BUNDLE-shaped hypothesis (audit P12c 2a: it is assumed as Held on A's own wires, not imported from a C theorem, and the channel map's entOK only checks that a buffer route exists), with hold rows (`Events9Sel*`; split rows CLEAN on all slow/fast/gb rows, but the split lag is a named hypothesis, not a causal consequence: `Events9PrefixSel.sibling_lag_neg`); a prefix-by-prefix verdict (`Events9Prefix.design_verdict9_upto`) with H_ACK_LAG replaced by checked rows at a source-anchored lag (rows not yet generated: probe E9SelRun). Remaining on a row: SatPin (the model), constants/reset, C's H_BUNDLE, setup, and the arbiter (corrected core + liveness rule + Unc).
         Audit `eb346fb` CONFIRMED it conditional on those hypotheses; its Lean certificates are
         UNVERIFIED. The gb ENTRY claim was OVERSTATED: E8Mux reran it with the OUTMUX hop, and 2 of
         3 failures are real ([C], same Lean checker).
     - **Routed timing, 2026-10-31 (A):** the corrected-core verdicts left unclaimed on 10-29 are now
       claimed (Events9Par, SelL/SelJ, Setup/Full, ArbNet/ArbNetEdge), and one combined statement,
       `Core/XAudit/Events9FullArb.design_verdict9_full_arb`, removes HARB7'/HRst: they are replaced by
       decidable checks at the real bd_arbiter LUTs (ArbOK, from the INITs and read paths) plus the rows
       ArbRowsOK, and by per-arbiter edge-window hypotheses ArbEdge (QClean = no metastable runt; a quiet
       start; a settle bound; no re-request while switching; A0 high around request falls). gcd_hw R5 was
       rebuilt (4 seeds, md5s identical to 10-29), and every committed run reproduced byte for byte.
       **Negative:** ArbRowsOK holds for only 3-7 of 9 arbiters at slow/fast and 0-1 at gb/indep. Only the
       B1 row fails: the real grant can fall through its q pin before its request pin sees the request
       fall, and the core's C-element grant cannot. This is an abstraction limit, not a demonstrated
       failure (`notes/A-e9arbnet.md`). So the combined theorem covers **no** gcd_hw row yet.
       **Later the same day:** B1 holds on every failing reader if the arcs share their position inside
       the band (min margin 51 ps), and also under path scatter κ ≤ ~0.047 (untrusted print). Making B1 a
       behaviour hypothesis ArbOrd (`Events9ArbB1`; `ord_of_row`: automatic where the band row holds) gives
       `Events9FullArb.design_verdict9arbnet_ord`. All its checked premises hold on **10 gcd_hw rows**
       (slow/fast on all 4 seeds, gb on 3/4). Those rows rest on SatPin, constants/reset, ArbEdge, ArbOrd
       (the in-corner correlation question), SelOK and SelPart. This is the routed control skeleton, not
       gcd correctness. **Joint satisfiability of these hypotheses on a real gcd_hw/ipow/xorshift run is not
       shown** (no witness), so the rows are conditional, not shown non-vacuous.
     - **Arbiters vs κ:**
       - B's `OnGcdArbKappa` is safe for κ ≤ 16587/374773 ≈ 0.0443. That is the server-free arc
         form, tight on the 1 fs grid for its binding row (`OnGcdArbKappaTight.rt1b_safe` /
         `rt1b_unsafe`; answers audit `861de85` "tight" mildly OVERSTATED, not re-audited). It is
         **not** a gate-level threshold of the routed design.
       - With the server, the A0 branch and the ustate arc credited (`OnGcdArbKappaSrv`):
         - D1 (the bare cell) is safe to κ ≈ 0.0802, but its counterexample needs a
           non-four-phase withdrawal;
         - D2 (the 12 held four-phase forms) is safe to κ ≈ 0.2166.
       - Which of D1 and D2 applies to gcd_hw is open.
       - The cons reading fails at κ = 0 on two rows.
       - Arc data provenance is UNVERIFIED (audit `7c4df29` ArbPin2). κ itself is unmeasured.
     - **Data path:** H_COMPUTE_FN (the yosys fused units compute bdc's expression) is not proved.
   - **Every hypothesis, graded, with the theorem that uses it and the test that would settle it:**
     `out/gcd_hw_hypotheses.md` (refreshed 2026-10-29 from B's `notes/B-gcd-hyps-for-A.md`,
     JOURNAL-C and this section).

3. **Reusable on other designs.**
   - **How-to:** `out/HOWTO-new-kernel.md` (A: xaudit, xevents) and `notes/C-howto-new-kernel.md`
     (C: tcheck).
   - **Second kernel at circuit level [L]:** `Net/IpowCapMain.ipow_circuit_safe3`. Every out0
     latch of the concrete ipow network is `ipowSpec b e`. Audit `8965ea0` CONFIRMED it, incl.
     non-vacuity (3^7 and a wrapping vector; the spec uses i32 wrap). It has the same hypothesis
     shape as gcd (H_CELLS, H_BUNDLE, H_START_ONCE).
     - B's `IpowCells.ipow_safe_of_contracts` replaces H_CELLS by per-cell contracts. But
       `ContractBridge.fbCel_iff_si` shows the feedback contract is equivalent to the bare SI step,
       so those contracts carry **no timing content** as stated. B's fix probe Bfc is running.
     - ipow's two multiplies (3 cascaded DSP48E1 each) were unmodelled by every shard until
       PrimsDSP (`Core/Prims/Dsp*`, claimed 2026-10-29: the cascade computes (a*b) mod 2^32; settle bound 7267/3074 ps prjxray, zero cascade wire).
   - **Token level [L]:** ipow for all i32. Collatz only conditional on C termination
     (unconditional for 1 ≤ n < 256; 8v).
   - **Routed:**
     - tcheck on 12 collatz/xorshift/ipow routes (10n, [C] front end, proved core). No disagreement
       is a fixed-point prjxray failure. Finding for research: rule A times GND/VCC tie-offs as data
       (audit `7f46f23` CONFIRMED).
     - Collatz: xevents5/7 CLEAN at slow and fast on 4 seeds (A-k2); xaudit certifies one
       transaction at slowmax only.
     - A's K3 (xevents8 on ipow and xorshift, 10-29). xorshift seeds 4 and 6 did not place.
     - **2026-10-31, current tool (A):** corrected arbiter core + arbiter link (`k3/run_e9_k3.sh`) on the
       rebuilt ipow/xorshift (md5s reproduce). On 10 rows (ipow 3/5, xorshift 5/8/9, each at slow and fast)
       every checked premise of `Events9FullArb.design_verdict9arbnet_edge` holds (xevents9par CLEAN,
       ArbOK + ArbRowsOK 2/2, OwnOK/RsOK/FixShape). So for those routes the routed control skeleton's
       verdict rests on SatPin, constants/reset, the per-arbiter edge windows ArbEdge (no metastable runt,
       quiet start, settle bound, no re-request while switching), SelOK and SelPart, and not on the refuted
       HARB7. ipow's DSPs are cut (datapath not covered); gb/indep rows fail ArbRowsOK (B1). A boundary
       negative control (+43 ps passes, +44 ps fails) shows the row is evaluated exactly. gcd_hw has no
       such row (`notes/A-k3.md`, `notes/A-e9arbnet.md`).
   - **Not yet:** "proves it correct or prints a counterexample trace" as one tool. C's `vk` (one
     `verify.sh` entry point with counterexample traces) is running.

Note on sources: JOURNAL-B's 2026-10-29 `### progress` times (07:14 .. 12:50) run ahead of the UTC
commit times of the B commits that carry them (e.g. `af3be4d`, 08:35:30 UTC, carries the "12:50"
entry), so B's clock was probably not UTC. Times quoted from JOURNAL-B here are B's own; order by
commit, not by those times.

## How to check

```
formal/setup.sh                 # once: Lean 4.35.0 + Mathlib v4.35.0 (see Toolchain)
formal/check.sh --committed     # build all committed Formal/ modules + axiom audit
formal/check.sh                 # same over every file in Formal/ (incl. uncommitted)
formal/check.sh Formal/Core/Lut.lean ...   # single files (paths relative to formal/lean)
```
The audit runs `collectAxioms` on every declaration in a `Formal.*` module and
fails unless it uses only `propext`, `Classical.choice`, `Quot.sound`. Negative
controls (journal, 2026-10-27): a hidden `sorryAx` fails it, `native_decide`
fails it (`..._native.native_decide.ax_1_1`). Work in progress lives in
`formal/lean/Wip/` (not built, never claimed).

## Verdicts per track

| # | track | verdict | evidence (checks) | effort to finish | buys the project |
|---|---|---|---|---|---|
| 1 | Toolchain | **works, with a workaround** | `formal/setup.sh`, `check.sh` | done | — |
| 2 | Trace representation | **works (all three)**; ℕ-ps discrete chosen for gate/cell proofs, ℝ for analog and fidelity; discretisation proved sound | `Core/Trace/{Discrete,Event,Real,Bridge}.lean`, `Core/Discretize.lean`, `Core/Circuit.lean` | ternary discrete model: `Core/XSim.lean` (timed ternary simulation, sound for every behaviour in the bands, §4b); its soundness for continuous-time transport/inertial channels (probe XSound2, `Core/XSimChan*`, claimed 2026-10-29) | one substrate for B and C; their discrete proofs transfer to real time |
| 3 | Delay channels | pure, inertial, involution, corner-correlated: **all work** | `Core/Delay/{Pure,Inertial,Involution,InvolutionTransfer,InvolutionDMin,InvolutionTrace,InvolutionLoop,Corner,CornerDiff,CornerCode,SAF,GLSPass,GLSFid,GLSPass2}.lean`, `Core/Fidelity.lean` | Done: full IDM trace semantics with chained cancellation (InvolutionTrace), the involution OR loop (InvolutionLoop), the GLS sample-at-fire channel (SAF), what a passing GLS run implies (GLSPass, fixed for autoImplicit=false, 263 decls; GLSFid/GLSPass2 for research's per-pin fid GLS). Open: the real exp/log instance (Wip/InvTrace/ExpReal.lean, needs Mathlib Log oleans); the signal-level loop bridge (InvLoop2, done, not yet claimed); the GLS resolver's trace semantics (GLSResolve running). No time estimate in the journal | sound wire abstraction; exact bundling lemma; GLSPass/GLSPass2: a passing SAF/fid GLS run covers only SAF/fid silicon at the annotated delays (counterexamples inside the band); one run covers the band only for acyclic monotone nets with rising inputs; metastability as a digital effect (unbounded resolution near a unique critical runt) |
| 4 | Kleene LUT | **works**, incl. a hazard audit of all 43 cell LUTs generated from the RTL, and SI environment models (Env/EnvFast: bd_c2, latch, link W=1,2, merge) | `Core/{Kleene,Lut,LutTree,Ternary,TernaryChannels,Bridge,LutCells,LutAudit,Env}.lean`, `Core/EnvFast/*`, `tools-A/lut_extract.py` | environment models exist for bd_c2, latch, link W=1,2, merge, mux (Env/EnvFast); the remaining cells are not estimated. H_KLEENE_LUT (mid-rail select) is untested on silicon (board test in the fidelity table) | decidable per-cell hazard/settling check |
| 5 | C-element | **works** (B) | [L] `Cells/{CElemFn,CElemTiming,CElemCore,CElemInvolution,CTree,CTreeTimed,ConstraintsSel,CElemStrict,CElemStrict2,KleeneWin,KleenePess,LutFbBridge,LutFbBridge2}.lean`. A: `Core/{Ternary,XSim,LutAudit}` (bd_c2). Constraints data: `python3 formal/out/cell_constraints.validate.py` (137 rows, 40 exact, 0 errors; 6 planted faults → 6 errors) | X-window widths are unmeasured (board test XW-1, B-kleene-win). The Env closure for the network (cell ← Env1 ← neighbours) is done only for the 2-stage pipe. C-trees: tree latency is unchecked on routes. No time estimate in the journals | **INITs:** machine-checked (audit `71ee3e86` CElemFn CONFIRMED). **Own-feedback race:** exact on every variant only in the STRICT form, one tick (H_X_UNIFORM). With per-edge windows it gains +wq (`KleeneWin`). **C-element fork wait** E ≥ dwmax+dlmax−dlmin: sufficient (B) and necessary (audit `drop_env_latency_cex`); no rule checks it. **C's LutFb/FbFirst:** derived from B's physical model for every bd_c2 in OpsGen, bd_c3 and the mux joins. **Routes:** the RT_FB race is real on bare Muller rings (8 seeds, [C] C-10f) but not reached on the gcd_hw kernel. It fails at the rig's `uenv1` under the band on seeds 2 and 4. Two sources, different tools: C-10h (`aa5919c`, notes/C-10h-tcheck3.md, tcheck with per-pin arcs) seed 2 −117/−221, seed 4 −86/−243 ps (fastG/slowG); the audit's own model (REPORT.md at `83b1290`, row `1e7947a` tcheck routes, CONFIRMED) −114/−219 and −81/−201 ps banded. C-10f2 (rerun with the xMUX hop) is in progress. **Kleene:** the "definite output" results depend on H_KLEENE_LUT; the safety results do not (`KleenePess`) |
| 6 | Latch / link | **works** (B) | [L] `Cells/{Latch,Bundling,LinkHandshake,LinkTimed,LinkExact,PipeTimed,PipeTimedN,PipePerPin,PipeWitness,RulesKL,FifoFidelity,LibGapLatch,ForkData,WinFifo,WinFifoCausal,NoRevert,ZeroDelayRefine,Necessity5Link,Necessity5Flink}.lean` | The network half of the physical → zero-delay refinement, and multi-token (C-8x running). The FIFO channel hypotheses (Win + H_NO_REVERT) are grade B. No time estimate in the journals | **One exact contract per bd_link stage** (`LinkExact`; audit `69c99a9` CONFIRMED, exact inside `Wf`, which holds 3 timing conditions outside the conjunction). **Physical stage refines C's zero-delay Link iff its six rows hold**, one token (`ZeroDelayRefine.link_ref_iff`; B's self-audit: it is essentially `LinkExact.exact`). **SETUP is proved sufficient only** (audit `71ee3e86` "exact bundling inequality" OVERSTATED). PipeTimedN for every N. Its unit witness was degenerate (audit `c5c6d8b`); `PipeWitness` now gives non-unit and DACK=2 witnesses (not re-audited). **Rules:** tighten.py rule I misses the latch feedback-pin arc (the 200 ps guard covers it), and rule F misses an in-flight value (the guard does not cover it by construction). Both CONFIRMED by audit `71ee3e86`. **FIFO pin-order condition:** with feedback on A1 (up to ~+0.43 ns), it is hidden by the flat SDF |
| 7 | Arbiter (digital race) | **works**; exclusion is **not unconditionally provable**; it holds exactly inside derived race windows (B) | [L] `Cells/{ArbBinary,ArbKleene,ArbInvolution,ArbInvolution2,ArbHandover,ArbA0Fork,ArbCorners,ArbCornersPin,ArbOverlapRace,ArbOverlapPess,Necessity5Arb,TernarySound,TernaryExact,TernaryOnBits,OnNetlistArb,OnNetlistArbKappa,OnNetlistArbKappaExact,OnGcdArb,OnGcdArbA0,OnGcdArbKappa,OnGcdArbKappaTight,OnGcdArbKappaSrv,ConstraintsKappa,KappaCPPR}.lean` (the Kappa files need Mathlib). A: `Core/LutAudit`, `Core/Discretize` (`mutex_between`), `Core/Delay/InvolutionLoop` | **Open:** whether gcd_hw ever runs the bare (non-four-phase) race, which decides the gcd κ threshold between 0.0802 and 0.2166; H_SETTLED. **Board:** the 8% bd_arbcell overlap is NOT explained (needs the measured bitstream's pin map, not archived); κ is unmeasured. No time estimate in the journals | **Metastability comes out of the gate model** under involution channels: a critical same-sense gap, eternal oscillation, arbitrarily late resolution (`ArbInvolution`, A's `InvolutionLoop`). **Runt direction:** from same-sense moves, contrary to the bd_arb header. **Handover exclusion** is relative timing (RT1/RT2), not structural. `grant_skew_exact`: exclusion iff \|d6−d5\| ≤ L (transport model). **link_arb A0 fork:** exact κ thresholds for all 16 cases (`OnNetlistArbKappaExact.exact_X`, mostly irrational; answers audit `861de85` "exact" OVERSTATED, not re-audited); 16/16 safe at κ = 1/11. **gcd_hw:** see goal 2; the 0.0443 figure is the server-free form only. **Withdrawn numbers:** the ArbHeldTimed numeric instances (16 ps, 96 ps, 112 ps server) are corner-mix artefacts (audit `d420b53` OVERSTATED, `71ee3e86` rule-J row REFUTED). ArbCorners' rule-J and RT1b numbers assume q on A3; real routes put q on A5 in 3/4 seeds, which makes rule J 8 ps optimistic for client 1 (audit `c5c6d8b` OVERSTATED); guarded rule J is withdrawn (per-wire counterexample −118.5 ps). **Pessimistic LUTs** do not explain the 8% (`ArbOverlapPess`); under weak0 the detector itself could fire. **H_A0_FORK** is checked by rule J (arb_fork.py), which lacks per-pin site-pin delays (audit `71ee3e86` CONFIRMED) |
| 8 | Composition (Kahn, gcd_hw) | **safety works at circuit level; liveness reduced, not proved; rig first result only** (C, with B's bridges) | [L] `Net/{Handshake*,Muller*,MullerTimed,Kahn,GcdHwLive,Ops*,OpsGen,CapstoneWalk,CapstoneWitness,CapstoneWitness3,CapstoneRig,CapstoneLiveNdWalk,IpowCapMain}.lean`; B: `Cells/{LutFbBridge2Env,ZeroDelayRefine,ResetCapstone,RigSrc,RigSrcWitness,RigLaps,ContractBridge,IpowCells}.lean`. Network regeneration: `formal/tools/capnet` (byte-identical, audit `8965ea0`) | **Open:** H_NO_DEADLOCK' plus a liveness witness (C-8z2 running); physical → zero-delay, network half (C-8x running); the Env closure over all 175 links; every rig result (C-8s3 running; B: LapInv fails at a close); H_MAP as a wiring table; H_COMPUTE_FN; H_ARB_EXCL from a timed arbiter (not derivable as stated). No time estimate in the journals | **The gcd result:** `gcd_hw_circuit_safe3` + `gcd_hw_joint_witness3`: every out0 latch of the real 465-channel network is gcd a b, from 3 named hypotheses, non-vacuous (audits `f4696cc`, `299a16f`). **ipow:** the same at circuit level (`ipow_circuit_safe3`, audit CONFIRMED). **Do not cite:** `Capstone.gcd_hw_conditional` (no gcd content, audit `eecc6f7` OVERSTATED) or 8u's `gcd_hw_live` (likely vacuous, `start_never_closes`). **Negative result:** the hand-drawn gcd graph of 8b/8f deadlocks for every a ≠ 0 (8j). **Pipelines:** FIFO and live given per-link obligations, under H_SI, an isochronic fork and 3 liveness assumptions (audit `71ee3e86` CONFIRMED with caveats); gate-level bd_link chain for every n (9c) |
| 9 | Ring needs 3 stages | **works** (C) | [L] `Net/{Ring,RingFair,RingGen,RingReset,RingResetCert,RingTimed,RingTimedPure,RingCheck}.lean` | Exact cycle time, N > 5 from reset, other cells on the cycle, a gate-level environment. No time estimate in the journals | **Interleaving model (H_SI):** dead for N ≤ 2, one token live iff N ≥ 3 (`ring_three`), k tokens need N ≥ 2k+1 (`k_tokens`); fair window N(N−1)/2 (`RingFair`, answers audit `71ee3e86` doc row). `RingGen` states them over the generated bd_c2n netlist, so a flipped INIT breaks the headline (answers audit "real INITs" OVERSTATED (mild), not re-audited). **Reset:** bdc's reset leaves every ring empty (`bdc_closed_ring_empty`). From reset with one start token, N = 3..5 have exactly one token and no deadlock, and N = 1, 2 deadlock (`RingResetCert`). **Timed:** `timed_ring_three` (inertial and bounded pure FIFO); rise-to-rise ≥ N·dmin, tight; no runt on a persistent ring. **Bench finding:** tb_ring never varied the token count, and N=4 with two tokens is dead (audit CONFIRMED) |
| 10 | Verified timing checker | **works on real routes**: core proved sound, front end untrusted Python; the delay data are the limit (C) | [L] `Timing/{Semantics,Checker,CheckerFixedFn,Rules,Unroll,MaxNode,SharedPrefix,FbFirstRt,GrantFork*,RuntAck*,OblBridge}.lean`; [C] `formal/tools/tcheck/` (results per route in `tools/tcheck/results/`) | 10m (arc-by-arc OUTMUX cross-check against the auditor's xrc.py, tie-off false path, rerun all rows), 10f2 (RT_FB with the xMUX hop) and 10l2 (rule K) were lost last session and relaunched. Rule K fails 16-24 of 42 rows per route at every corner, undiagnosed. No time estimate in the journals | **Soundness:** `check_sound` CONFIRMED by the audit. "Per-node exact" holds only when the witness may choose the cell functions (`CheckerFixedFn`; answers audit `71ee3e86` OVERSTATED). **Rules:** E/A/J each have a proved counterexample. Rule A under E's band is sound iff tl ≤ 403 (answers audit `d420b53` off-by-one). **On 16 routes** (gcd_hw ×4, collatz/xorshift/ipow ×12): every disagreement is project-PASS/tcheck-FAIL, and none fails at a fixed prjxray point. Rule A and tcheck time GND/VCC tie-offs as data (audit `7f46f23` CONFIRMED). **Grant fork:** the runt never breaks the handshake on the 36 gcd_hw arbiters at 4 corners (`GrantFork*`, 10j); RuntAck 288/288 + 304/304 (audit `f4696cc` CONFIRMED, one corner per row). **OUTMUX hop:** the audit's PARTLY REFUTED row (`1e7947a`, OUTMUX missing) is against C-10g. The driver-side OUTMUX/xMUX hop (a6lut/a5lut/f7amux/f8mux/carry4 → xMUX) has been in tcheck's `extract.py` since C-10h (`_ic`, driver hop `dh`, extract.py:354-371; first in `29a164e`, 2026-10-27 06:18); audit row `f4696cc` (Contracts*/RuntAck) states "OUTMUX hop IS included (tcheck extract.py since C-10h)", and C's probe note `notes/C-10m-outmux.md` (2026-10-29, WIP) says the same. What is still open is 10m's arc-by-arc cross-check against the auditor's xrc.py and the rerun of every row, so JOURNAL-C's verdict block (which calls the hop missing) is out of date on the hop but right that the rows are provisional until 10m lands. "+490 ps" is a mean |
| 11 | Netlist import | **works for LUTs** (C, B); whole-design bitstream import being rebuilt | [L] `Gen/{Cells,Netlist,Proofs*}.lean` (36 cells/rtl modules, 163 theorems tying them to B's transcriptions), `Net/Import/*`, `Net/Fasm`, `Net/FasmLink`, B's `Cells/OnNetlist`. Run: `formal/tools/gen/gen.sh --check`, `formal/tools/import/import.sh --check`, `formal/tools/fasm2lean/check.sh` | 11f (FF/CARRY4/F7F8 and whole-design bits) was lost and relaunched. The doc's earlier estimate is 3-5 d to extend fasm2lean to gcd_hw (`out/gcd_hw_hypotheses.md` M5) | **Proofs about generated terms:** a flipped INIT breaks the build. The routed link and arbiter bits (4 seeds) compute the logical cells (audit `d420b53` CONFIRMED). The import's "Kleene spec" equality is same-INIT only (audit `d420b53` OVERSTATED wording). **Pin permutation** after P&R is real and moves delay by up to ~0.5 ns. Research's fasm2net on a gcd_hw route: 11619/11619 LUT functions equal, 3 harmless A6 ties (audit `4a44aef`). B's reset netlist was regenerated from the synthesized netlist (audit `f832d38` CONFIRMED) |
| 12 | Other tools | **bound-finders, not provers** (C): about 1 day per tool | [C] `formal/tools/{smt,async,zone}` (z3 BMC/k-induction/Spacer, Storm, TChecker by git clone) | The 12a/b/c thresholds used the fast/slow corner pair as rise/fall, so they are **suspect until 12d's one-corner rerun lands** (running). UPPAAL/Workcraft/PRISM downloads were blocked | Exact thresholds and witness traces for fixed integer delays in seconds; nothing for all delays. Find the bound fast, then prove it in Lean. 12c raised H_GRANT_FORK, which 10i/10j then measured and proved harmless on gcd_hw. A's Env/EnvFast is the kernel-checked SI analogue of Workcraft |
| 13 | Literature | **done** | `notes/A-lit-1.md`, `notes/A-lit-2.md`, `notes/A-lit-3.md` (2026-10-27: paper hosts unreachable from the sandbox, entries tagged abstract/snippet/memory) | — | positioning; nothing like this exists in Lean or any proof assistant (no mechanised involution channels, no verified STA, no async Lean work); κ≈0.1 per arc plausible from 7-series intra-die data (5–8%), 0.2 conservative |

### 1. Toolchain
Lean 4.35.0, Mathlib v4.35.0, lake project `formal/lean`. The sandbox proxy
blocks release.lean-lang.org, Reservoir, cache.mathlib.org and
lakecache.blob.core.windows.net, so Lean comes from the GitHub release zip and
Mathlib is built from source, only the modules imported (rule: never
`import Mathlib`). Most Core and Cells files need only core Lean. 4 cores /
15 GB: `slot.sh` allows 3 concurrent Lean processes.

### 2. Traces
Three representations did the same benchmark (B0 definitions, B1 fixed delay
composition, B2 bounded transport relation with composition and monotonicity,
B3 pulses, B4 inertial, B5 an AND gate in a conjunction circuit):
- **ℕ → Bool, 1 ps** (`Core/Trace/Discrete.lean`, 505 lines, core Lean, ~2 h):
  all of B0–B5. Non-Zeno for free; ties (simultaneous arrival) exact; `decide`
  does bounded model checks (256 inputs × 10 steps in ~10 s). Rounding to 1 ps
  costs ≤ 1 ps per arc. Weakness: sub-quantum runts are invisible; soundness
  w.r.t. real time needs a separation hypothesis (proved: `Core/Discretize.lean`, §2b).
- **Event lists** (`Core/Trace/Event.lean`, 625 lines, ℝ times): all of B0–B5;
  composition is `List.map`; but every n-input gate needs an event-list merge
  (200 lines for one 2-input gate); only finitely many transitions in total
  (no free-running ring).
- **ℝ → Bool** (`Core/Trace/Real.lean`, 511 lines, ~1.5 h): all of B0–B5,
  channel as a strictly increasing time warp (composition ~10 lines; the
  event-level reading is *proved* from it). B4 carries a named hypothesis
  `RealComplete`, since discharged from Mathlib (audit: this line was stale). Costs:
  every "first event" argument needs completeness; concrete waveforms are
  verbose (ε choices); nothing computes, so no `decide`. Finding: the
  order-preserving warp can never lose a pulse, which is unsound for runts
  (w ≤ hi−lo); the over-approximation `Window lo hi` (output at t equals
  input at some instant in [t−hi, t−lo]) is the sound default for safety.
Decision so far: ℕ-ps for gate and cell proofs (shards B and C chose it
independently), ℝ for analog loops and for the fidelity bridge from prjxray.

### 3. Delay channels
- **Bounded pure (transport) delay** (`Core/Delay/Pure.lean`): channel = FIFO
  retiming with delay in [lo, hi]. Series composition is *exactly* the sum
  band (`chan_comp_iff`); a pulse of width w comes out with width in
  w ± (hi−lo) and can vanish iff w ≤ hi−lo (`pulse_vanish_iff`); the
  bundling lemma `bundle_two_wires`: data stable at request arrival when
  ts + hi_data ≤ lo_req.
- **Inertial** (`Core/Delay/Inertial.lean`): filtering of pulses < ρ;
  output pulse width discontinuous at ρ; inertial channels are **not closed
  under composition** (`inertial_comp_1_2_not_inertialRD`); on runt-free
  inputs inertial = transport (`inertialRD_of_noShort`). Consequence: a GLS
  with inertial LUT paths (today's iverilog GLS) cannot show a LUT runt, so it
  is not evidence of runt-freedom; proofs must never use inertial filtering
  as a hypothesis.
- **Involution** (`Core/Delay/Involution.lean`, Függer/Najvirt/Nowak/Schmid):
  all hypotheses are fields of `InvolutionPair`. Consecutive outputs cancel
  iff t(n+1) − o(n) ≤ −δmin (`cancel_iff`); output pulse width is strictly
  increasing in input width and tends to 0 as the input width decreases to the
  threshold (`pulseWidth_small`: right-hand limit 0 at the threshold, continuity
  elsewhere not stated; the property that makes the model faithful to
  short-pulse filtration), in contrast to inertial (`inertial_gap`). Exp
  channel derived from a first-order RC (exp/log as hypotheses). **Transfer
  lemma, corrected and proved (`Core/Delay/InvolutionTransfer.lean`, answering the
  audit's OVERSTATED row).** `transfer_sep`: if consecutive inputs are at least S apart
  with S > D − δmin (D = max(δ∞↑, δ∞↓)), nothing cancels, each input transition gives
  exactly one output transition with delay in [min(δ↑, δ↓)(S − D), D], and the output
  is a `Pure.Chan` behaviour of the input with that band (`chan_sigOf`). The old
  wording (separation T0, band [δ(T0), δ∞)) was wrong in all three parts.
  `sep_threshold_sharp`: at 0 < S ≤ δ∞↑ − δmin evenly spaced inputs cancel, so the
  threshold is exact for symmetric channels. A concrete instance (`ratPair`,
  δ(T) = 2 − 1/(T+2)) shows the class is non-vacuous. `Core/Delay/InvolutionDMin.lean` removes the `IsDMin`
  hypothesis (δmin exists for every `InvolutionPair`, from its fields alone) and
  closes the asymmetric gap: S-separated inputs never cancel iff
  δ∞↑ − δmin < S and δ∞↓ − δmin ≤ S (`sep_threshold_exact`).
  **Trace semantics** (`Core/Delay/InvolutionTrace.lean`, 321 decls): the IDM channel as a
  map on transition lists (the non-forgetful algorithm as a fold), proved equal to a
  declarative survivors semantics (`channel_eq`); chained cancellation included, no
  transition cancels twice; agrees with `transfer_sep` above the separation threshold;
  a single pulse is cancelled iff width ≤ δ∞↑ − δmin, else the width law holds; exp
  channel over an abstract `ExpLog`: cancelled iff width ≤ τ ln 2. Not covered: the real
  exp/log instance, simultaneous transitions, the equality case at the threshold, η-noise.
  **The arbiter/C-element loop** (`Core/Delay/InvolutionLoop.lean`, 197 decls; B's OR loop
  with one involution channel, orbit level): a stationary pulse train exists and is unique;
  the critical runt s* = δ∞↑ − l is the only width in (0, δ∞↑) that never cancels
  (`crit_unique`); wider runts latch, narrower die; for every N and every time bound there
  are runts near s* that take more than N transitions / resolve later than the bound
  (unbounded resolution time, the digital form of metastability); for a symmetric channel
  s* > δ∞/2 strictly. So handover exclusion cannot be unconditional in this model. Not
  covered: every signal-level solution (InvLoop2's bridge to B's `loop_orb`, claimed 2026-10-29; formerly done but not
  yet claimed), rate law, multi-cell loops.
- **Corner correlation**: the independent band [fast-min, slow-max] is 3–4×
  wide (A-fidelity), so no matched-delay (bundling) condition is provable from
  independent bands; the shared-corner + local-scatter model that replaces them is §3b.

### 2b. Circuit layer and discretisation
- `Core/Circuit.lean`: the owner's layering, representation-independent:
  `Gate := Beh W σ → Prop`, `Circuit := List Gate`, `Sat`, composition is
  conjunction (`sat_compose`), refinement, hiding internal wires by
  projection, assume-guarantee chaining. `Core/Trace/Bridge.lean`: event lists
  denote exactly the right-continuous ℝ → Bool functions with finitely many
  changes (`range_toFun`), so the trace choice locks nothing in.
- `Core/Discretize.lean`: if a continuous behaviour satisfies a bounded
  transport channel and its input has no two transitions within one quantum
  q, its grid samples satisfy the discrete channel with bounds
  [⌊lo/q⌋, ⌈hi/q⌉] (`chan_sample`), and likewise for gates and circuits
  (`circuit_sample`, `transfer`); joint separation over a gate's inputs is
  needed. Shard B's C-element theorems therefore hold at grid points of every
  separated continuous behaviour (`loop_of_continuous`). Without separation a
  sub-quantum runt is invisible: grant exclusion can hold at every grid point
  and fail between them (`mutex_between`) -- exactly the arbiter tie.

### 3b. Corner correlation (`Core/Delay/Corner.lean`)
With one shared PVT corner c and affine nominal delays per arc plus local
scatter |ε| ≤ κ, a bundling condition at both corner endpoints is equivalent to
it at every corner (`bundle_ratio_affine_iff`); monotone nominal delays alone
are not enough (`monotone_not_enough`). The project's guardbands become exact
scatter limits: skew.py rule E is sound iff κ ≤ 383/1927 ≈ 19.9% (`ruleE_sound`,
`ruleE_tight`); rule A *with exact division Pd/5* iff κ ≤ 1/11 ≈ 9.1% (`ruleA_sound_rel`,
`ruleA_tight`); tighten.py's gate as coded (`max(int(0.2*t),200)`, SLACK = 0) is sound iff κ ≤ 25/276 ≈ 9.06% (`Core/Delay/CornerCode.lean`: `ruleA_code_sound`, `ruleA_code_tight`, worst case t_data 1004, t_req 1204, confirming the audit); with SLACK ≥ 1 (resize.sh's search) it is again κ ≤ 1/11. Assumed, not proved in Lean: Python's `int(0.2*t)` = ⌊t/5⌋ for 0 ≤ t < 2^50 (argument plus scans). **What the ring data say about κ, theorem by theorem** (this replaces two
paragraphs that contradicted each other: one said the per-path hypotheses were
refuted, the correction said they were not):
- `Corner.ring_kappa_lower` [L]: if two rings on one die both obey the per-path
  scatter model with a shared scale, then (rᵢ − rⱼ) ≤ κ(rᵢ + rⱼ) for their
  measured/predicted ratios rᵢ, rⱼ. `CornerDiff.ring_kappa_iff` [L]: that bound is
  attained, so (r_max − r_min)/(r_max + r_min) is the best lower bound on per-path κ
  that ratio data alone can give.
- Applied to the 7-link class of the 128 `ro_many` rings (ratios 0.773..1.470,
  cells/hw/README.md; `formal/tools-A/kappa/kappa.py repo` [C], no common offset in
  [0, 988] ps lowers it) this gives per-path κ ≥ 0.311 (`guard_refuted_by_7link_rings`).
  **But** those ratios are measured against SDFs written before
  `patches/nextpnr-xilinx-lut-perm-sink.patch` (shard C, `notes/C-10c-prjxdelay.md`),
  which charged 0–150 ps for permuted LUT pins where the routed hop is ~295 ps, on ~85%
  of chain hops. So the 0.311 bound measures that SDF bug, not silicon scatter, and does
  **not** refute the per-path hypotheses of `ruleE_sound`/`ruleA_sound_rel` (correction
  of 2026-10-27 ~07:00, also at the head of `notes/A-kappa.md`). Against corrected
  predictions, C-10c finds measured/predicted 1.067 (current SDF) / 0.989 (prjxray) over
  47 comparable rings; the audit (`55fde94`, OVERSTATED) notes that the 47 are
  re-routed predictions and only ONE ring (ro_top ring 0, 6293 ps) was measured on
  silicon for this comparison, and that both numbers rest on one global scale fitted to
  the 512-ring median (unscaled 0.939/0.605). So these are not a
  measurement of κ either.
- `CornerDiff` [L]: rules E and A compare two paths, so what they need is a bound κd on
  the scatter of a path *difference*. Both rules are sound under κd with the same limits
  (`ruleE_sound_diff`, `ruleA_sound_diff`, both tight); per-path κ implies κd but not
  conversely (`diff_not_imp_scat_strong`, the auditor's non-degenerate witness: a guarded pair with κd = 0 that violates per-path Scat K at every positive scale; the older `diff_not_imp_scat` witness is a scale artefact, `diff_not_imp_scat_degenerate`), so
  ring data (one absolute path per ring) cannot decide κd either way.
- Net: κ (per path) and κd are **unmeasured** on the current toolchain; whether rules E
  and A are safe on silicon is open; the per-ring data and bitstreams needed to redo the
  ring analysis are not in the tree.
- **κ estimator** (`formal/tools-A/kappa/kappa.py`, `notes/A-kappa.md`;
  `python3 kappa.py selftest`, `python3 kappa.py repo`) [C]: computes the pair bound and
  the differential κ from any per-route two-path data. Proposed board experiment: a ring
  with a shared body splitting into two tails rejoined at a scan-selected LUT mux (the
  shared body, offset included, cancels), ≥ 64 pairs per class, 4 seeds, two
  temperatures; or, cheaper, commit the `ro_many` per-ring raw logs (`kappa.py rawlogs`
  parses them).

### 4. Kleene LUT
- `Core/Kleene.lean`, `Core/Lut.lean`: shared K3 and LUT API (INIT as
  `BitVec (2^k)`, I0 = LSB, LUT6_2 O5/O6). Kleene eval equals the INIT-table
  definition for every k; monotone; single-input change never hazardous
  (`no_static_hazard_single`); two-input change can be — on the C-element itself,
  a b 01→10 with q=0 gives X (`Init.bd_c2_two_change_hazard`). 19 cell INIT constants (23 `*_eval` theorems)
  transcribed with `*_eval` theorems that confirm the RTL header comments.
- `Core/LutTree.lean` (gate fidelity): the LUT as a pass-transistor mux tree.
  Mux-tree Kleene eval = INIT-table semantics for every k, INIT, input
  (`evalTree_eq_tableEval`); tree order irrelevant; with arbitrary per-mux
  delays a single-input change with equal endpoint values never glitches
  (`sic_glitch_free`), under named hypotheses `H_mux_kleene`, `H_sram`.
- `Core/Ternary.lean` + `Core/TernaryChannels.lean`: Eichelberger ternary
  simulation is sound for discrete-time causal behaviours (`Causal`, which
  includes GMW, `gmw_causal`, and discrete transport with lower bound ≥ 1
  step, `causal_of_transport`), and, in continuous time, for every network
  whose nodes are zero-delay gates followed by `Core/Delay` transport
  (`Chan`) or inertial (`InertialRD`/`BoundedInertial`) channels with a
  positive lower delay bound (`ternary_noGlitch_channels`). Settling
  (algorithm B) holds within `|ν|·D` for both channel kinds, `D` the largest
  upper delay bound (`ternary_settle_channels`; for inertial channels via
  `SettlesWithin`, not `Stale`). A zero lower delay bound makes it unsound
  (`zero_delay_chan_unsound`, `zero_delay_inertial_unsound`); grid samples
  of continuous behaviours are `Causal` only under separation
  (`causal_of_sample`; counterexample `sample_not_causal`). bd_c2's every
  single-input flip settles with no static hazard. This is a decidable,
  delay-independent per-cell check.

### 4b. Whole-cell and whole-design checks (A, phases 1–2)
- **Substrate** (`Core/Substrate.lean`, `Substrate/{Chan,CornerNat,Real,Legacy}.lean`;
  guide `notes/A-substrate.md`): the one API for B and C. Delay relation
  `Win lo hi` (fixed ⊂ transport ⊂ `WinR` ⊂ `Win`; GLS SAF ⊂ `WinR 1 d`), composes
  with summed bounds; the corner model in ℕ ps with an endpoint check sound for
  every real corner and real delay within κ (`endpoints_sound_real`).
- **Timed ternary simulation** (`Core/XSim.lean`): sound for every behaviour in
  the bands, feedback allowed; `decide +kernel` verdicts are theorems (130 gates
  × 200 steps in 180 s).
- **SI environment model** (`Core/Env.lean`): bd_c2, the bd_latch pair and
  bd_link (1-bit) are speed-independent under rules H, L and isoEn, each proved
  necessary. Limit: ~1000 states per kernel certificate; the bit-packed checker
  `Core/EnvFast` extends this to link W=1,2, merge and mux (row 4; Findings, bd_mux).
- **xaudit** (`lake build xaudit`; `formal/tools-A/xaudit/run_all.sh`): a
  compiled whole-design X/hazard audit whose engine is proved equal to XSim and
  to Ternary A/B; the JSON parser and the compiler are trusted, one verdict is
  re-checked by the kernel. On a hand-flattened 3-stage pipeline: clean at one
  corner, hold-violation control flagged, and a C-element race flagged when
  the cell's own feedback is slower than a neighbour's response (an obligation
  not found among tighten.py's rules). On gcd_hw: next bullet.
- **xaudit on the real routed gcd_hw R5** (`notes/A-xaudit-gcd.md`, 4 seeds,
  prjxray per-arc bands via the research branch's `xray_delay.py`; 47,894
  wires, 4,599 storage nodes): with bands ≤ 2% wide it **certifies a whole gcd
  transaction** (a=7, b=0) for every delay in band and every power-up state, and
  the negative control is flagged. At prjxray's one-corner widths (~17%) the
  window domain loses precision after 4–11 ns: imprecision, not a race (520
  concrete samples correct; no static own-feedback candidate). With fast and
  slow corners mixed per element, 4–10 own-feedback race candidates per seed;
  one reproduced concretely (a 9 ps runt in `ucontrol_merge4.uarb1.ua2`, seed d).
  The C-element feedback assumption holds at each corner and fails once corners
  mix, so it rests on the shared-corner hypothesis and on κ.
- **gcd_hw control at real prjxray widths** (`Core/XAudit/Events4.lean`,
  `notes/A-events4.md`; seed d only; analysis in Python over a recogniser shared
  with `lake exe xevents4`, rule arithmetic proved, end-to-end `Beh4.safe` still
  open): at one corner, 402/405 C-element stages clean for all time and all
  select sequences (Back margin ≥ 961 ps slow / 434 ps fast). With fast and slow
  mixed per element: 331/405 clean; the two own-feedback races fbrace found, plus
  guarded-ack races (arbiter A_b to −1278 ps, umux3/umux4 −51..−187 ps) and
  a FASTFALL delay-line finding that turned out to be a model artefact
  (Events5: the shared chain after two taps meet was double-counted; corrected,
  64 → 1/4/0/0 lines per seed). All of these need corner mixing, i.e. local
  scatter, which is unmeasured. **Events5** (all 4 seeds, strict margins,
  `Beh4.safe` proved, so the verdict is a theorem about the model; the netlist
  link `design_beh4` and the guard timing are still open): slow and fast corners
  402/405 on every seed (3 = the cascaded arbiter, outside the domain); at
  skew.py's own guardband (one die, 0.668–1.0 × slow max) four items fail:
  three arbiter re-arm entries on seed d (−52, −26, −9 ps) and the rig's `uenv1`
  (−19 ps, seed 5). The real FASTFALL residual is rule F's missing in-flight term
  at the head of `bd_delay_gated` (g[0] is a plain buffer): −365/−726 ps on
  mixed dies, not reached at the rig's ~260 ns source low phase.
  **Events6** (`lake exe xevents5`): the netlist link `design_beh4` is proved
  (per-pin, no `H_ATOMIC_LUT`), so the checker's verdict on the parsed routed
  netlist is a theorem, but for gcd_hw it is still conditional on 45 residual
  obligations per seed (branch labels through merges, the 3-way merge, the
  cascaded arbiter, and 6 guarded acks arriving through delay lines whose
  obligation is expected to be false until the domain gets a guarded
  multi-copy pin kind). Superseded by **Events8** (`Core/XAudit/Events8Beh.design_verdict8`,
  goal 2 above): the checker prints CLEAN at the slow and fast corners on all 4 seeds, conditional on SatPin,
  constant wires and reset, H_ARB (HARB7), SelOK, SelPart and HDsub. **This verifies no real gcd_hw run:
  HARB7 is false on real uncontested bd_arbiter runs (`Events8Arb.unc_not_harb`), and with the corrected
  core no row is CLEAN (54 structural residuals per row). Audit `e91d41ff`/`eb346fb` OVERSTATED rows, answered here.** (audit `eb346fb`
  CONFIRMED as conditional, Lean certificates UNVERIFIED; the gb ENTRY claim OVERSTATED,
  2 of 3 real after E8Mux added the O5/MUXF OUTMUX hop, [C], `notes/A-e8mux.md`).
- **Per-pin race checker** (`lake exe xevents2pin`, `Events2Pin*.lean`): sound
  without the all-pins-at-one-instant assumption (`H_ATOMIC_LUT`); with prjxray
  per-physical-pin bands, per-pin skew costs 11–79 ps of margin. One corner: no
  failing pin on ring3/pipe3/gcd_hw (4 seeds). Mixed corners: 1–4 pins per seed
  on ring3/pipe3, 6–8 on gcd_hw. Site-pin differences (−468..+308 ps) make any
  SDF-fed race check unreliable.
- **Event-count domain** (`Core/XAudit/Events*.lean`, `Events2*.lean`;
  `lake exe xevents`): per-wire transition counts with min-plus timing (timed
  marked graph) over the behaviour's own monotone warps. Closed and open
  Muller networks of real-INIT n-input C-elements with delay chains stay
  binary for all time under explicit decidable obligations (`Back`/`Race`:
  own feedback hi ≤ the lo-sum of the loop back through each neighbour); ring3
  and pipe3 period bounds [135, 171] steps, both attained, via exact cycle-ratio
  certificates. Finding: at an open boundary the race margin is only the port
  route's lo plus the environment's response minus feedback hi (30 ps + env on
  illustrative bands, vs 930 ps inside). Choice (mux/steer) and bundling inside
  loops are the remaining steps toward gcd_hw.

### 13. Literature
`notes/A-lit-1.md` (async/SI/DI verification, involution model,
metastability-containing logic, arbiter theory; 40 sources) and
`notes/A-lit-2.md` (proof-assistant hardware work). Closest prior art:
ACL2 link-joint self-timed proofs (Chau/Hunt/Kaufmann/Roncken/Sutherland);
Graphiti (Lean 4, Dynamatic dataflow rewrites, ASPLOS'26) as the token-level
target; Lutsig (HOL4, 7-series LUT/CARRY4, synchronous). Nobody has
mechanised LUT-built async cells, bundled-data timing together with gate
function, or a gate-level arbiter.

## Fidelity per primitive

### Against the research GLS at 6524fa3 (probe Fid3, 2026-10-29; iverilog/Float experiments, not theorems; notes/A-fid3.md, run: `formal/tools-A/glsdiff3/run-1029/run.sh`)

Grades: A = measured on this part or fixed by a vendor document; B = documented structure or faithful physical model, unmeasured; C = unsourced assumption or known wrong.

| primitive | formal model (Lean) | research GLS (6524fa3, `GLS_MODEL=fid`) | silicon: what is known (source) | grade formal / GLS | test that would settle it |
|---|---|---|---|---|---|
| **LUT function and X** | Kleene mux tree from INIT, A6 at the root (`Core/LutTree`, `Lut.keval = kevalSpec`); hypothesis `H_mux_kleene` (a mid-rail select with equal data passes the data) | `?:` mux tree on the delayed pins (leaf-first; the order does not change values). Equal to Lean on 43,767/43,767 vectors | Structure: LUT6 = two LUT5 + A6 mux (UG474). Single-input change does not glitch (P. Alfke, comp.arch.fpga, informal, not a datasheet). Mid-rail select behaviour: no source | B / B (same model) | board: masked-pin toggle into a fabric edge counter (A-fidelity); SPICE of a pass-gate mux leaf |
| **LUT per-pin arcs** | per-pin bounded transport `[lo, hi]` then the zero-time function (`Events2Pin`, `Pure.Chan`) | per-pin transport, one SDF point per pin (`FID_LUT6`), 1 ps output sampler; `+FID_LEVEL_PS` for internal skew (default 0) | prjxray LUT arcs are flat per output; pin dependence is in site-pin delays (A-fidelity). Internal tree skew: unknown | B / B. GLS = one point of Lean's band (60/60 + 60/60) | per-pin delay ring (A-fidelity) |
| **LUT glitch / runt** | transport passes every pulse; inertial and involution channels are available (`Delay/{Inertial,Involution}`); which one is silicon is a hypothesis | every pulse ≥ 1 ps passes (transport) | no 7-series LUT pulse-rejection figure found (research f3_model.md, A-fidelity: estimated 15-50 ps from R·C, not measured) | B / B: transport is the hazard-pessimistic side; it is optimistic only for a proof that needs a narrow pulse to die | pulse-shrink experiment: XOR with a k-LUT-delayed copy into N hops and a toggle counter (A-fidelity R1) |
| **routing, buffered pips** | `Fidelity.DelayBound` per sink arc [FAST_MIN, SLOW_MAX]; Elmore `rcBound` with κ; shared corner + scatter \|ε\| ≤ κ (`Corner.lean`) | `fid/xray_delay.py`: prjxray `timing.py` RC tree (Buffer per buffered pip, Elmore over the downstream subtree, site-pin delays, fanout C). Transport ICBUF per sink. One SDF column (or `band` = one shared lerp) per run | all 3737 INT_L pips are `is_pass_transistor = 0` (A-fidelity scan of prjxray-db). prjxray's model is ±1.5% from Vivado (not silicon). Board: n=128 ring periods fall inside the summed bands (FEASIBILITY) | B / B for the band. GLS **scatter is unbounded Gaussian**, outside every κ-bounded theorem (FOR-RESEARCH §8, unchanged) | already partly done (ring periods); per-wire scatter from more rings |
| **routing, pass-transistor pips** | zero-delay alias (`H_alias`) | `PassTransistor(R)` in the RC tree (the only ones are fixed CLB site-pin aliases with `delay=null`, `res=0`) | prjxray-db: pass-transistor pips exist only as fixed tile-wire→site-pin aliases on this part (A-fidelity R2) | B / B (agree) | not separately observable |
| **MUXF7/F8** | `Core/Prims/Muxf` (PrimsComb): Kleene mux under `H_MUXF_PASS`, constant transport per arc with prjxray per-corner numbers (`XrayData`); select change with equal data and any single-input change with unchanged output glitch-free for any delays; select-rises-while-deselected-input-changes glitch forced for every admissible delay pair (≥ 16 ps fast / 22 ps slow) | `FID_MUX2`: per-pin transport, Kleene `?:` | structure per UG474; S-toggle with equal data: no source | B / B | board: D0 = D1 = 1, toggle S at ring rate, count OUT falls (expect 0) (A-fidelity M1) |
| **CARRY4** | `Core/Prims/Carry` (PrimsComb): MUXCY+XORCY with the PRECYINIT mux, Kleene, band per arc; adder agreement (512 cases), no single-pin hazard on any output, a two-pin (S0, DI0) hazard on CO0 whose order prjxray's bands allow at both corners; equal to C's Gen model except carry-in CI OR CYINIT vs the PRECYINIT mux (equal under every decoded configuration) | **per-(pin, output) transport, then the same equations** (78de9c2). E1: 60/60 exact on multi-pin random traces | MUXCY/XORCY structure (UG474); arcs per (pin, site output) from prjxray SDF. Note CARRY4 is read-once (each pin has one path to each output), so per-(pin, output) transport is what a transport cascade gives; the SDF arcs need not be additive (they end at site pins) | B / B (now agree; was GLS C) | carry-chain TDC style: launch an edge into CIN/S, sample the CO taps (standard TDC papers) |
| **FF (FDRE/FDSE) function and X** | `Core/Prims/{SeqNext,SeqFlop}` (PrimsSeq): Kleene next state (R beats CE), power-up INIT, CLR priority; `SeqGls`: research's SLICE_FFX has a violation-free run with Q=0 where every Kleene run has Q=X. Census: gcd_hw's kernel has no flops (FDRE/FDSE only in the rig, `bd_flink` in bd_mlink.v, and arb_mtbf) | `if (SR)` / `if (CE)` (default), `sr === 1` / `if (ce)` (fid): **x on SR or CE is read as 0** | an x (mid-rail or unknown) SR/CE gives an unknown next state; nothing documents a definite value | B / **C** (GLS wrong, optimistic: hides X). Fix tested: `patch/prims_x.diff` | `run-1029/run.sh` E7: F1, F2 must print x |
| **FF timing (CK→Q, setup/hold, aperture, min pulse width)** | `Core/Prims/{SeqFlop,SeqXray,SeqSync}` (PrimsSeq): each input read over its own setup/hold (recovery/removal) window, X if not constant there; Q old until cqLo, new after cqHi; on a violation X up to cqHi+res then one definite unspecified value (res = named `H_FF_RESOLVE`, no MTBF); two-flop synchronizer output definite. prjxray-db ships no fast-corner setup/hold (`H_WINDOW_SLOW_ONLY`; fast CK→Q min 112 ps vs slow-only hold 241 ps, `fast_hold_mismatch`). Not covered: clock runts / min pulse width | transport CK→Q; SDF SETUPHOLD aperture (negative SETUPHOLDs read since 666ea57) with an old/new choice and t_r = TAU_FF·ln(ap/2\|δ\|), TAU_FF = 75 ps; CK min pulse width TMPW 70 ± 20 ps | SETUPHOLD per pin in prjxray-db (Vivado numbers). Flop τ: Beer et al. ASYNC 2010, 57/51/73 ps at 130/90/65 nm; no 28 nm figure. Min pulse width: none found in prjxray-db (research could not read DS187) | B (timing as hypotheses) / C (TAU_FF, TMPW assumed) | hw/arb_mtbf-style synchroniser sweep (MMCM fine phase shift) for TAU_FF; CK runt sweep for TMPW |
| **latch (SLICE_LATX, LDCE/LDPE)** | `Core/Prims/SeqLatch` (PrimsSeq): transparency, hold, X containment; not covered: latch G/GE pins, X on the gate | per-pin transport (78de9c2); **X pessimistic** (closed + CE = x → x; CLR = x → x even when the result is SRVAL); no metastability at gate close (stated) | UG474: latch-mode storage element, gate on CK, enable CE, async SR. **No design uses LDCE/LDPE**: `bd_latch` stores on LUTs (cells/rtl/bd_latch.v header) | B / C (pessimistic, harmless today). Fix tested: `patch/prims_x.diff` | E7: L1-L3 must print 0 |
| **LUT state loop: C-element, LUT latch, arbiter q** (metastability) | B: `ArbInvolution` (`stF_runt`), `CElemInvolution.orb`; proved: a critical runt s* exists in (δ∞ − δ(0), δ∞) (`arb_eternal`). A: `Core/Delay/InvolutionLoop` (§3) proves it unique, s* = δ∞↑ − l, s* > δ∞/2 for a symmetric channel, with unbounded resolution time near it (orbit level). Float evaluation (not a theorem): s* = 0.50-0.58·TLOOP (A-fid3 §3 item 3's skew direction is wrong in this model, JOURNAL 08:26, correction pending), deterministic either side; near s* the loop **circulates a pulse train** and resolves with TAU_eff ≈ 1.2-17·TLOOP | `FID_RESOLVE` on self-loop LUTs (gen.py): runt p < TLOOP decided at **TLOOP − WIN/2** (349 of 424 ps), N(0, WIN/4) noise, t_r = TAU·ln(WIN/2\|δ\|), TAU = WIN = 150 ps (assumption). During resolution the node **holds a clean value** (default) or x (`+META_X=1`); one runt reaches fanout, echoes ignored. Multi-cell loops get no resolver | none measured. Without the resolver (`+META_OFF=1`) the GLS's own transport loop circulates the runt forever with period TLOOP (E4: Q 1124↑ 1473↓ 1548↑ 1897↓ …), i.e. the echo is physical and the "rejection" is a modelling choice | B (Lean channel family, unmeasured) / **C** (centre has no derivation; TAU optimistic under involution; clean hold hides the pulse train) | **hw/arb_mtbf**: sweep the r1→r2 skew (MMCM fine phase or IDELAYE2 taps) and record P(r1 wins): the 50% point is at TLOOP/2 (involution) or TLOOP − WIN/2 (GLS), 137 ps apart at TLOOP 424; count q toggles per race with a ripple counter (train vs single runt); resolution-time histogram for TAU |
| **BUFGCTRL** | not modelled (clock only in rigs) | transport I0→O (fid) | no BUFG min pulse width in prjxray-db | — / B | — |
| **DSP48E1** | `Core/Prims/{Dsp,DspData,DspTimed}` (PrimsDSP): ipow's combinational mode only; function exact, coarse X sound, one lumped settle band (H_DSP_LUMPED) | combinational and registered modes; still iverilog module paths (SAF) | ipow uses 6 (two multiplies, three cascaded DSP48E1 each, all pipeline registers 0; `notes/A-prims-dsp.md`); gcd_hw uses none | — / C (SAF) | per-unit exhaustive/random vectors on the routed ipow DSP cone; DSP delay vs the matched delay lines (B-ipow-cells) |

### Earlier table (2026-10-27; superseded by the 6524fa3 table above, kept for history)

(From `notes/A-fidelity.md`, `A-lut-tree.md`, `A-kleene-lut.md`. Where the two tables
differ, the one above is current.)

| primitive | model in Lean | fidelity | hypothesis | how to test |
|---|---|---|---|---|
| LUT function | Kleene mux tree from INIT | logic exact (INIT = function, proved for all k) | `H_mux_kleene`: a mid-rail select with equal data inputs passes the data, no charge-sharing dip; `H_sram` | board: masked-pin toggle into a fabric edge counter; SPICE |
| LUT timing | per-mux delays, arbitrary | order of tree (A6 at root per UG474) only affects delays | prjxray LUT arcs are flat; pin dependence is in site-pin delays (A1 slow ≤ 0.516 ns) | per-pin delay ring |
| routing pip | bounded transport [fast-min, slow-max] per sink arc | all INT_L pips in prjxray zynq7 are buffered; RC tree responds monotonically (no glitch) | band from prjxray via Elmore per sink arc (not summed per pip); shared corner + local scatter (pending) | n=128 ring periods inside summed bands |
| MUXF7/F8, CARRY4 | settle within hi (superseded: `Core/Prims/{Muxf,Carry}`, table above) | "only in datapath cones, never in control" (unchecked; gcd_hw has 857 MUXF7, 343 MUXF8, 59 CARRY4, JOURNAL 2026-10-29 08:11) | "anything before hi" | — |
| FF (FDRE) | — (superseded: `Core/Prims/Seq*`, table above) | PrimsSeq census: FDRE/FDSE only in the rig, `bd_flink` (bd_mlink.v, not emitted by bdc) and arb_mtbf; none in gcd_hw's kernel | standard setup/hold (slow corner only in prjxray) | — |
| delay model in the GLS at research 5d535d7 (superseded: see the 6524fa3 table above; CARRY4/latch early edge FIXED under fid in 78de9c2) | default: sample-at-fire (SAF) on every specify path; `GLS_MODEL=fid`: per-pin transport for LUT and MUXF7/8 (equal to Lean's per-pin transport on 60/60 + 60/60 traces), still SAF for CARRY4, latch, DSP, BUFG | default disagrees with silicon (early edges, swallows runts); fid fixes LUT/MUXF but CARRY4 still propagates edges early (23 ps after the cause through a 223 ps arc) | — | FOR-RESEARCH §8 |

Note: prjxray-db's `timings/*.sdf` triples are (FAST)(SLOW), not rise/fall;
a standard SDF reader misreads them (A-fidelity).

## Findings for the main project (to verify, not confirmed defects)
- **C-element own-feedback obligation, unchecked by the flow** (two shards,
  independently). A's `xaudit` flags C-element glitches in a 3-stage pipe
  when a cell's own feedback is slower than a neighbour's response; C (track 8
  Muller timed, `H_FB_BEFORE_INPUT` / `FbBound`: feedback hi < lo-sum of each
  neighbour loop, strict) derives the same bound and finds it
  placement-dependent: the shortest LUT-to-LUT route of 11b fails it, the
  seed-1 route passes. No tighten.py rule checks it. On routes (C-10f, [C] with
  per-instance Lean certificates `Timing/RtFb*`): real on bare Muller rings (slowE
  4-12 of 64 stages fail on all 8 seeds, worst −116..−231 ps; feedback on pins 1-3;
  C-10f2's rerun with the xMUX hop gives 1-8 fails per seed, WIP) but not reached on
  the shipped gcd_hw kernel (4 seeds, worst slowE +234 ps); the rig's `urig.uenv1`
  fails it under the band on seeds 2 and 4 (numbers in track row 5). B (PinAssign):
  the router puts C-element/latch feedback on the slowest site pin in 12/36 fixture
  pins and 24/64 muller64 stages.
- **The research GLS's LUT delay can propagate an edge early**
  (`notes/A-gls-compare.md`, `tools-A/gls-compare/run_all.sh`). iverilog
  specify paths on `SLICE_LUTX` behave as "sample at fire": a change at t
  schedules an update at t+d that copies the function value when it fires,
  with no cancellation (fits 140/140 random traces; inertial 48, transport 4).
  An edge following an earlier change within d arrives early (reproduced: a
  rise at 1130 ps seen at 1244 ps through a 124 ps arc; down to 4 ps in the
  probe). GLS bundled-data margins can therefore be optimistic for glitchy
  data cones. Not measured: how often in a routed design. The GLS's annotated
  and baked builds also treat wire pulses differently (LUT-like vs transport).
- X-propagation of the GLS LUT/MUXF7 models equals Core `kevalSpec` on all
  43,767 vectors tested; bd_c2 single-input flips clean in both. bd_c2 a,b
  01→10 at q=0: Lean says hazard (X); the GLS shows a sharp skew threshold
  with a clean flip, and endless oscillation with a transport feedback wire.
- The research GLS's `SLICE_LUTX` builds the LUT mux tree with A6 at the
  leaves; the silicon has A6 at the root (UG474). Harmless for logic values,
  differs in timing (A-lut-tree).
- **bd_arb header: "a tie is resolved deterministically" is not true for a
  same-sense tie.** Both requests rising together from idle is a static hazard
  on q for either held q (`LutAudit.arb_tie_from_idle_hazard`; shard B 7a
  reached the same conclusion independently in timed form). Same-sense
  near-ties should be in the MTBF experiment (cells/verify/MTBF.md).
- **The losing grant can pulse without metastability**
  (`LutAudit.arb_grant_near_tie_runt`): q rising while r2 rises, with routing
  skew between the q branches. A2 = C(g2, A0) absorbs it, but bdc/emit.py's
  `won = g2 | ack` drives `index` directly, so index sees the pulse. Now checked
  on gcd_hw: shard C's 10i finds the grant-fork runt live on 32/40 routed bd_arbiter
  instances (up to ~1.2 ns at SLOW_MAX), and 10j proves it never breaks the handshake
  on the 36 routed gcd_hw arbiters at 4 corners (`Timing/GrantFork*`, per-instance
  kernel verdicts, under H_CAUSAL_PATH and H_FF_DRAINED); RuntAck checks 288/288 ack
  and 304/304 index rows (audit `f4696cc` CONFIRMED; one corner per row, no band;
  passes depend on server latency and H_FF_DRAINED; routes not the board bitstreams).
- **bd_mux: three obligations the RTL header does not state**
  (`EnvFast/Mux*.lean`, notes/A-envfast-2.md): return-to-zero (the previous
  token's x_ack/y_ack fall before the next z_ack rises; shard B's H_MUX_RTZ,
  found independently); select held until ctl_req's fall has passed the join
  LUT uj1 (the header says until ctl_ack falls); fork conditions on the z_ack
  and ctl_req branches. Each is shown necessary. bd_merge with its data mux is
  sound under exclusivity and the matched delay; an earlier `selFast`
  obligation is withdrawn (it only bites while the output window is closed).
- Shard B (7b): the bd_arbiter A0 hold relies on a fork ordering H_A0_FORK
  (A0's fall must reach ua2 before A0 → ustate → q → ugrant → g2 does). It IS
  checked by the flow's rule J (`cells/verify/arb_fork.py`; B corrected its earlier
  "unchecked"); 7g proves rule J's condition exact in the box version, and rule J is
  optimistic only by ignoring per-pin site-pin delays (up to ~0.5 ns, not in
  nextpnr's SDF; audit `71ee3e86` CONFIRMED). B proposes rule J'
  (`notes/B-arb-a0fork.md`).
