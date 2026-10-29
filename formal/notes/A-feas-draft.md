# A-feas-draft: refreshed FEASIBILITY rows (tracks 5-12) and goal status, for the lead to paste

Probe FeasDraft (shard A), session 2026-10-29. Writing only, no Lean run.

STATUS: done. Draft for review; nothing here is a claim of its own.

Read (working tree at `4800b13`): `formal/PROGRAM.md`, `formal/FEASIBILITY.md`, `JOURNAL-B.md`
(verdicts, audit response, session 2026-10-29 07:14..12:50), `JOURNAL-C.md` (verdicts, sessions
2026-10-27 and 2026-10-29 07:22..08:06), `JOURNAL.md` (session 2026-10-29 07:12..08:35),
`out/gcd_hw_hypotheses.md`, the audit `REPORT.md` (scratchpad copy). I read the Lean signature
of four theorems (`gcd_hw_circuit_safe3`, `gcd_hw_live_final`, `gcd_hw_safe_phys_links` and
`gcd_hw_circuit_safe''` via the hypotheses doc) to get their hypotheses right. I checked
everything else against the journals only.

Conventions used below:
- **[L]**: checked in Lean, as the owning shard's journal reports it (file, theorem). The run command
  is `formal/check.sh <path relative to formal/lean>`, or `formal/check.sh --committed` for all files.
  Mathlib-closure files need Mathlib built first.
- **[C]**: computed (Python, iverilog, data extraction). The theorem is not about this data
  unless a row says so.
- **[A]**: argued in prose.
- **audit `<commit>` "<claim>" VERDICT** cites a row of `origin/claude/audit:audit/REPORT.md`. The
  report has no row numbers, so rows are named by commit and claim. Row numbers quoted in the
  journals, such as "row 18", are B's or C's own numbering.
- "(not re-audited)" marks a fix a shard made in answer to an audit row that the audit has not
  yet re-checked.

Note on B's timestamps: JOURNAL-B's 2026-10-29 entries run to "progress 12:50", but the B commit
that carries them is `af3be4d` at 08:35:30 UTC, and `date -u` here read 08:36. B's progress
times are probably not UTC. The lead should check this before quoting B's times.

---

## 1. Status against the owner's three goals (draft, replaces FEASIBILITY.md:24-55)

### Status against the owner's three goals (2026-10-29 ~08:40 UTC)

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
       The value of κ is unmeasured.
   - **From shard B:**
     - `KleeneWin`: each binary edge gets its own X window, and every race gains c + a exactly. This
       drops the assumption H_X_UNIFORM;
     - `KleenePess`: a pessimistic bracket strict ≤ model ≤ H_KLEENE_LUT. Every safety and exclusion
       result transfers to it. Every result that needs a definite output (hold, restore, reset)
       needs pass(v) instead. This answers audit `abe7d25` KleeneBox: "H_KLEENE_LUT is the
       hazard-free extension (optimistic)".
   - **Probes done, waiting for the lead's check.sh and review (NOT claimed, in no journal yet):**
     - PrimsSeq: FDRE/FDSE/FDCE/FDPE and LDCE/LDPE, 6 files `Core/Prims/Seq*`;
     - PrimsDSP: DSP48E1 as ipow uses it, `Core/Prims/{Dsp,DspData,DspTimed}`;
     - InvLoop2: the signal-level bridge to B's `loop_orb`.
   - **Open:**
     - RAMB18E1 is not modelled (bd_mem's BRAM is opaque in Gen);
     - which channel the silicon LUT is (transport, inertial or involution) is a hypothesis, with no
       measured pulse-rejection figure;
     - per-edge windows have no data (prjxray has fast and slow corners only);
     - κ is unmeasured;
     - the research GLS's flop reads x on SR/CE as 0, and its resolver centre has no derivation
       (Fid3, [C]).

2. **A correct gcd.**
   - **Token level [L]:** bdc's gcd_hw graph returns `Nat.gcd a b` for a, b < 2^31 on every
     schedule, live and bounded without fairness (`Net/GcdHwLive.gcd_hw_graph_computes_gcd`,
     8i/8k).
   - **Circuit level, safety [L]: `Net/CapstoneWalk.gcd_hw_circuit_safe3`.** For a, b < 2^31, every
     out0 latch of the concrete 465-channel network is `Nat.gcd a b`, under three hypotheses:
     H_CELLS (the unit-time Ops gate models), H_BUNDLE (`Held`, on zero-delay traces) and
     H_START_ONCE. H_WALK is now a theorem (`gcd_hw_walk`, 8s).
     - Non-vacuity: `Net/CapstoneWitness.gcd_hw_joint_witness`, one run (a=12, b=18) that latches 6
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
         delays; `RigSrcWitness`, lagging read maps, urdly 7). This answers audit `ae791b6, 824f130`
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
         seeds, under SatPin, constant wires and reset, H_ARB (HARB7), SelOK, SelPart and HDsub.
         Audit `eb346fb` CONFIRMED it conditional on those hypotheses; its Lean certificates are
         UNVERIFIED. The gb ENTRY claim was OVERSTATED: E8Mux reran it with the OUTMUX hop, and 2 of
         3 failures are real ([C], same Lean checker).
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
   - **The hypothesis list is stale.** `out/gcd_hw_hypotheses.md` predates all of the above (see §4).

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
       PrimsDSP, which is done but unclaimed.
   - **Token level [L]:** ipow for all i32. Collatz only conditional on C termination
     (unconditional for 1 ≤ n < 256; 8v).
   - **Routed:**
     - tcheck on 12 collatz/xorshift/ipow routes (10n, [C] front end, proved core). No disagreement
       is a fixed-point prjxray failure. Finding for research: rule A times GND/VCC tie-offs as data
       (audit `7f46f23` CONFIRMED).
     - Collatz: xevents5/7 CLEAN at slow and fast on 4 seeds (A-k2); xaudit certifies one
       transaction at slowmax only.
     - A's K3 (xevents8 on ipow and xorshift) is running. xorshift seeds 4 and 6 did not place.
   - **Not yet:** "proves it correct or prints a counterexample trace" as one tool. C's `vk` (one
     `verify.sh` entry point with counterexample traces) is running.

---

## 2. Track rows 5-12 (draft, replaces FEASIBILITY.md:79-86)

Run commands: `formal/check.sh <files>` (paths relative to `formal/lean`) or
`formal/check.sh --committed`. Python evidence has its own command, given in the row.

| # | track | verdict | evidence (checks) | effort to finish | buys the project |
|---|---|---|---|---|---|
| 5 | C-element | **works** (B) | [L] `Cells/{CElemFn,CElemTiming,CElemCore,CElemInvolution,CTree,CTreeTimed,ConstraintsSel,CElemStrict,CElemStrict2,KleeneWin,KleenePess,LutFbBridge,LutFbBridge2}.lean`. A: `Core/{Ternary,XSim,LutAudit}` (bd_c2). Constraints data: `python3 formal/out/cell_constraints.validate.py` (137 rows, 40 exact, 0 errors; 6 planted faults → 6 errors) | X-window widths are unmeasured (board test XW-1, B-kleene-win). The Env closure for the network (cell ← Env1 ← neighbours) is done only for the 2-stage pipe. C-trees: tree latency is unchecked on routes. No time estimate in the journals | **INITs:** machine-checked (audit `71ee3e86` CElemFn CONFIRMED). **Own-feedback race:** exact on every variant only in the STRICT form, one tick (H_X_UNIFORM). With per-edge windows it gains +wq (`KleeneWin`). **C-element fork wait** E ≥ dwmax+dlmax−dlmin: sufficient (B) and necessary (audit `drop_env_latency_cex`); no rule checks it. **C's LutFb/FbFirst:** derived from B's physical model for every bd_c2 in OpsGen, bd_c3 and the mux joins. **Routes:** the RT_FB race is real on bare Muller rings (8 seeds, [C] C-10f) but not reached on the gcd_hw kernel. It fails at the rig's `uenv1` under the band on seeds 2 and 4 (audit `1e7947a` CONFIRMED). **Kleene:** the "definite output" results depend on H_KLEENE_LUT; the safety results do not (`KleenePess`) |
| 6 | Latch / link | **works** (B) | [L] `Cells/{Latch,Bundling,LinkHandshake,LinkTimed,LinkExact,PipeTimed,PipeTimedN,PipePerPin,PipeWitness,RulesKL,FifoFidelity,LibGapLatch,ForkData,WinFifo,WinFifoCausal,NoRevert,ZeroDelayRefine,Necessity5Link,Necessity5Flink}.lean` | The network half of the physical → zero-delay refinement, and multi-token (C-8x running). The FIFO channel hypotheses (Win + H_NO_REVERT) are grade B. No time estimate in the journals | **One exact contract per bd_link stage** (`LinkExact`; audit `69c99a9` CONFIRMED, exact inside `Wf`, which holds 3 timing conditions outside the conjunction). **Physical stage refines C's zero-delay Link iff its six rows hold**, one token (`ZeroDelayRefine.link_ref_iff`; B's self-audit: it is essentially `LinkExact.exact`). **SETUP is proved sufficient only** (audit `71ee3e86` "exact bundling inequality" OVERSTATED). PipeTimedN for every N. Its unit witness was degenerate (audit `c5c6d8b`); `PipeWitness` now gives non-unit and DACK=2 witnesses (not re-audited). **Rules:** tighten.py rule I misses the latch feedback-pin arc (the 200 ps guard covers it), and rule F misses an in-flight value (the guard does not cover it by construction). Both CONFIRMED by audit `71ee3e86`. **FIFO pin-order condition:** with feedback on A1 (up to ~+0.43 ns), it is hidden by the flat SDF |
| 7 | Arbiter (digital race) | **works**; exclusion is **not unconditionally provable**; it holds exactly inside derived race windows (B) | [L] `Cells/{ArbBinary,ArbKleene,ArbInvolution,ArbInvolution2,ArbHandover,ArbA0Fork,ArbCorners,ArbCornersPin,ArbOverlapRace,ArbOverlapPess,Necessity5Arb,TernarySound,TernaryExact,TernaryOnBits,OnNetlistArb,OnNetlistArbKappa,OnNetlistArbKappaExact,OnGcdArb,OnGcdArbA0,OnGcdArbKappa,OnGcdArbKappaTight,OnGcdArbKappaSrv,ConstraintsKappa,KappaCPPR}.lean` (the Kappa files need Mathlib). A: `Core/LutAudit`, `Core/Discretize` (`mutex_between`), `Core/Delay/InvolutionLoop` | **Open:** whether gcd_hw ever runs the bare (non-four-phase) race, which decides the gcd κ threshold between 0.0802 and 0.2166; H_SETTLED. **Board:** the 8% bd_arbcell overlap is NOT explained (needs the measured bitstream's pin map, not archived); κ is unmeasured. No time estimate in the journals | **Metastability comes out of the gate model** under involution channels: a critical same-sense gap, eternal oscillation, arbitrarily late resolution (`ArbInvolution`, A's `InvolutionLoop`). **Runt direction:** from same-sense moves, contrary to the bd_arb header. **Handover exclusion** is relative timing (RT1/RT2), not structural. `grant_skew_exact`: exclusion iff \|d6−d5\| ≤ L (transport model). **link_arb A0 fork:** exact κ thresholds for all 16 cases (`OnNetlistArbKappaExact.exact_X`, mostly irrational; answers audit `861de85` "exact" OVERSTATED, not re-audited); 16/16 safe at κ = 1/11. **gcd_hw:** see goal 2; the 0.0443 figure is the server-free form only. **Withdrawn numbers:** the ArbHeldTimed numeric instances (16 ps, 96 ps, 112 ps server) are corner-mix artefacts (audit `d420b53` OVERSTATED, `71ee3e86` rule-J row REFUTED). ArbCorners' rule-J and RT1b numbers assume q on A3; real routes put q on A5 in 3/4 seeds, which makes rule J 8 ps optimistic for client 1 (audit `c5c6d8b` OVERSTATED); guarded rule J is withdrawn (per-wire counterexample −118.5 ps). **Pessimistic LUTs** do not explain the 8% (`ArbOverlapPess`); under weak0 the detector itself could fire. **H_A0_FORK** is checked by rule J (arb_fork.py), which lacks per-pin site-pin delays (audit `71ee3e86` CONFIRMED) |
| 8 | Composition (Kahn, gcd_hw) | **safety works at circuit level; liveness reduced, not proved; rig first result only** (C, with B's bridges) | [L] `Net/{Handshake*,Muller*,MullerTimed,Kahn,GcdHwLive,Ops*,OpsGen,CapstoneWalk,CapstoneWitness,CapstoneRig,CapstoneLiveNdWalk,IpowCapMain}.lean`; B: `Cells/{LutFbBridge2Env,ZeroDelayRefine,ResetCapstone,RigSrc,RigSrcWitness,RigLaps,ContractBridge,IpowCells}.lean`. Network regeneration: `formal/tools/capnet` (byte-identical, audit `8965ea0`) | **Open:** H_NO_DEADLOCK' plus a liveness witness (C-8z2 running); physical → zero-delay, network half (C-8x running); the Env closure over all 175 links; every rig result (C-8s3 running; B: LapInv fails at a close); H_MAP as a wiring table; H_COMPUTE_FN; H_ARB_EXCL from a timed arbiter (not derivable as stated). No time estimate in the journals | **The gcd result:** `gcd_hw_circuit_safe3` + `gcd_hw_joint_witness`: every out0 latch of the real 465-channel network is gcd a b, from 3 named hypotheses, non-vacuous (audits `f4696cc`, `299a16f`). **ipow:** the same at circuit level (`ipow_circuit_safe3`, audit CONFIRMED). **Do not cite:** `Capstone.gcd_hw_conditional` (no gcd content, audit `eecc6f7` OVERSTATED) or 8u's `gcd_hw_live` (likely vacuous, `start_never_closes`). **Negative result:** the hand-drawn gcd graph of 8b/8f deadlocks for every a ≠ 0 (8j). **Pipelines:** FIFO and live given per-link obligations, under H_SI, an isochronic fork and 3 liveness assumptions (audit `71ee3e86` CONFIRMED with caveats); gate-level bd_link chain for every n (9c) |
| 9 | Ring needs 3 stages | **works** (C) | [L] `Net/{Ring,RingFair,RingGen,RingReset,RingResetCert,RingTimed,RingTimedPure,RingCheck}.lean` | Exact cycle time, N > 5 from reset, other cells on the cycle, a gate-level environment. No time estimate in the journals | **Interleaving model (H_SI):** dead for N ≤ 2, one token live iff N ≥ 3 (`ring_three`), k tokens need N ≥ 2k+1 (`k_tokens`); fair window N(N−1)/2 (`RingFair`, answers audit `71ee3e86` doc row). `RingGen` states them over the generated bd_c2n netlist, so a flipped INIT breaks the headline (answers audit "real INITs" OVERSTATED (mild), not re-audited). **Reset:** bdc's reset leaves every ring empty (`bdc_closed_ring_empty`). From reset with one start token, N = 3..5 have exactly one token and no deadlock, and N = 1, 2 deadlock (`RingResetCert`). **Timed:** `timed_ring_three` (inertial and bounded pure FIFO); rise-to-rise ≥ N·dmin, tight; no runt on a persistent ring. **Bench finding:** tb_ring never varied the token count, and N=4 with two tokens is dead (audit CONFIRMED) |
| 10 | Verified timing checker | **works on real routes**: core proved sound, front end untrusted Python; the delay data are the limit (C) | [L] `Timing/{Semantics,Checker,CheckerFixedFn,Rules,Unroll,MaxNode,SharedPrefix,FbFirstRt,GrantFork*,RuntAck*,OblBridge}.lean`; [C] `formal/tools/tcheck/` (results per route in `tools/tcheck/results/`) | 10m (OUTMUX and tie-off false path, rerun all rows), 10f2 (RT_FB with the xMUX hop) and 10l2 (rule K) were lost last session and relaunched. Rule K fails 16-24 of 42 rows per route at every corner, undiagnosed. No time estimate in the journals | **Soundness:** `check_sound` CONFIRMED by the audit. "Per-node exact" holds only when the witness may choose the cell functions (`CheckerFixedFn`; answers audit `71ee3e86` OVERSTATED). **Rules:** E/A/J each have a proved counterexample. Rule A under E's band is sound iff tl ≤ 403 (answers audit `d420b53` off-by-one). **On 16 routes** (gcd_hw ×4, collatz/xorshift/ipow ×12): every disagreement is project-PASS/tcheck-FAIL, and none fails at a fixed prjxray point. Rule A and tcheck time GND/VCC tie-offs as data (audit `7f46f23` CONFIRMED). **Grant fork:** the runt never breaks the handshake on the 36 gcd_hw arbiters at 4 corners (`GrantFork*`, 10j); RuntAck 288/288 + 304/304 (audit `f4696cc` CONFIRMED, one corner per row). **Caveat:** the 10g rule-J numbers are PARTLY REFUTED (audit `1e7947a`, OUTMUX missing), and "+490 ps" is a mean. See §5 item 1 on whether 10h includes OUTMUX |
| 11 | Netlist import | **works for LUTs** (C, B); whole-design bitstream import being rebuilt | [L] `Gen/{Cells,Netlist,Proofs*}.lean` (36 cells/rtl modules, 163 theorems tying them to B's transcriptions), `Net/Import/*`, `Net/Fasm`, `Net/FasmLink`, B's `Cells/OnNetlist`. Run: `formal/tools/gen/gen.sh --check`, `formal/tools/import/import.sh --check`, `formal/tools/fasm2lean/check.sh` | 11f (FF/CARRY4/F7F8 and whole-design bits) was lost and relaunched. The doc's earlier estimate is 3-5 d to extend fasm2lean to gcd_hw (`out/gcd_hw_hypotheses.md` M5) | **Proofs about generated terms:** a flipped INIT breaks the build. The routed link and arbiter bits (4 seeds) compute the logical cells (audit `d420b53` CONFIRMED). The import's "Kleene spec" equality is same-INIT only (audit `d420b53` OVERSTATED wording). **Pin permutation** after P&R is real and moves delay by up to ~0.5 ns. Research's fasm2net on a gcd_hw route: 11619/11619 LUT functions equal, 3 harmless A6 ties (audit `4a44aef`). B's reset netlist was regenerated from the synthesized netlist (audit `f832d38` CONFIRMED) |
| 12 | Other tools | **bound-finders, not provers** (C): about 1 day per tool | [C] `formal/tools/{smt,async,zone}` (z3 BMC/k-induction/Spacer, Storm, TChecker by git clone) | The 12a/b/c thresholds used the fast/slow corner pair as rise/fall, so they are **suspect until 12d's one-corner rerun lands** (running). UPPAAL/Workcraft/PRISM downloads were blocked | Exact thresholds and witness traces for fixed integer delays in seconds; nothing for all delays. Find the bound fast, then prove it in Lean. 12c raised H_GRANT_FORK, which 10i/10j then measured and proved harmless on gcd_hw. A's Env/EnvFast is the kernel-checked SI analogue of Workcraft |

Per-row notes for the lead:
- **Row 5:** the old row's "1-2 d: port to Core" is stale. B's side of Phase 1 is done
  (`PrelimCore`). Deleting Prelim waits on A's `Core/LutList` (JOURNAL.md 07:17: LutList2 not
  relaunched; it needs B and C in one commit).
- **Row 7:** I left out ArbAnalog/ArbAnalog2/ArbResolve. B keeps them as checked files, but they
  are outside the digital-only north star.
- **Row 10:** the effort column of the old row ("1-2 weeks for routed designs") is overtaken.
- **Row 12:** the old row's numbers ("env min response ≥ feedback max", "server latency ≥ ~60
  ps") are among the suspect thresholds. Do not quote them until 12d lands.

---

## 3. Places in FEASIBILITY.md that are now stale or contradicted (line: why)

1. **:24** "(2026-10-28 ~03:00 UTC)": the date is stale. Replace with §1 above.
2. **:32-35** "Open (probes running 2026-10-28): full involution trace semantics,
   MUXF7/F8/CARRY4/LUT6_2 ... in Core (today only in C's generated files), the per-pin fid GLS
   model": all three are now claimed. InvolutionTrace (`aa90885`), PrimsComb `Core/Prims/*`
   (JOURNAL 08:11), GLSFid/GLSPass2 (JOURNAL 08:01). Still open: flops and latches (PrimsSeq is
   done but unclaimed).
3. **:37-40** cites `gcd_hw_circuit_safe''` with H_WALK as a hypothesis. It is superseded by
   `gcd_hw_circuit_safe3`, where H_WALK is proved (8s). "the physical -> zero-delay refinement is
   C's open 8x": B has since proved the cell half (`ZeroDelayRefine`).
4. **:41-43** `gcd_hw_live_final`: correct, but it omits that there is no witness (audit `fccbd1b`:
   the 8t run violates H_BOUNDED_DELAY').
5. **:43-46** design_verdict8: correct as conditional. It should add: the audit CONFIRMED it
   conditional with its certificates UNVERIFIED; the gb ENTRY claim was OVERSTATED (2 of 3 real,
   E8Mux); E8Hyp found that HARB7 is implied by no B or C statement.
6. **:46-49** "all 36 gcd_hw arbiters safe for κ ≤ 16587/374773 ≈ 0.044 in the literal endpoint
   reading": B now says this is the server-free form and not a gate-level threshold. The
   server-credited thresholds are 0.0802 (bare cell, non-four-phase) and 0.2166 (held four-phase),
   from `OnGcdArbKappaSrv`. H_SPREAD_CORRELATED is a renaming of the lit model (B's self-audit 4,
   item 8).
7. **:49-50** "see `out/gcd_hw_hypotheses.md`": that file is stale (§4).
8. **:51-55** goal 3: missing B's `IpowCells`/`ContractBridge` finding (the contracts are
   timing-free, `fbCel_iff_si`), the DSP48E1 dependence of ipow, and audit `8965ea0` (ipow
   non-vacuity CONFIRMED).
9. **:77** row 3:
   - the effort column "involution exp/log instance 1 h, full trace semantics 1–2 d" is overtaken
     by InvolutionTrace and InvolutionLoop;
   - the text repeats its last parenthetical "(only SAF silicon at the annotated delays; ...)"
     almost verbatim, an editing artefact;
   - the GLSPass history sentence can shrink to "fixed, 263 decls OK".
10. **:79** row 5: "1–2 d: port to Core" is stale (B side done). The rest is overtaken by §2.
11. **:80** row 6: "2–3 d: link stage = C-element + latch, W-bit lift" is overtaken by `LinkExact`
    and `ZeroDelayRefine`.
12. **:81** row 7: "race windows for every property (B, phase 2)" is done in the main. The open
    items are now the bare-vs-held question and the unexplained 8%.
13. **:82** row 8: "works at protocol level + Muller stage", evidence `Net/Handshake*.lean`, effort
    "Kahn/gcd ... (phase 3)". Very stale: circuit-level gcd and ipow safety exist.
14. **:83** row 9: the effort "1–2 d: tie to bounded-delay traces; H_ONE_TOKEN" is done (9d:
    RingTimed, RingResetCert).
15. **:84** row 10: "works on toy netlists", evidence only `Timing/{Semantics,Checker,CheckerToy,Rules}`,
    "1–2 weeks for routed designs", "blocker is delay data (nextpnr SDF has slow max only)". Stale:
    tcheck runs on 16 routes with prjxray bands.
16. **:85** row 11: "yosys JSON for 11 cells" is stale (Gen: all 36 cells/rtl modules).
17. **:86** row 12: the quoted thresholds are suspect (rise/fall misuse, JOURNAL-C 2026-10-27
    11:04), and "zone-based dense time (TChecker) pending" is done (12c).
18. **:136-158** involution bullet:
    - **:139-140** duplicates the `pulseWidth_small` parenthetical (artefact);
    - **:155** "Not covered: the filtered output under chained cancellation; an exp-channel
      instance" is stale: InvolutionTrace covers chained cancellation and an abstract ExpLog
      instance, with the real exp/log not checked;
    - **:156-158** "the arbiter loop has no bounded settling time ... (no MTBF: that needs the analog
      layer, shard B 7c/7d)" is now proved digitally for the OR loop (`InvolutionLoop`), and the
      analog layer is outside the north star.
19. **:159-161** "a shared-corner + local-scatter model is being probed": stale. `Corner.lean` and
    the whole of §3b exist.
20. **:190-207** internal contradiction:
    - **:190-198** (the correction) says the κ ≥ 0.311 ring bound measures the pre-patch SDF bug
      and "does **not** refute the per-path hypotheses";
    - **:201-206** (the estimator paragraph) still says "so the *per-path* hypotheses of
      `ruleE_sound` and `ruleA_sound_rel` are refuted".
    - Keep the correction and drop the refutation, as A-kappa.md's header does.
    - Also relevant: audit `55fde94` (10c OVERSTATED): only ONE ring was measured on silicon for
      the 47-ring comparison, and 1.067/0.989 rest on one fitted global scale. Read "Against
      corrected predictions, comparable rings agree to 1.1% / 6.7%" (:194-196) with that caveat.
21. **:256-257** "a bit-packed checker, EnvFast, is in progress": stale. EnvFast is cited as done
    in row 4 (:78) and in Findings (:405-412).
22. **:264-265** "Not run on gcd_hw yet": contradicted by the next bullet (:266-276).
23. **:301-302** "No seed is certified yet: about 3 days of work left": overtaken by Events8
    (:43-46, `design_verdict8` CLEAN at the slow and fast corners on 4 seeds, conditional).
24. **:349** LUT state loop row: "proved: a critical runt s* exists in (δ∞ − δ(0), δ∞)
    (`arb_eternal`)". A now has more:
    - uniqueness and the exact location (`InvolutionLoop.crit_unique`, s* = δ∞↑ − l, s* > δ∞/2
      for symmetric channels);
    - unbounded resolution time.
    The "0.50-0.58·TLOOP" figure is a Float evaluation, not a theorem. JOURNAL 08:26 notes that
    A-fid3 §3 item 3's skew direction is wrong in this model (correction pending, InvLoop2).
25. **:346** FF row "(PrimsSeq probe in progress)" and **:351** DSP48E1 "not modelled": both
    probes are done but unclaimed. Update when the lead claims them. ipow uses 6 DSP48E1, which
    makes the DSP row relevant to goal 3, not "only if a design's bundled cone runs through a DSP".
26. **:363** earlier table, "MUXF7/F8, CARRY4 | settle within hi | only in datapath cones, never in
    control": superseded by PrimsComb. gcd_hw uses 857 MUXF7 and 343 MUXF8 (JOURNAL 08:11); the
    journal does not say whether any sit in control cones. Drop or mark superseded.
27. **:371-377** finding "C-element own-feedback obligation, unchecked by the flow". It should add
    C-10f's result: real on bare Muller rings (8 seeds) but not reached on the shipped gcd_hw kernel
    (4 seeds). The rig's `uenv1` fails RT_FB under the band on seeds 2 and 4 (audit `1e7947a`).
28. **:400-404** "index sees the pulse: an unchecked bundling margin": now checked on gcd_hw. 10j
    proves the grant-fork runt never breaks the handshake on the 36 routed arbiters at 4 corners;
    RuntAck 288/288 ack + 304/304 index rows (audit `f4696cc` CONFIRMED, one corner per row,
    depends on server latency and H_FF_DRAINED).
29. **:413-414** H_A0_FORK: should add that rule J (cells/verify/arb_fork.py) checks it. B
    corrected its earlier "unchecked". Rule J's real gap is the per-pin site-pin delays (audit
    `71ee3e86` CONFIRMED), and B proposes rule J'.
30. **:8** "a verdict for every track": still true. **:10** "Short answer (provisional)": still
    consistent. No change needed beyond adding "circuit-level gcd and ipow safety now exist,
    liveness and the routed link are the remaining gaps", if the lead wants it.

Not stale as far as these sources go: :57-69 (how to check), :89-120, :163-178, :180-189 (now
consistent with audit `6763571` CornerCode CONFIRMED), :217-243 (audit `065a361` TernaryChannels
CONFIRMED), :333-352 except as noted above.

---

## 4. Stale in `formal/out/gcd_hw_hypotheses.md` (A owns it; dated 2026-10-27 ~11:00)

- §0.1 / §1: the headline is `gcd_hw_circuit_safe''`. The current one is `gcd_hw_circuit_safe3`
  (H_WALK proved, 8s).
- §0.3 item 1: "There is no network-level non-vacuity witness" is contradicted by
  `gcd_hw_joint_witness` (8t; audit `299a16f` CONFIRMED). Liveness: `gcd_hw_live_final` exists
  (conditional, no witness).
- §0.3 item 7 and the §3 last row: "RigContract.lean does not compile" is fixed (audit `807448a,
  21b1b7c` CONFIRMED: it compiles; its claims are withdrawn as conditional on H_RESULT_FRESH).
- §2.6 H_WALK "not proved": it is proved. H_START_ONCE: now `gcd_rig_first`/`gcd_rig_first_env`
  (first result) and B's `gcd_rig_every` (LapInv, no witness).
- §2.2: "These theorems are not instantiated on the 367 operators" is still true overall. Add B's
  `gcd_hw_safe_phys_links` (links only, Env1 assumed), `ContractBridge` and LutFbBridge2.
- §2.3: add `arb_excl_not_derivable` and the Bsrv thresholds.
- §2.5: add `ResetCapstone` (reset → C's safety, H_MAP and H_CELLS_AFTER open). The "netlist
  generators ... not in the repo" point is answered: audit `f832d38` CONFIRMED, regenerated from
  the synthesized netlist.
- §4 M6 (SI discretisation) and the 8x row: add B's `ZeroDelayRefine` (cell half).
- B's paste block for it exists: `notes/B-gcd-hyps-for-A.md` (Bhyp2), with 16 ledger
  contradictions K1-K16.

---

## 5. Contradictions between sources that the lead should settle before pasting

1. **Does tcheck include the slice OUTMUX hop?**
   - JOURNAL-C's verdict block (2026-10-29) says the hop is missing and the rows are "provisional
     until 10m's rerun".
   - `out/gcd_hw_hypotheses.md` §3 says 10h's `extract.py:347-358` adds it.
   - The audit row `f4696cc` Contracts*/RuntAck says "OUTMUX hop IS included (tcheck extract.py
     since C-10h)".
   - The PARTLY REFUTED row (`1e7947a`) is about 10g. Read in this light, C's verdict may be
     over-cautious, or 10m may concern the O5/MUXF exits in particular, which E8Mux found missing in
     A's own band builder. My row 10 states the caveat without settling it.
2. **RT_FB on the rig's `uenv1`:** B (Br correction) and the audit (`1e7947a`) give seed 2
   −114/−219 and seed 4 −81/−201 ps banded; C-10h gives −117/−221 and −86/−243. These are
   different tools and per-pin arcs. Quote both or neither.
3. **gcd_hw κ:** FEASIBILITY:47 (0.0443) vs B 09:50/12:50 (0.0443 server-free; 0.0802 or 0.2166 at
   gate level). Use B's newer reading.
4. **B's journal times** run ahead of the UTC commit times (see the header note).
