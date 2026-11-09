# Shard B journal (cells: C-element, latch/link, arbiter)

## Verdicts (shard B)

All files under formal/lean/Formal/Cells/ check under the lakefile's options
(autoImplicit=false). Session 2026-10-29: every file committed this session was
re-checked by the lead through a private olean build (lean -DautoImplicit=false -o,
real Mathlib where imported) with #print axioms (only propext / Classical.choice /
Quot.sound); a full lake build / check.sh waits for setup.sh's Mathlib build in
this sandbox. Notes: `formal/notes/B-*.md`; hypothesis ledger
`formal/notes/B-hypotheses.md` (rewritten 2026-10-29). Machine-readable cell
constraints: `formal/out/cell_constraints.json` (151 entries, 38 exact, 56 boundary-tight, 10 sufficient at Bj11; generator
`cell_constraints.gen.py` + `cell_constraints.bj5.py`, validator 0 errors).

| track / phase | verdict | evidence (Lean files) | open |
|---|---|---|---|
| 5 C-element | **works** | CElemFn, CElemTiming, CElemCore, CElemInvolution, CTree, CTreeTimed, CTreeExact, CElemStrict(2), **KleeneWin, KleenePess** | the "+1 strict" rows rest on H_X_UNIFORM (KleeneWin: per-edge windows give c(first)+a(after) exactly; feedback window wq makes the strict point a hazard); X widths unmeasured (test XW-1); hold/restore results need per-pin pass(v) under pessimistic LUTs (KleenePess) |
| 6 latch/link/pipe | **works** | Latch, Bundling, LinkHandshake, LinkTimed, LinkExact, PipeTimed(N), PipePerPin, PipeWitness, RulesKL, FifoFidelity, LibGapLatch, ForkData, WinFifo(Causal), NoRevert, **ZeroDelayRefine** | link stage refines C's zero-delay Link/Held iff its six rows (one token, per cell); network half and multi-token running (Bzd2) |
| 7 arbiter (digital race) | **works** | ArbBinary, ArbKleene, ArbInvolution(2), ArbHandover, ArbHeldTimed(2), ArbA0Fork, ArbCorners(Pin), ArbPin(2), ArbOverlapRace, **ArbOverlapPess**, Ternary* | board's 8% bd_arbcell overlap NOT explained (also not by pessimistic LUTs; a weak-0 detector pin could fire the filter falsely); multi-token held-arbiter exclusion running (Barb2) |
| Phase 1 port | **B side done** | Prelim names Core objects; PrelimCore | deletion is a cross-shard patch (notes/B-port-core2.md) |
| Phase 2 library | **works; 40 exact, 42 boundary-tight, 12 sufficient, 11 not necessary (with exact replacements)** | Lib*, Ops*, AMerge*, MuxN3*, Constraints*, Necessity*, **Necessity4Mux*, Necessity5*** | remaining sufficient rows: H_RST_SEL, uxa_join_latency, isochronic_forks, iso_zack, bundled_z_data, rst_flush, bbm |
| Phase 2 on real routes/bits | **works; arbiter safety decided by the corner model, exact thresholds** | OnNetlist*, OnNetlistArb, TernaryOnBits(2), PinAssign, OnGcdArb*, **OnNetlistArbKappaExact, OnGcdArbKappaTight(A), OnGcdArbKappaSrv, KappaCPPR** | link_arb: exact kappa per case (irrational, 0.18-0.55). gcd_hw at gate level with the server credited: 0.0802 if the bare non-four-phase race can occur, else 0.2166 (four-phase held forms) -- decided by Bbare (running). kappa unmeasured; gcd_hw arcs from an unarchived extraction (provenance UNVERIFIED) |
| Phase 3 support | **in progress: bridges to C's capstone, gate-level network closure** | ResetContract, ResetGcd*, Rig*, RigLaps, RigSrcWitness, ResetCapstone*, ResetWitness2, LutFbBridge(2,2Env), ContractBridge, IpowCells(T), AssumeGuarantee*, EdgeTimes*, FiniteRuns*, ZeroDelay*, RingPhys*, ArbNoWithdraw, ArbSettled, ArbMultiToken, ArbAMerge, SelfAuditB6-B8 | NETWORK THEOREMS (gcd_hw_safe_net/net2/net3, fin_net/fin_net3/fin_net3', and the chain forms gcd_hw_safe_chains/fin_chains) do NOT bind pin drivers or the cell set to the netlist (SelfAuditB9; audit P12b CONFIRMED and broader): a pinless cell's contract is the bare claim that its node is clean, so none of them enforces that a link's environment comes from a gate model, and the chain forms are per-link existentials whose end contracts equal Env1 in content. 'Gate-modelled' counts in earlier entries describe the INTENDED elaboration only. FIX (2026-10-31): FiniteNetBound.FGcdNetOKB binds every tied pin's driver to the cell the netlist names (63/175 links bound on both sides); gcd_hw_safe_fin_netB has a JOINT WITNESS on a gate-timed run in which the tied cells drive each other (BWitNet.gcd_hw_fin_netB_witness; unit LUT delays, one run). With every bd_mux gate-modelled and bound as well, and drivers traced through 1-input joins (FiniteNetBoundM): 136/175 links bound on both sides (the 39 unbound sides end at amerge 28, muxn 4, fork trees 6, source 1: FiniteNetBoundMCensus), joint witness BWit2Net.gcd_hw_fin_netBM_witness (same limits). Steer/mux selects bound to bit 0 of the control bus. C's H_CELLS for all 192 non-link operators remains a hypothesis in every one of them (H_OTHER). Departure bounds assumed except on link chains (EdgeTimes). Infinite-run theorems exclude terminating runs (SelfAuditB8); finite form gcd_hw_safe_fin_links has a joint witness on C's real a=12,b=18 run, with each link's Env1 still assumed (finite network closure: Bfin2). Reset->capstone: H_MAP proved (generator byte-identical), H_CELLS_AFTER open. Rig every-result blocked (H_PEND_FAST). H_PIN (arbiter rise-side race) unchecked by any project rule |
| Phase 3 gate-level network, drivers bound (2026-10-31) | **works, with a joint witness** | FiniteNetBound, FiniteNetBoundM, FiniteNetBoundMCensus, BWitLib, BWit2Lib, BWitNet, BWit2Net (+ Data/Cells/NDefs/NChk) | gcd_hw_safe_fin_netBM: C's gcd_hw safety with all 175 links' H_CELLS from B's gate models of links, forks N<=4, 2-joins, steers, ORs and muxes, every tied pin wired to the cell the netlist names (136/175 links bound both sides); joint witness on one gate-timed run (unit LUT delays, wires 1-3). Open: amerge (28 unbound sides), muxn, fork trees, routed delays; H_OTHER (192 operators) still assumed |

| THE goal: H_PRIM and the arbiter under H_ARB(T) (2026-11-01) | **H_PRIM: done for every primitive in the kernel cone; arbiter: H_ARB alone insufficient, separation lemma proved (separation itself not); S3 candidate counterexample at κ >= ~0.15 (simulation, transport-only)** | HPrimWin, HPrimInv, PrimTables, SpecFb, SpecArbVacuous, ArbOKRepair, ArbT, ArbTSpec, ArbClean, Ua1Static | H_PRIM: window form implied by transport/varying/inertial; read-time models (Spec GateOK) do NOT cover involution in general (HPrimInv, audit-confirmed); tables for LUT6_2/MUXF/CARRY4 = Core (PrimTables); no FF in the kernel cone (audit T4). Spec v1 ArbOK vacuous on handovers (fixed by A at 08:11); repaired ArbOK needs T >= state arc; H_ARB(T) alone allows a double acknowledge (spec_double_ack, audit-confirmed); one_ack and q_clean_set(_gen) decide a settled/separated arbitration; the target's nine ustates meet the table facts. Simulation (untrusted, two independent simulators): no arbiter races on the 16 rig vectors (>= ~50 ns); arbiter 0's ack C-element ua1 latches a runt that circulates for ever at g = 1, κ >= ~0.15 (Ua1Static: static margin holds at 0.15, fails at 0.16); ("harmless with runt resolution" WITHDRAWN 2026-11-02: research's fid GLS with its resolver still breaks the handshake at those delays, audit T6; and no finite run shows the liveness failure). Open: S3 obligations proved for every behaviour (checker); the H_PRIM semantics decision; Lean witness of the runt failure (not eventually periodic) |

| THE goal S3: cell theorems on THE target's own gates, every behaviour (2026-11-06) | **works for all 4,597 storage gates (mux joins: while the select is held); environment premises open** | SpecCElem, SpecCElemWin, CElemWinView, CElemWinViewPS, GrantExcl, ArbGrantPS, AckLow, ArbAckPS, SpecLatchSep, SpecCElemFact, SpecCElemWit, CElemPS, ViewPS, CElemView, CElemViewPS, SpecLatch, SpecLatchFact, SpecLatchWit, LatchView, LatchViewPS, ArbViewPS, ArbViewPSReset | `CElemViewPS.target_ps_celem_forced` (361 C-elements switch only when forced, given hA = timed DI protocol + loop race), `LatchViewPS.target_ps_latch_close` (4,185 latches close cleanly and hold, given derived setup / hold / enable-width windows), `ArbViewPS`/`ArbViewPSReset` (9 arbiter state LUTs, separated arbitration, both directions), `ArbGrantPS.target_ps_grants_excl` (grants exclusive once H_ARB(T) has settled the state), `ArbAckPS.target_ps_ack_low` (the losing client's ack stays low while the state is settled; 18 acks); all for every behaviour of `circuit net boundary`, collapsed relation derived from Behaves, held pins derived from constant gates. `CElemWinViewPS.target_ps_muxj_forced` (42 mux joins). Open: hA and the latch windows (network / C), the mux select's stability, close arbitrations (H_ARB(T) + server path). Simulation: windows met with ≥ 2.26 ns slack; all-paths race bound 0.298 is a false path; C's persistence pairs never withdraw in timed runs |

| THE goal: refutation below the 0.44 frontier (2026-11-08) | **works: Lean-refuted at g = 1, κ = 10/25 (w ≤ 20 and plain, every g ≥ 1, κ ≥ 0.40, every reset ≥ 400 ns)** | CexX16 (KBase, RBase, Wit, Refute, AllR, Frontier; C's/A's witness machinery re-instantiated) | race: merge4's arbiter acknowledge C-element ua2 (SLICE_X16Y21.A6) reading its fork; only wide operands exercise it (16/60 vectors fail at 0.38-0.40, 0/60 at 0.35); κ = 0.36-0.39 livelock, exactly periodic at 0.36 (period 79 ps): Lean needs a periodic H_RUNT check (not written). Latch-hold adversary: no failure at 0.43 (1,544 latches, both corners, w = 0 and 20) |

Analog files (ArbAnalog, ArbAnalog2, ArbResolve) predate the digital-only
north star; they check but get no further work.

Library coverage: every LUT INIT in cells/rtl (bd_ce, bd_latch, bd_link,
bd_arb, bd_ctl, bd_merge, bd_mux, bd_end, bd_mem, bd_mlink) is proved equal
to its header equation (CElemFn, Latch, LinkHandshake, ArbKleene, Lib1,
Lib2): no mismatches. Caveat (Lib2): single-X glitch freedom holds for EVERY
INIT under closure semantics, so the per-cell single-X theorems carry no
per-cell content; all of it is in H_KLEENE_LUT.

Headline answers to the owner's model (PROGRAM.md "The model the owner has
in mind"):
- Metastability comes OUT of the gate model, with no arbiter-specific
  postulate: under shard A's involution channel the real bd_arbcell INIT has
  a critical same-sense request gap with eternal oscillation and arbitrarily
  late resolution nearby (ArbInvolution, CElemInvolution); in the analog
  first-order model the same holds as Buridan's principle (ArbAnalog, with an
  explicit non-vacuous loop in ArbAnalog2); Kleene shows only (X,X) at the
  grants (ArbKleene); the e^(-t/tau) law and MTBF bound are ArbResolve.
- Mutual exclusion of a LUT arbiter is NOT unconditionally provable in the
  digital model: a binary runt trace (ArbBinary) and the involution critical
  gap (ArbInvolution) both break it; it holds exactly inside derived race
  windows (request-edge separation vs loop delay, grant skew, BBM on O5/O6).
  (The analog/MTBF view, ArbAnalog/ArbResolve, agrees but is outside the
  owner's digital-only north star and gets no further work.)
- Delay channels: bounded window/pure delay admit all the positive cell
  proofs; pure transport shows runts circulating forever (unphysical);
  inertial decides every runt in bounded time (unphysical); involution gives
  the faithful unbounded-resolution behaviour.
- Ternary simulation is sound AND exact for LUT networks under GMW delays
  (TernarySound, TernaryExact), so Kleene results are statements about every
  binary trace.
- The proofs are about the real cells: B's LUT functions equal the LUTs read
  back from 4 routed bitstreams (OnNetlist).

Fidelity (per primitive, shard B): LUT function exact (real INIT, pin map);
Kleene LUT = hypothesis on ONE 2:1 pass-transistor mux (MuxTree proves the
tree then gives closure semantics in any input order), graded B: credible
for clean or late select edges, doubtful for a mid-rail select while the
legs move (NMOS-only tree). Delays: bounded window/transport channels on ℕ
or ℤ ps; no R/C, no buffered vs pass-transistor pip distinction yet; per-pin
LUT arcs only in 7e. Feedback: a routed wire with an interval.

Findings for the cell owner (not confirmed on a route):
- CORNER MIX (Bg, verified in prjxray utils/makesdf.py:63): the SDF's two
  IOPATH groups are FAST and SLOW corners, not rise and fall. Every "56 ps
  rise / 124 ps fall" number (bd_prims_sim.v, ARBITER.md, 7e/7h/7j/7g
  instances) mixes corners. Theorems are parametric and stand; the numeric
  instances are being redone at consistent corners (probe Bc).

- tighten.py rule I omits the latch's I2 (feedback) pin arc; rule F omits a
  value in flight on the FASTFALL chain wire. Lean counter-traces; today the
  guardband covers both numerically.
- H_A0_FORK: bd_arbiter's hold needs A0's fall to reach ua_k before
  A0 -> q -> g_k does. CORRECTION (7g): this IS checked, by rule J
  (cells/verify/arb_fork.py); my earlier note and owner notification saying
  "unchecked" were wrong. 7g proves rule J's condition exact (iff, both
  clients, box version) and finds rule J optimistic by ignoring per-pin
  site-pin delays (up to ~0.5 ns, not in nextpnr's SDF). [The second reason
  first given here, "a flat 124 ps LUT arc (68-161 ps the wrong way)", was
  the corner mix and is withdrawn (audit row 10): at SLOW_MAX the flat 2x124
  is exact for client 2, and for client 1 26 ps conservative on the identity
  pin map but 8 ps optimistic with q on A5, as in 3 of 4 routed seeds
  (ArbCornersPin.ruleJ_seed, audit row 35).] Proposed rule J' in
  formal/notes/B-arb-a0fork.md. Survey raw minimum +618 ps; worst pin
  assignment leaves ~0 across the full box on the tightest route.
- C-element fork: after seeing the ack the environment must wait out the
  feedback wire (E >= dwmax + dlmax - dlmin). Unchecked.
- CORNERS (Bc, ArbCorners): at a consistent corner the bare-cell handover
  overlap is 0 for every routing (the 16 ps was the corner mix; audit
  CONFIRMED). The rule-J/RT1/RT1b/caps numbers in ArbCorners assume q enters
  ugrant on pin A3 (identity pin map); the routed bits put q on A5 in 3 of 4
  seeds, where O5's arc is 116 ps at SLOW_MAX (< O6's 124) and 48 at FAST_MIN
  (> 45): rule J is then 8 ps OPTIMISTIC for client 1, not 26 ps conservative,
  and RT1b is not structural at SLOW_MAX (audit row 35, ArbPinA5.lean). The
  "guarded rule J covers FAST_MIN" result rests on ONE wire ratio for the
  whole signed wire sum (plus k <= 1, site pins excluded); with per-wire
  ratios inside the measured band it fails by -118.5 ps (audit row 36,
  ruleJ_perwire_cex). Withdrawn as stated; redo per pin per seed (probe Bc2).
- FEEDBACK PIN ORDER (Bq, FifoFidelity): the timed pipe's FIFO assumption
  holds for bd_link_ctl iff (besides FIFO pin buffers and tree) the
  feedback reaches its mux select before the first departing req/ack does:
  w_hi + pq.hi <= E_tau + min(pr.lo, pa.lo). The per-pin term is up to
  ~+0.43 ns with feedback on A1 (slow corner); the flat 25 ps/pin SDF hides it
  from every rule and from the GLS (which satisfies FIFO by construction).
  Counterexample run oscillates. Fixtures suggest feedback does land on A1 in
  some seeds (unverified reading). Fix: a FASM-pin gate, or LOCK_PINS.
- PIN 1 FEEDBACK IS COMMON (Bp, PinAssign, from the bits): the router put a
  C-element/latch feedback on the slowest site pin (pin 1) in 12/36 feedback
  pins of C's fixtures and 24/64 muller64 stages; all 12 muller64 stages that
  fail C-10d's routed RT_FB check have a positive per-pin term. A site-pin
  table in arb_fork.py/skew.py plus pins read from FASM (~0.5 d) would make
  rule J' and H_SEL_ORDER gates.
- ROUTED ARBITER SAFETY HINGES ON THE CORNER MODEL (Bt3, OnNetlistArb):
  on the 4 link_arb bitstreams the A0 fork is safe on 8/8 seed x client
  pairs at one die corner (proved on C's Behaves), negative on 8/8 if each
  delay is independent in [fast_min, slow_max], and negative on 7/8 at the
  fast corner once the 0.772/1.155 guardband is applied on top (arithmetic,
  not Lean), while shipped rule J passes all 8. The corner model needs board
  or GLS evidence (A's kappa estimator).
- ARBCELL 8% NOT EXPLAINED (Bov + Bmt): Bov proved the cell cannot make
  a >= 203 ps grant overlap in any digital trace, and showed the detector's
  site pins CAN at SLOW_MAX if the filter threshold is ~203 ps. Bmt rebuilt
  arb_mtbf (current toolchain, nextpnr 9c732bc6303458df; seed 5 as recorded,
  plus seeds 1-4, an old-binary route and an RLOC route) and evaluated the
  proved window per copy: 0/192 copies predicted to fire on every route,
  because the filter threshold itself, with site pins, is ~1.35 ns (median),
  not 203 ps. The measured bitstream is not reproducible (no FASM/bit kept;
  copy overlap with the board's 15 is at chance). My earlier owner
  notification ("the rig can") is corrected. Side findings: ARBITER.md's
  "146 copies at 0 ps skew" came from placer estimates (real median 138 ps,
  234 with site pins); toolchain.sh's dsp-areg fingerprint
  (ZAREG_2_ACASCREG_1) is also present in the unpatched source
  (xilinx/fasm.cc:5096), so that check cannot fail (verified).
- GCD_HW ROUTES (Br, 4 seeds, nextpnr 9c732bc6303458df, toolchain.sh ok,
  --freq 100): in the KERNEL no C-element violates H_SELORD and no latch bit
  violates the corrected rule I or rule H with site pins at a consistent
  corner. CORRECTION (audit pass 4, rows 43/71): Br reused C's rtfb_design.py,
  which omits the driver-side LUT->xMUX hop (prjxray a6lut->amux
  0.071..0.209 ns); with it, the RIG's urig.uenv1 ring FAILS RT_FB on 2 of 4
  seeds (C's tcheck, run not identified: seed 2 -114/-219 ps, seed 4 -81/-201 ps banded; C-10h, with per-pin arcs: -117/-221 and -86/-243); Br's
  "+4 ps" was optimistic. Kernel margins are unaffected in sign. Rule H with
  site pins drops to +40 ps guarded on its worst bit.
- Held arbiter: g1/g2 and A1/A2 exclusion across a handover are relative
  timing (RT1/RT2), contrary to the header's "structural WITH THE HOLD".
- Arbiter runt direction (7a): the runt comes from SAME-sense request moves
  within one loop delay (both rising from idle with a gap in (0, L), or a
  request pulse shorter than L, or A0 falling against a request edge);
  opposite-sense moves give q exactly one clean edge. bd_arb.v's header says
  the reverse. Exact simultaneity is the only deterministic tie. Ties go to
  the previous winner; alternation needs H_Q_BEFORE_REREQ.
- Bare-cell filtered overlap (8%): an isolated handover overlaps <= 26/3 ps
  at a consistent corner (SLOW_MAX/FAST_MIN) and <= 82/105 ps in the box
  (ArbCorners.caps_are/box_caps; the earlier 72/94 were corner-mixed; pin-map
  caveat of audit row 35) for any request skew, below the filter; the observed events are not the
  digital handover overlap.

## Audit response (claude/audit REPORT.md, read 2026-10-27)

Rows concerning shard B, and what was done:
- Row 10 (REFUTED): "rule J uses a flat 124 ps arc (68-161 ps the wrong
  way)", "O6 rise 45-56, fall 100-124". Agreed: prjxray's two groups are
  FAST and SLOW corners (makesdf.py:63). Withdrawn. ArbCorners (Bc) proves
  every old instance is the corner mix and recomputes: rule J's flat 2x124 is
  exact (client 2) or 26 ps conservative (client 1, identity pin map only;
  8 ps optimistic with q on A5, audit row 35); its real gap is the
  per-pin site-pin delays (Bp/PinAssign measures them from the bits).
- Row 24 (OVERSTATED): ArbHeldTimed/ArbHeldTimed2 numeric instances (16 ps
  threshold, 96 ps margin, "112 ps server") are corner-mix artefacts. Agreed;
  the generic theorems stand. Corrected values are ArbCorners'
  slow_arc_only/fast_arc_only/box_7h/box_7j (at a consistent corner with
  zero routing every condition holds for every server delay >= 0, as the
  audit found). Doc comments and notes of the old files now point there.
- Row 20 (OVERSTATED): LinkHandshake.setup_iff is an arithmetic unfolding;
  SETUP is proved sufficient only, necessary on one trace (setup_needed).
  Agreed; wording fixed (exact only as a worst-case-data condition; the
  audit's setup_not_necessary shows a passing run violating it).
- Row 21 (OVERSTATED scope): deadlock freedom for any N assumes atomic gates
  and isochronic forks (fork delays only N<=3); held_protocol assumes zero
  wire delay; CTree is equality of reachable-state sets in an atomic-cell
  model; Latch.hold_of_dack is a single-transaction arithmetic lemma (Bt2's
  latch_rule_h_net is the windowed form). Agreed; table wording fixed.
- Row 51 (CONFIRMED) adds a result: drop_env_latency_cex shows the C-element
  fork condition E >= dwmax + dlmax - dlmin is NECESSARY, not just
  sufficient. Recorded.

Audit pass 3 (2d5d055), rows on B:
- Row 35 (OVERSTATED): ArbCorners' rule J / RT1 / RT1b / caps use the
  identity pin map (q on A3); real routes use A5 in 3/4 seeds, flipping the
  sign. Agreed; findings line corrected; probe Bc2 redoes it per seed.
- Row 36 (OVERSTATED): guarded rule J needs one wire ratio; per-wire ratios
  break it. Agreed; withdrawn as stated.
- Row 37 (OVERSTATED): PipeTimedN's unit witness is degenerate (req and ack
  arrive in the same tick, the C-element never holds). Agreed; the audit's
  Aud.witness_g repairs the control side; a non-unit data-side and DACK >= 2
  joint witness is now proved for every N (PipeWitness: W1 data, W2 DACK=2,
  W3 per-pin with feedback on the slowest pin; C-element and latch holds
  exercised).

Audit pass 5 (8886b11), rows on B:
- ResetGcdWave / Rst2 "real control netlist" (OVERSTATED wording, theorem
  CONFIRMED): agreed; the 3322-node network is bdc RTL + cells/rtl INITs +
  gcd_rig.v at default sizes, not the synthesized/routed netlist, and its
  generator is lost. Wording fixed in ResetGcd.lean's header and
  B-reset-gcd.md. (Regenerating it from the yosys JSON is a follow-up.)

Audit pass 4 (37951ab), rows on B:
- Row 45 (OVERSTATED): ArbOverlapRace's 305 ps rig overlap is a hand-chosen
  pin/route witness (73 ps with q on ugrant A3); the universal cell cap is
  CONFIRMED. Agreed; Bmt had already shown the rig does not explain the 8%.
- Rows 43/71: Br's gcd_hw RT_FB numbers omit the LUT->xMUX hop; corrected in
  the findings above (uenv1 fails on 2 seeds; rig, not kernel).

North star (PROGRAM.md, owner, 2026-10-27; I read it late, at ~05:30):
digital only. The analog probes (ArbAnalog, ArbAnalog2, ArbResolve) are
outside it: kept as checked files, no further work. The arbiter is treated
as a digital race (ArbBinary, ArbInvolution, TernaryOnBits). Phase 1 task
for B: port Cells from Prelim to Core and delete Prelim. Phase 2: the whole
library against a handshake spec, and formal/out/cell_constraints.json.

## Session Tue Oct 27 10:48:58 UTC 2026

### progress 10:54
Took LOCK-B (previous B lock 1h50m stale). Fresh container: A's setup.sh
running (Lean zip ok; Mathlib from source). Audit 1f6a9a1 row 48 (REFUTED as
checked: RigContract.lean does not compile) is right and is mine:
`stale_window` used the section variable `e` outside `section timed`. The
previous session's probes compiled with bare `lean`, whose default
autoImplicit=true silently bound `e`; the lakefile sets autoImplicit=false.
Reproduced the 9 errors with -DautoImplicit=false, fixed by binding
`{e : Nat → Nat}` explicitly (same meaning as the auto-bound one), and it now
checks under the lakefile's options. Every check in this session passes
-DautoImplicit=false (or goes through lake). A sweep of every core-only
Cells file under those options is running.

### progress 10:58
Launched 12 probes (all write new files only; nothing claimed until it
checks under lake options): Bw (discharge B's FIFO channel hypotheses from
Win plus a spread/pulse bound; contradiction X1), Bs (strict own-feedback
race on the mux-tree LUT; X2), Bk1 (link_arb A0 fork under A's kappa corner
model), Bk2 (cell_constraints shapes under kappa, exact check), Bri
(gcd_rig.idx_setup, the last unproved rig entry), Bfd (H_FORK_DATA and the
amerge index bundling, rows C14/C11), Bu (rig uenv1 single-token release vs
C's H_START_ONCE), Bpt (Prelim deletion made mechanical), Bsa (self-audit of
B files committed after 07:45: vacuity, statement vs note, mutants), Bag
(A0 fork and RT1/RT2 on gcd_hw's routed arbiters), Bpr (audit row 76 prose:
rise/fall wording), Blt (library coverage gaps; dctl lt_first).

### progress 11:21
In (each checked under autoImplicit=false, core olean build; see commit
messages for statements): Bpr (audit row 76 prose), Blt LibGapSteer
(bd_steer select timing exact per pin; bd_link_dctl not emitted, lt_first
deprioritised), Bs CElemStrict (own-feedback race exact only STRICT under the
per-pin Kleene mux tree: X2 resolved in C's favour), Bfd ForkData (C14:
C-8f's H_FORK_DATA sufficient, not necessary; exact form credits the
handshake round trip; C11 amerge index), Bag OnGcdArb (RT1/RT1b on all 36
gcd_hw arbiters x 4 consistent corners; box needs 525-711 ps server, not
proved met; A0 fork on gcd_hw NOT done: routes absent here, probe Bar
rebuilding), Bsa self-audit (19 files compile, 4 witnesses, 7 mutants break;
RigContract stale claim and ContractsMux witness wording OVERSTATED), Bw
WinFifo (X1: B's FIFO hypotheses do NOT follow from Win; FIFO = Win +
H_NO_REVERT under spacing; H_NO_REVERT is inertial-type, a named fidelity
hypothesis), Bri RigIdx (gcd_rig.idx_setup proved sufficient and exact;
RigContract.idx_setup's H_TOKEN_STATIC fails in the running ring).
Bsa's "OpsTimed.SteerWit violates its own H_T1" (commit 3300f44) was
misattributed (probe Bsw): H_T1 belongs to ContractsB.steer_contract, which
SteerWit never claimed to witness; SteerWit witnesses steer_ok and
steer_ok_static. Disproof theorems not_H_T1/not_H_T2 added, notes fixed.
Corrections applied: B-rig-contract.md correction block (5 items: idx_setup
hypothesis, "refuted" -> "excluded given H_RESULT_FRESH", verdict_current
scope, withdrawn necessity, constants not bit-exact); RigContract docstring
theorem name. Bk2 ConstraintsKappa written, held until Mathlib builds
(finding: JSON's "box is always sound" is wrong for kappa > 0).
Running: Bk1, Bu, Bpt, Bmx, Bdg, Bj (JSON: strictness, steer, fork rows),
Bar, Bsw, Bex, Bc4.

### progress 11:23
In: Bmx LibGapMux (bd_mux select exact at both joins), Bdg LibGapDelay
(bd_delay_gated flush exact under stated side conditions; false without
H_LO_ORDER), Bsw (SteerWit finding was misattributed; corrected), Bu
RigToken (rig env ring uenv0/uenv1: release in ANY rst order, given
H_UENV1_HOLD (exact), H_ACK_QUIET, one rst fall; then for any kernel
#start rises <= #results + 1 and the prefix form of H_START_ONCE).
FOR SHARD C (Bu): C's H_START_ONCE (CapstoneCut.lean:145, global
`cnt (riseB start.req) t <= 1`) is false for a whole rig run (one start per
lap); what B proves is the per-result / prefix form (start_per_result,
start_once_prefix). Missing bridges: a T-bounded capstone, the kernel's
return to reset after a lap, the time origin (start.req = 1 at release vs
Src.iz), and H_ENV_REFINES_SRC (uenv1 + fork c3 as C's Src). Rig finding:
H_FB_FIRST at uenv1 is the rig's RT_FB, which fails under the band on seeds
2 and 4 (C-10h); dropping it gives extra start offers
(Stale.stale_fb_extra_start). GLS test: exactly one start_req rise between
consecutive res_req rises on seeds 2/4 at the fast corner.

### progress 11:39
Heartbeat. Core-only sweep: 79 Cells files (all whose closure avoids
Mathlib) compile under autoImplicit=false, no errors; the Mathlib ones wait
for the build (1441 Mathlib oleans so far). In since 11:23: Bpt PrelimCore
(Prelim deletion now a mechanical cross-shard patch; FOR SHARD A: please
commit Wip/_snapA/LutList.lean as Core/LutList.lean and switch Core/Bridge's
imports, see notes/B-port-core2.md; the deletion must land in one commit with
C's `open` lines), Bc4 CElemStrict2 (every C-element variant and cycle, latch
pair bits, exact reset width, needed only at hold vectors), Bj
cell_constraints (128 entries, 127 proved, 19 exact; strict feedback race),
Bex WinFifoCausal (Win LUTs + H_NO_REVERT suffice for the 1- and 2-stage
pipe). Held for Mathlib: Bk1 OnNetlistArbKappa (link_arb A0 fork safe 8/8 at
kappa 1/11; at the guardband kappa s1 client 2 is unsafe in the pessimistic
endpoint reading; A has no measured kappa), Bk2 ConstraintsKappa.
Running: Bar (toolchain + reroute + A0 fork on gcd_hw), Barp (arbcell
per-pin race), Blp (latch per-pin exact), Bmn (bdc_muxn), Bsx (necessity of
sufficient rows), Bex2 (Win lines, general N), Bng (grade H_NO_REVERT), Brst
(gcd_hw reset vectors), Bhyp (B hypothesis ledger for the capstone).

### progress 11:50
In: Bmn LibGapMuxN, Bhyp B-hypotheses.md (29-row ledger + change list for
A's gcd_hw_hypotheses.md), Bsx NecessityReset/NecessityMuxRtz (reset width
exact; JSON reset forms short in box mode; H_RST_EARLY not necessary), Blp
LibGapLatch (latch setup/hold exact per pin; hold strict), Bng NoRevert
(H_NO_REVERT from ordered-replay channels; LUT needs H_MUX_MONO; grade B),
Bar OnGcdArbA0: toolchain restored from the toolchain-cache branch blob
(toolchain.sh 9/9 ok, nextpnr 9c732bc6303458df), C-10e's routes d/2/3/4
reproduced byte-for-byte (FASM, JSON, SDF vs results/sha_*.txt); on all 36
gcd_hw arbiters at each consistent corner the A0 fork is safe (288/288
clients, worst +239 ps) and A1/A2 are exclusive across both handovers given
H_SERVER_GRAPH (server at least the routed R0->A0 path); in the independent
box the fork fails on 15/72 clients (worst -501 ps). So gcd_hw's arbiter
safety, like link_arb's, is decided by the corner model.
FOR SHARD C (Bar): bug in tcheck `extract.Prjx.split`: when a driver leaves
its site through two site pins (O6 on B and BMUX), sink a's OUTMUX hop is
counted as shared and sink b's dropped (16 pairs on the gcd_hw routes). Jx is
optimistic for seed 3 merge11 c2 (421 vs 336) and seed 4 merge12.uarb2 c1/c2
(353/235 vs 270/152), still positive; C-10i/10j rows affected (seed 2
merge10.uarb1 client 1 drg -75/-211 ps). Corrected split in Bar's scratch
extractor (a0extract.py); B-gcd-arb.md carries the correction for Bag's RT1.
Running: Barp, Bex2, Brst, Bj2 (JSON batch 2), Bmg, Blink.

### progress 12:00
In: Bj2 cell_constraints batch 2 (129 entries, 31 exact; reset-width forms
fixed: the old form passed at W = 917 where the real bd_c2 loses reset),
Brst ResetGcdVec (195 of gcd_hw's 414 reset loops are at a hold vector,
where the reset width binds and is exact; 209 forced, 10 frontier), audit
pass 5 wording (ResetGcd on the RTL-level network), Bag2 OnGcdArbFix
(RT1/RT1b re-proved from the corrected extraction, not C's rows: no corner
margin changes sign; seed 2 merge10.uarb1 RT1 172/238/464/659 ps instead of
249/333/636/872; worst +53 / +32 ps at FMIN; box need there 596 ps).
FOR SHARD C (Bag2): C's working-tree extract.py already has the equivalent
split fix (C-10m); RuntAckInst (16 Row literals), GrantForkInst (24 Box
literals) and compare5 Jx (12 A0 pairs) need regenerating; no okAck/okT/okI
verdict flips per Bag2's recomputation. OnGcdArb (old rows) stays as
committed; OnGcdArbFix supersedes its numbers.
Running: Barp, Bex2, Bmg, Blink, Bnet, Bsx2.

### progress 12:22
In since 12:00: Barp ArbPin (arbcell per-pin race: same-sense window
unchanged; handover/opposite-sense exclusion needs pin FIFO, H_PIN_FIFO),
Bex2 WinFifoN (N-stage pipe on Win channels; wires: monotone read => FIFO;
strict DACK flush under Win), Bmg NecessityMerge (uxa_feedback /
uxa_req_latency not necessary; exact H_XA_LOOP), Bsa2 self-audit 2 (10 exact
theorems CONFIRMED, non-degenerate non-monotone witnesses, 13/13 mutants;
JSON citation fixes), Blink LinkExact (one bd_link stage: exact 6-condition
contract, no cross-cell condition), Bj3 cell_constraints batch 3 (130
entries; validator enforces exact => iff), Bsx2 Necessity2* (18 more rows
necessary at the boundary or not necessary), ArbHeldTimed2 runt-decay remark
corrected. Mathlib build: 2264 oleans; Mathlib-closure files still waiting.
Running: Bnet (regenerate the reset network from the real build), Bfw
(first-wave reset cells), Barp2 (arbcell per-pin on gcd_hw routes), Bct
(C-tree depth >= 2 exact), Blink2 (closed-loop link pipe, W bits, tokens),
Bsx3 (necessity round 3).

### progress 12:35
In since 12:22: Barp2 ArbPin2 (no routed gcd_hw arbiter needs H_PIN_FIFO;
seed 2 merge3.uarb1 fails within one corner's range even with FIFO pins),
Bnet ResetGcdNetRe/ResetGcdNetR5 + committed generator (reset contract
re-proved on the synthesized network and on the R5 board build; audit
pass-5 caveat closed for ResetGcd), Bct CTreeExact (bd_ctree exact at any
depth), Bfw ResetGcdVec2 (per-cell reset model derived from the network
run; 21 first-wave cells closed). Running: Blink2, Bsx3, Bk3, Bj4, Bwv
(Wave/Vec on the real nets), Bsrc (rig env as C's Src).

FOR SHARD A (FOR-RESEARCH.md input, probe Bgls, notes/B-gls-vs-exact.md):
research GLS bug gen.py:494-512 (GLS_SCALE_INST not applied to wire delays
under wire-mode scatter); fid resolver runts hidden without +META_VERBOSE;
ranked minimal GLS changes C1-C7 to make B's exact rows GLS tests.

FOR SHARD C (probe Bsrc, notes/B-rig-src.md): RigSrc.gcd_rig_first_env is
C's gcd_rig_first with H_ENV and the sources' SrcR discharged on B's side
(rig_cellR gives CellR for every operator incl. sources). In C's hypothesis
table: Src.H_LUT_SI (channels 0-2) and H_ENV proved by B; Src.dat = H_DAT;
Src.iz false at release, supplied by preRun. Still open for C: laps >= 2,
and the rig's sinks K.sink 416 / K.sink 3 as H_SINK_SI.

### progress 13:02
Mathlib is built far enough here (CornerNat and the Delay modules compiled
by setup.sh's lake build, still running for the rest of Formal). Checked
under the real Mathlib with the lakefile's autoImplicit=false (lean -o into
a private overlay of lake's build dir): ConstraintsKappa (Bk2),
OnNetlistArbKappa (Bk1), OnGcdArbKappa (Bk3), and ArbInvolution's comment
edit; collectAxioms over all 784 theorems of the three kappa files: only
propext/Classical.choice/Quot.sound. Results:
- Bk2: the exact corner-model check GenOK for every constraint shape
  sum(P)+a <= sum(Q)+b (sound; tight under H_DISJ+H_DIV; sandwich within
  1 ps per arc otherwise). The JSON's "box is always sound" is FALSE for
  kappa > 0 (box_unsound_with_kappa); a SLOW-only check is unsound even at
  kappa = 0. kappa_check patch to be regenerated into the JSON next.
- Bk1 (link_arb A0 fork): safe on 8/8 at kappa = 1/11; at the guardband
  kappa (0.199) 8/8 in A's literal endpoint reading, 7/8 in the
  side-pessimistic one (s1 client 2 unsafe from kappa ~ 0.18).
- Bk3 (gcd_hw, all 36 arbiters x 18 conditions): under A's literal
  endpoints every condition holds for kappa <= 0.0443 (binding: seed 3
  merge12.uarb1 RT1b without server credit), 0.0802 with the server
  credited (binding: seed 2 merge3.uarb1 r2->r1 handover); in the
  side-pessimistic reading 5 rows on 3 arbiters fail at kappa = 0. So
  gcd_hw's arbiter safety needs a measured kappa below ~0.044 (A's model).
Also in since 12:35: Bsx3 Necessity3*, Bsrc RigSrc, Bkx KleeneBox, Bgls.

## Session Tue Oct 27 02:48:05 UTC 2026

### progress 02:48
Took LOCK-B. Running A's setup.sh next; then probes for tracks 5/6/7.

### progress 02:52
A's setup.sh running (Lean 4.35.0 via GitHub zip; Mathlib by git, built from
source since the cache hosts are blocked). Wrote Formal/Cells/Prelim.lean (core
Lean only: K3, lutB/lutK, muxTree, LUT6_2 O5/O6) so the binary and Kleene cell
proofs need not wait for Mathlib. Sanity: bd_c2's INIT = ~rst.maj(a,b,q) by
decide in 0.3 s.
Launched 12 probes: 5a CElemFn, 5b CElemTiming, 5c CTree, 6a Latch,
6b LinkHandshake, 6c Bundling, 7a ArbBinary, 7b ArbKleene, 7c ArbAnalog
(Mathlib), 7d ArbResolve (Mathlib), 7e ArbHandover, Bf MuxTree (fidelity of
H_KLEENE_LUT: per-mux hypothesis vs closure semantics).
Choice: discrete time (ℕ ps ticks, traces ℕ → Bool) for the cell timing
probes, ℝ only for the analog loop. Reason: the cell lemmas are about finite
delay intervals and finite INITs; ℕ keeps them in core Lean with decide/omega.
To reconcile with A's trace choice once Core lands.

### progress 02:59
Checked and pushed: 5a CElemFn, 6a Latch, 7b ArbKleene (all core Lean, clean,
axioms propext/Quot.sound). setup.sh was looping on `lake update` because
Mathlib's post-update hook runs `cache get`, which fails file by file
(cache host 403); killed it and started `lake build` of Formal plus the
Mathlib ODE/exp/log/IVT/Lebesgue modules directly.
Finding from 7b (to check on a route, not a confirmed defect): the A0 hold in
bd_arbiter relies on the A0 fork ordering H_A0_FORK: A0's fall must reach ua2
before the path A0 -> ustate -> q -> ugrant -> g2 does, or A2 = C(g2, A0)
fires for a transaction the server never started.
Untracked files in the tree are probes still being written; they are
committed only after they check.

### progress 03:07
In and pushed: 5b CElemTiming, 5c CTree, 6c Bundling, 7e ArbHandover, Bf
MuxTree. Verdict table at the top. Launched 5d (C-element on A's ℝ-time
Core channels; inertial/involution), 7f (ternary-sim soundness), 7g (A0
fork), 7h (RT1/RT2 timed). Running: 6b, 7a, 7c, 7d. Note: A's Core uses ℝ
time and a FIFO pure delay; 5b's window channel is weaker than FIFO, so its
positive results transfer and its counter-trace (fixed transport) is FIFO.

### progress 03:13
In: 6b LinkHandshake, 7a ArbBinary, 7f TernarySound, 7g ArbA0Fork (rule J
proved exact; corrected my earlier "unchecked" claim, owner re-notified).
Launched 6d LinkTimed (controller composed with latch, timed), 7i
TernaryPhases. Running: 7c, 7d (waiting on Mathlib), 5d, 7h, 7i, 6d.

### progress 03:17
Container restarted. Lost: the Mathlib lake build (about 1430 oleans had
survived; restarted) and all running probes. Resumed 7d, 5d, 7h, 7i, 6d from
their transcripts; 7c was not resumable and was re-created to continue from
its files on disk (Wip/Cells/ArbAnalog.lean, notes/B-arb-analog.md).

### progress 03:26
In: 7h ArbHeldTimed, 6d LinkTimed (stage contract; env latency, enable
pulse width and reset sequencing unchecked by any rule), 7i TernaryPhases
(A0-fork early ack is a concrete bounded run; C-element and arbiter-tie X
shown exact by witness runs). 5d CElemCore (involution: an unresolvable runt
width always exists; inertial circulation band is [rho, D-rho]) is written
and was checked by its agent against hand-compiled Core oleans; held back
until lake builds Core and it checks there.
Launched: Lib1 (bd_ctl/merge/mux INITs + Kleene), Lib2 (bd_end/mem/mlink),
7j (held arbiter, client-2 direction + non-vacuity), 6e (N-stage pipe timed).
Running also: 7c (analog, re-created), 7d (resolution law).

### progress 03:49
In: 7j ArbHeldTimed2 (non-vacuity witness for both directions), Lib1, Lib2
(library INIT coverage complete, no mismatches), Bg notes (GLS comparison;
corner-mix finding verified, owner notified). Launched Bc (consistent-corner
re-instantiation, corner sign changes), Bh (iverilog runs of the
predictions), Lib3 (merge/mux handshake). Running also: 7c, 7d, 6e.

### progress 04:06
In: 6e PipeTimed (2-stage pipe, FIFO channel, witness), 5d CElemCore
(lake-checked against Core), 7d ArbResolve (Mathlib: e^(-t/tau) law,
probability and MTBF bounds, no_deadline), Bh notes (iverilog runs: all six
predictions match on the real cells; the GLS is one LUT arc more permissive
than the formal transport thresholds on loops, so formal numbers stay the
gates; iverilog ICBUF delay lost on a net that is both input and output of
one instance in the gate build).
MergeMuxSI (Lib3) is being split: its 2000-state check takes 7 GB / 160 s,
too heavy for a claimed file in every shard's lake build; it goes to Wip.
Running: 7c (analog), Bc (corners), 6f (pipe general N), Lib3 split.

### progress 04:14
In: 7c ArbAnalog, Bc ArbCorners, 6f PipeTimedN. All three tracks have a
verdict. Running: 5e (involution loop on Core), Bn (B theorems on C's
bitstream-read netlists), 7k (analog non-vacuity, rate closure), Bq (FIFO
assumption fidelity), 7l (general ternary exactness). Full check.sh running.

### progress 04:19
Full formal/check.sh on this sandbox: lake build of all of Formal/ OK (2939
jobs, all three shards); the axiom audit then failed only because the root
Formal.olean was not built (the lakefile globs "Formal.+" do not match the
root module). Built it with `lake env lean Formal.lean -o` and re-ran the
audit: 9443 declarations checked, none BAD. For shard A (owner of
check.sh/lakefile): the root module may need adding to the build.

### progress 04:37
In: 5e CElemInvolution, 7m ArbInvolution, 7l TernaryExact, 7k ArbAnalog2,
Bq FifoFidelity, Bn OnNetlist. Headline-answer block added at the top.
Running: Bp (real pin assignments from FASM), Bt (timed bridge to the
bits), Bx (ternary checker on the whole routed netlist).

### progress 04:56
In: Bt OnNetlistTimed (timed C-element/latch theorems on the 4 routed
bitstreams; Dmax 569-960 ps by seed). All six running probes (Bp, Bx, 6g,
5f, Lib4, Bt2) were stopped by an API session limit at ~04:45; resuming them
from their transcripts.

### progress 05:38
Read PROGRAM.md's owner updates (north star: digital only; 48-hour phases)
and the independent audit; responses above. Phase 2: cell_constraints.json
out (84 entries). In since last note: 7n ArbInvolution2, Bt3 OnNetlistArb,
audit corrections, Bk RulesKL, 5f CTreeTimed, Bx TernaryOnBits.
Running: P1 (port Cells from Prelim to Core, non-breaking for C/A's
importers), P3 (prove the 19 unproved constraint entries), Bov (does a
digital race explain bd_arbcell's unexplained overlap?), Bx2.

### progress 07:03
Audit f5facff: no new rows on B. In since the last note: Bov/Bmt (arbcell
8% not explained; correction sent), Bg2 gcd_hw inventory, P3 Constraints*
(16/19 unproved entries closed), P4 JSON update (87 entries, 82 proved), Lt
OpsTimed* and Lt2 OpsTimed2 (timed steer/mux/merge, control and value), Cm
AMerge*/MuxN3* (control_merge and 3-way header, SI), Bc2 ArbCornersPin
(audit rows 35-36), 6h PipeWitness (audit row 37).
Running: P1 port (Prelim -> Core), Br (obligations on routed gcd_hw, 4
seeds), Cm2 (timed control_merge obligations), Lt3 (necessity of operator
obligations).

### progress 07:45
Audit c27fc04: no new rows on B. P1 port of Prelim onto Core finished in the
working tree (Prelim now names Core's objects: K3 = Core.K3, lutK = Core's mux
tree, Trace/WinDelay = Substrate.Sig/Win; 114 importing modules incl. C/A
compiled by the probe); a full lake build is verifying it before commit.
P5: cell_constraints.json at 116 entries (110 proved). In: Cm2
AMergeTimed*, Lt3 OpsCounter (6 value obligations exact on a run; 4 control
obligations shown unnecessary), Rst ResetContract (pending commit with the
port).

### progress 08:16
PHASE 1 PORT committed (e54d7ca), verified by a full lake build (3115 jobs)
and check.sh OK. Prelim now names Core's objects (K3 = Core.K3, lutK = Core's
mux tree with lutK_ofFn = Lut.keval, lutB_ofFn = Lut.eval). NOT deleted: C's
Net/Fasm/Basic, Net/CoreLutPrelim, Gen/PrelimSem, Net/Import/PrelimSem and A's
Core/Bridge still import it; their Cells bridges are now identities (toCells,
toP/ofP). Recommended deletion route (notes/B-port-core.md): move Prelim's
list-based LUT API into a Core module (e.g. Core/LutList.lean, shard A) and
change import lines. The Trace/WinDelay half (CElemTiming -> Substrate) was
reverted: it makes Core.Circuit visible to importers, and Formal.Core.Gate
then shadows Env.Gate in A's Core/EnvFast/SteerEnv.lean (unqualified 'Gate'
at l.84). FOR SHARD A: qualify it (Env.Gate) and B will redo that half.
New in the same commit: OpsCounter, OpsExact, MuxN3Timed, ResetContract,
ResetGcd/ResetGcdNet (gcd_hw control network reset and release, by decide).
In before that: Br (gcd_hw routes: clean at consistent corners).

## Session Wed Oct 28 02:48:37 UTC 2026

### progress 02:48
Took LOCK-B (previous B lock 13h46m stale). Running setup.sh; reading the audit.

### progress 02:52
Audit (e7b64c5, unchanged since 2026-10-27 12:42): no new rows on B; row 59
(RigContract) is PENDING the auditor's pass-6 rebuild, fix already in 807448a.
Fresh sandbox: 4 cores, 15 GB, so formal/slot.sh allows 3 Lean processes; A's
setup.sh is building Mathlib from source (cache host 403). Probes check through
a private-olean checker (lean -o into a scratch dir with -DautoImplicit=false, through
slot.sh, no lake build). Prelim deletion is left to shard A's coordinated
LutList2 probe (a B-only switch changes statement text that C's files depend on).
Launched 11 probes: Bnx4 (necessity of the bd_mux/bdc_muxn latency rows), Bnx5
(remaining sufficient rows: FASTRISE ack_flush, rst_flush, reset_first, settled
exclusion, token_static), Bsa3 (self-audit of files committed since 12:20), Blap
(rig laps >= 2, H_SINK_SI), Brz (reset state at the capstone's T0 from B's reset
run), Bgr (gcd_hw routes: feedback site pins, H_SEL_ORDER, strict feedback race per
cell), Bshp (shared path prefixes in the arbiter race conditions vs the kappa
threshold), Bipw (cell contracts for C's ipow_hw capstone), Bj5 (JSON: apply
KleeneBox, Necessity3, kappa results), Bxw (the X-window width: parametric exact
form and a test design), Bhyp2 (hypothesis ledger refresh, change list for A).

## Session Thu Oct 29 07:14:49 UTC 2026

### progress 07:14
Took LOCK-B (previous B lock 28h stale). The 2026-10-28 02:48 session's 11
probes never landed (no commits after its session start; sandbox ended): none
of Bnx4/Bnx5/Bsa3/Blap/Brz/Bgr/Bshp/Bipw/Bj5/Bxw/Bhyp2 is claimed. Running setup.sh.

### progress 07:19
Audit (pass 7/8 at formal 6863284): rows on B are 18 (OnNetlistArbKappa "exact
per-pair thresholds" OVERSTATED: the gap kappa* .. kappa*+6/(E+L) is undecided and
the auditor has a whole-ps violating assignment inside it at 200/1103), 19
(OnGcdArbKappa "tight" mildly OVERSTATED: unsafe side only at arc level at kappa_u),
88 (KleeneBox CONFIRMED in model; H_KLEENE_LUT is the optimistic hazard-free
extension). Withdrawn until decided: "exact" for the link_arb kappa thresholds and
"tight" for the gcd_hw one. Probes on each.
Fresh sandbox again (4 cores, 15 GB, 3 Lean slots); setup.sh building Mathlib from
source. Core-only files check through a private olean checker (lean
-DautoImplicit=false -o, through slot.sh). Launched 13 probes: Bkx18 (decide the
kappa gap, row 18), Bkx19 (gcd_hw kappa tight + gate-level unsafe + within-corner
spread hypothesis, row 19), Bpess (pessimistic LUT models vs H_KLEENE_LUT, row 88),
Bnx4 (mux/muxn rows necessity), Bnx5 (other sufficient rows), Bsa3 (self-audit),
Bxw (non-uniform X windows), Bhyp2 (ledger for the capstone), Brz (reset ->
capstone initial state), Bipw (ipow cell contracts), Blap (rig every lap), Bshp
(shared-arc cancellation in kappa checks), Bj5 (JSON update + audit label fixes).

### progress 07:28
In: Bhyp2 (notes only). B-hypotheses.md rewritten for the current capstone
(gcd_hw_circuit_safe3, gcd_rig_first, gcd_hw_live_final); B-gcd-hyps-for-A.md is
the paste block for out/gcd_hw_hypotheses.md. Finding: the capstone's import
closure (69 modules) contains from B only LinkHandshake's `ctlB` (a definition),
so NO B cell hypothesis is a Lean hypothesis of any capstone theorem: B's rows
enter only through four unmechanised bridges (OpsGen bindings / LutFb not derived
from any B lemma; 8x physical -> zero-delay; M6 SI discretisation; reset -> init,
probe Brz). Exception: RigSrc.gcd_rig_first_env, whose env binders are real
hypotheses (uenv1's H_UENV1_B/M1 graded C: fails under the band on seeds 2/4) and
which has no joint witness. Contest-freedom does not discharge H_ARB_EXCL (still
A0 fork + RT1/RT2 + server: per corner proved, C in the box and for kappa >
0.0443). 16 B/C/A ledger contradictions listed (K1-K16).

### progress 07:34
In: Bj5 (data, no Lean). cell_constraints.json: 132 entries, 131 proved, 33 exact,
validator 0 errors (negative control: 5 planted faults -> 5 errors). KleeneBox makes
the six select setup/hold rows of bd_steer/bd_mux/bdc_muxn strict (+1) in
binary-edge times under H_KLEENE_LUT + H_X_UNIFORM (w = 1 tick, grid minimum); the
'<=' form stays exact in definite-window times. Necessity3 lifts 7 rows (bd_pipe
boundary_I/boundary_H/data_lead/output/lat_lumped, bd_arbcell.grant_skew,
bdc_amerge.bundled_idx_ack_g) to necessary at the 1-ps boundary; bd_pipe.rst_lines
stays sufficient. Every corner-model row records kappa (unmeasured); the corner rule's
"box always sound" corrected (false for kappa > 0). Audit row 18: link_arb kappa*
recorded as a safe bound, not exact. Audit P8: bd_ctree.node_loop and
bd_merge.uxa_loop now state the binary '<=' form their iffs prove (scope H_PIN_FIFO;
the +1 is strict_pending); new informational row bd_link.stage (LinkExact, scope
Wf + Split). The validator now rejects an exact row whose +1 has no strict-form iff.
The patch pass is committed as out/cell_constraints.bj5.py and run by
cell_constraints.gen.py (regeneration reproduces the JSON; md table re-rendered).

### progress 07:39
In: Bxw KleeneWin (core; checked under autoImplicit=false, axioms standard on 33
theorems, re-run by me). H_X_UNIFORM dropped: each binary edge has its own X window
[T-a, T+c), and every race gains c(edge that must come first) + a(edge that must come
after), exactly (iffs: steer_win_exact, join_win_exact, muxn_win_exact,
latch_win_exact, cel_edges_iff/cel_env_iff for every C-element Facts cycle). New
H_FB_WIN: the feedback pin's own window wq adds +wq to the own-feedback race
(clean_iffW, box_iffW, cel_env_win_iff, latch_fbwin_iff); on the real bd_c2 INIT,
CElemStrict's strict_clean point becomes a hazard at wq = 1 (c2_fbwin_hazard).
steer_split_matters: with width-1 windows on every edge, binary equality can be safe
and a 1-tick-strict margin unsafe, so "+1 strict" comes from H_X_UNIFORM, not from
the cells. Not covered: window values (no data bounds w: prjxray/SDF carry no
transition data; the research GLS has w = 0 by construction and an assumed
WIN = 150 ps), adversarial per-token windows, muxn unselected Cover. Test XW-1
(notes/B-kleene-win.md): MMCM-phase-swept bd_c2 race with a held-level outcome; the
mixed band width W̄ replaces +1 in every strict row and calibrates the GLS's WIN.

### progress 07:43
In: Bsa3 self-audit 3 (notes/B-self-audit3.md; SelfAuditB6 + generated
SelfAuditB6Data, both checked here, axioms standard). Audit row 824f130 (joint
env+network non-vacuity of RigSrc.gcd_rig_first_env, UNVERIFIED) closed: one
unit-delay rig-environment run of C's 465-channel gcd_hw network (a=12, b=18)
discharges every hypothesis of gcd_rig_first_env, decided by the kernel and fed
into the theorem (rig_env_feeds); out0 latches 6 at tick 474, the env's second lap
starts at 432 (rig_env_latch/relap). Needed a generic lemma cell_sh1 (one-tick
left shift keeps every non-source cell model). The witness is degenerate in its
delays (identity read maps, urdly 0, unit gates): probe Bjw redirected to a
non-identity / nonzero-delay witness. Reset contracts on ResetGcdNetRe/R5 now have
all-zero-start witnesses (D = W = 0). OVERSTATED (mine): ResetGcdNetR5's generated
header says "checked node by node" but that part is omitted, and it labels ~1511
removed delay elements as merged data inputs (harmless: no gate pin reads them);
the R5 transcription is unverifiable here (netlist JSON not on disk). Mutants:
4/5 fail as they should; a 1-tick in_ack shift passes H_C3 alone (caught by the
env check as a whole). Nothing refuted.

### progress 07:48
In: Bipw IpowCells (core; checked here, axioms standard on 30 theorems). Goal 3,
second kernel: C-8y's H_CELLS for ipow_ps's 83-operator network follows from
per-cell contracts on the emitted cells (generated LUTs at their real arity; FbCel =
H_LUT_SI + BoundedDelay feedback route + H_RT_FB on every feedback LUT):
ipow_cells, and ipow_safe_of_contracts = ipow_circuit_safe3 with H_CELLS replaced by
the contracts. New: generated N=1..4 C-elements are flat (cgate_eq, decide);
bd_pipe stage controllers = bd_link's; a join with unmodelled source-chain inputs
meets C's Join (join_of_contract; was prose); B's WinDelay feedback wire gives C's
BoundedDelay (the only B-model bridge proved). Remaining hypotheses, NOT derived from
B's cell theorems (cited only): H_SEL_PIN, H_DELAY_LUMPED, H_CTREE_ATOMIC (once:
uselect0's 5-input join), arbiter grant fields, data fields incl. the two DSP48E1
multiplies, which no shard models (needs a DSP primitive model, a function check of
the mapped multiplier, its delay vs the matched 64/118 delays, glitches). Non-vacuity
only by an all-quiet run (b=3, e=7) plus a switching FbCel witness. Finding: C's
network omits 2 bd_src, 2 bd_fork, 4 source-chain constants and 4 join inputs of
the emitted design (harmless for H_CELLS, proved; matters for liveness). The
operator-to-Verilog match is by hand from bdc/emit.py output (scratch).
ResetGcdNetR5 header corrected per self-audit 3 (comment only; file re-checked).

### progress 07:52
All of the following re-checked here (private olean build, autoImplicit=false;
axioms only propext/Classical.choice/Quot.sound).
- Bnx5 Necessity5{Arb,Delay,PipeRst,Link,Flink,Mem} (notes/B-necessity5.md):
  bd_arbcell.grant_skew EXACT for every delay triple in the transport model
  (grant_skew_exact: exclusion iff |d6-d5| <= L); settled exclusion exact on its
  shared-q precondition (settled_iff). FASTRISE H_ACK_FLUSH exact for DACK=2 and NOT
  necessary for DACK>=3 at line level (pulse_iff; the real DACK=3 chain is clean
  while violating it by 1); bd_pipe rst_lines DACK/guard terms boundary-tight, so
  with Bsx3 every PipeTimedN reset/line term is; bd_link_dc K'/L' and bd_flink
  qfb_first boundary-tight (Lean <= at guard 0); bd_mem setup/hold/rdata/clk_low
  exact in the event model, clk_high's shipped bound not necessary (exact: tPWH <=
  dcLo + dsLoF). JSON not yet updated (next Bj pass). Open: rst_flush, bbm,
  H_RST_SEL, pipe-level ack_flush, the Kleene +1 on these rows.
- Bfb LutFbBridge (notes/B-lutfb-bridge.md): bridge Br1 closed per cell kind. C's
  OpsGen premises LutFb/FbFirst (imported verbatim) follow from B's physical model
  (Win LUT + H_NO_REVERT, WinDelay feedback wire) plus the four-phase environment
  Env1/EnvC with Timing1, H_LUT_POS (1 <= lo) and H_PWR, for the link controller
  bd_c2n (link_lutFb -> Link.H_CEL_SI) and every bd_c2 C-element in OpsGen (fork2,
  join2, muxN, arbiter ua1/ua2, mux uxa/uya). Witnesses with LUT bands [1,3]/[1,2],
  wire 1. Counter-runs: without H_NO_REVERT both premises fail; an ideal transport
  loop with a one-tick input runt breaks LutFb, so it is a cell+environment fact.
  Open: mux uj0/uj1, bd_c3, C-trees, LutSI premises, deriving Env from neighbours
  on gcd_hw, instantiation on CapstoneNet.
- Bpess KleenePess (notes/B-kleene-pess.md): pessimistic bracket below
  H_KLEENE_LUT (audit row 88). Per-pin X-select policies <p0,p1> (kle, weak1 NMOS
  weak 1, weak0, strict) and output retention; strict <= model <= lutK for any tree
  order (bracket); exact: output definite v iff closure = v and every X pin passes v
  (lutP_definite; tree/pin order irrelevant). Every exclusion/safety result
  transfers (excl_M, arb_acks_safe). Every hold/restore/reset becomes "needs pass(v)":
  C2(1,1,X)=1 iff p1; latch hold of q needs pass q; RST0 needs p0, RST1 p1;
  under weak1 the arbiter reset leaves q = X. KleeneBox: steer +w survives weak1,
  fails without pass-0; join +w fails under every pessimistic model (explicit runs).
  So the "definite output" results depend on H_KLEENE_LUT, the safety ones do not.
  Deciding test: board runt-flag pass matrix (6 pins x 2 values, FDCE async flag).
- Bjw RigSrcWitness(+Data) (notes/B-rig-src-witness.md): second joint witness of
  gcd_rig_first_env with every read map lagging (beta=t-3, phi1=t-5, phi0=t-4,
  gamma=t-2/3/5) and urdly = 7; out0 offered 438, latches 6 at 489; c3/uenv1/uenv0
  holds exercised (w_nondegenerate). A latch needs lap 2 offered first (M0 with
  monotone phi0). cell_sh1 duplicates SelfAuditB6.cell_sh1 (separate namespaces;
  to dedupe later). Open: H_SINK_SI in general, time-varying lags.

### progress 07:54
In (checked here, axioms standard):
- Bkx19 OnGcdArbKappaTight (core) + OnGcdArbKappaTightA (Mathlib bridge to
  OnGcdArbKappa's objects; checks now that Mathlib's needed part is built). Audit
  row 19 closed for the binding row (g3 merge12.uarb1 RT1b, server-free form, lit
  reading, A's CornerNat restated field for field, whole-fs delays): safe for
  kappa <= 33176.932320/749546 (rt1b_safe, a certificate sound for every rational
  corner), unsafe for kappa >= that + 1/749546000000 (rt1b_unsafe; the binding corner
  is interior, c = 27/5295104). The whole kappa_ex - kappa* (~3.9e-6) is the 1 fs grid.
  Gate level (rt1b_gate_unsafe): a full 7j run (real INITs, all t, server included)
  overlaps g1/g2 for every kappa >= kappa_U, BUT only with zero server delay, zero A0
  route to ustate and zero ustate O6 arc (what the server-free form allows). With
  those delays credited as corner-model arcs this arbiter's threshold is 0.651 and
  the design minimum becomes 0.0802 (g2 merge3 h21). So "0.0443" is the server-free
  form's number, not a gate-level threshold of the routed design. Lit safety now
  carries the named hypothesis H_SPREAD_CORRELATED; under H_SPREAD_INDEP (cons) the
  row fails at every kappa incl. 0 (-46.8 ps). Board test T_SPREAD in the note.
  Other rows keep their gap (<= 1.8e-5). Arc numbers still from Bar's extraction
  (routes not on disk: provenance UNVERIFIED, as the audit says).
- Blap RigLaps (notes/B-rig-laps.md): lap contract from the env cells (lap_offer:
  at start's k-th re-offer out0.ack has risen k times and is still high; lap_close;
  order consume(k-1) < offer(k) < close(k-1) < consume(k)). H_SINK_SI PROVED with a
  FIFO read map (sink_si, out0_sink_si_cells, pend_sink_si); dropping monotonicity
  alone breaks it (CXS.nonfifo_breaks_sink). For C: gcd_rig_every (every out0 result
  is gcd a b) given LapInv (CellR on shiftRun) at release and after every close;
  lapinv_at_close leaves only H_KER_REARM; but lap_cut_fails: LapInv fails at a close
  whenever the p_end loop beats out0's return (H_PEND_FAST, expected on silicon:
  2 LUTs vs 16 delay elements). With C's rearm_fails_at_reoffer neither cut works;
  every-result needs a re-entrant window theorem (C's). gcd_rig_every has no
  witness.

### progress 08:00
In: Bnx4 Necessity4Mux/MuxC/MuxN (core, checked here, axioms standard;
notes/B-necessity4.md). bd_mux.uj_env_latency_req and bdc_muxn.uj_env_latency_req
are NOT necessary: the ack C-element also waits for z_ack, so the real return path
is max(W0x.lo, W0o.lo+Lor.lo+Dz.lo+Es+Wzx.lo); the max form is proved sufficient
(mux_ok_staticN, muxn3_ok_staticN; the shipped form implies it), and runs on the
real INITs violate the shipped form by 3 ticks while meeting the full spec (pass8;
non-necessity over the box since sufficiency covers every run). On bd_mux the max
form is tight at slack 1 on its z_ack branch (fail10). uj_env_latency_ctl is
necessary at the boundary against the shipped mux_ok_static (claimC1_false).
Binary <= forms; one parameter point each, no iffs. Open: uj1/uya and muxn boundary
runs, uxa_join_latency, isochronic_forks, iso_zack, bundled_z_data.

### progress 08:04
In: Bshp KappaCPPR (Mathlib; checked here, axioms standard; notes/B-kappa-cppr.md).
Common-path pessimism in A's kappa model: common arcs cancel exactly (allOK_net);
the exact check is GenOK on the symmetric difference under H_DIV
(allOK_iff_gen_net; sandwich_net without); uncancelled GenOK is pessimistic by
exactly 2 kappa C_s (genOK_full_iff; a real-data case where it fails while the
condition holds, naive_pessimistic). Data: OnGcdArbKappa's 18 forms are exactly the
netted full conditions (fulls_net; shared by identity: the A0 stem = one fall
event, and the r_k prefix = one edge), so the gcd_hw design threshold does not
move: safe and tight on the full conditions for any r-prefix delay
(design_cppr_safe/_tight). Two of Bk3's cancellations are NOT identities (d12 in
mA/nA pairs an A0 fall with a rise, rise = fall; 7g's H_ARC_C merges two pin arcs on
equal numbers); undoing them moves fork2 on seed 4 merge12.uarb2 from 0.2165 to
0.2004 and leaves the design minimum >= 0.0443 (split_*). Missing data: r-prefix
delays, rise/fall split, LUT-internal stage sharing (an arithmetic bracket moves
only o1x/o2x).
Lead's checker had a path bug (proofwidget vs proofwidgets), fixed at 09:45;
Mathlib-closure files now check.

### progress 08:15
In (checked here, axioms standard):
- Brz ResetCapstone{,Glue,Wit} (notes/B-reset-capstone.md): B's reset connected
  to C's safety capstone. C's initial state lives in the init* fields of H_CELLS:
  all 465 channels idle at t = 0 (cap_idle0). The RTL never reaches that state:
  uenv1 and upsnk are 1 on [23(D+W+1), E] in every bounded GMW run with rst held
  (rtl_not_idle). The RTL reset state AtS (requests on channels 0..6, channel 3
  acked) is C-reachable in 3 virtual ticks (glue_cells, per cell type, side_chk
  decided for 367 operators). gcd_hw_safe_after_reset: B's GMW reset + H_MAP (C
  channel -> gNet node map) + C's gate models / bundling / start from T0 =
  23(D+W+1) give gcd a b on every out0 latch from T0. Open, named: H_MAP has no
  mechanised table (Rst2's generator is lost; only hot channels evidenced by rfl);
  H_CELLS_AFTER assumed, not derived from GMW (C's O4); H_START_AFTER inherits the
  rig re-offer caveat; the 9 bd_src-fed frontier links have no C channel; per-pin
  wire lags vs C's one trace per wire; liveness not glued. Witnesses: joint (frozen
  C family, so vacuous conclusion), C side with a result (8t run from T0 = 2,
  latches 6), and nonvac_net2 (D=40, W=1, H_STEER_HOLD live on 6 steps) replacing
  the degenerate D=W=0 reset witness.
- Bzd ZeroDelayRefine (notes/B-zero-delay-refine.md): cell half of bridge Br2 /
  C-8x, one token. Every physical behaviour of a bd_link stage, bd_steer and the
  bd_mux join (B's per-pin models) refines, by a monotone retiming of event windows,
  an explicit zero-delay run satisfying C's own Link/Steer/Mux, Protocol and Held,
  with the latched value equal at capture. Link exact: all behaviours refine iff
  the six bd_link.stage rows (link_ref_iff under Wf/Split/Causal); each 1-tick row
  violation has a non-refining behaviour. Steer/mux setup/hold counter-runs refute
  every retiming (unselected silence holds in every C run). Extra named hypotheses:
  Causal/SCausal/MCausal (environment causality), H_JOIN_RACE (sufficient), widths.
  C's handshake fields are images; its zero-delay data fields hold only as captured
  values (argued). Open: the network half, multi-token, mux zr/xa/ya/ca nodes.
- Bj6 cell_constraints.json (generator-produced; regeneration byte-identical,
  validator 0 errors, 6 planted faults -> 6 errors): 137 rows, 40 exact, 42
  boundary, 12 sufficient, 11 not_necessary (with replacement rows), 1 structural.
  Necessity4/5 applied; every strict +1 row records that it rests on H_X_UNIFORM
  (w = 1 unmeasured) with the per-edge form and wq = 0 (KleeneWin); new field
  kleene_dependence on 72 rows (KleenePess: 64 need both pass values, 6 the reset
  value, 2 pass0; safety/exclusion rows need none); rt1b kappa bracketed to 1.3e-12
  with the server-free caveat and H_SPREAD_CORRELATED.

### progress 08:21
In: Bbr ContractBridge (core; checked here, axioms standard; notes/B-contract-bridge.md).
CORRECTION to my 08:30 IpowCells entry: FbCel was described as "H_LUT_SI +
BoundedDelay feedback route + H_RT_FB". Bbr proves fbCel_iff_si: FbCel is EQUIVALENT
to the plain SI step, because its feedback-route and H_RT_FB fields are existential
and the ideal feedback (qp = o, lo = hi = 0) always satisfies them. So IpowCells'
feedback contracts carry NO timing content as stated; ipow_cells /
ipow_safe_of_contracts stand as theorems but their contracts are timing-free SI
assumptions. Fix probe (Bfc) launched: pin qp/lo/hi to the routed feedback.
Bridges proved (contract_of_contractB: ContractB implies IpowCells.Contract, so C's
proof is unchanged; ipow_safe_of_contracts' non-vacuous on the quiet run):
H_CTREE_ATOMIC from CTreeExact.tree_suff + H_CTREE_LOOP + read lower bound >= 1 +
H_RUN (any tree shape; covers ipow's 5-input join and gcd's N=5/6 fork acks);
H_SEL_PIN for steer (LibGapSteer.steer_tokens + per-pin setup/hold, H_SEL_DEC from
H_BUNDLE) and mux; ungated H_DELAY_LUMPED from a FIFO read map + H_PULSE_WIDTH
(fails for non-monotone maps, lumped_needs_fifo). H_ARB_EXCL as stated is NOT
derivable from B's per-pin arbiter (arb_excl_not_derivable via su_osc: both grants
high at some tick); it holds per arbitration inside B's QUIET/COMMIT window only,
which C's amerge proof (exclusion at every tick) cannot use. Open: H_ARB1/2,
H_AMERGE_RTZ multi-token, gated delay line.

### progress 08:32
In (checked here, axioms standard):
- Bkx18 OnNetlistArbKappaExact (Mathlib; notes/B-arb-kappa-exact.md). Audit row 18
  answered: the gap is decided for all 16 link_arb A0-fork cases (4 seeds x 2
  clients x lit/cons). In A's whole-ps CornerNat model (rational kappa and corner,
  Nat delays; Bridge restates it in A's types), exact_X: all-corner,
  all-assignment safety iff Below_X kappa, at gate level on both sides. For 15 cases
  the threshold kappa_ex is irrational (root of an explicit integer quadratic,
  approached only at an interior corner that moves with kappa, never attained); s2c2
  cons is 94/325 at the fast corner. Safe kappas form an interval (safe_antitone).
  cons: .2955 .1807 .3356 94/325 .3109 .2440 .2081 .2825; lit: .4784 .4011 .5482
  .4964 .5380 .4594 .4149 .4917 (brackets decided to 1e-10). The auditor's point is
  CONFIRMED: s1c2 cons is unsafe at 200/1103 with the auditor's assignment
  (audit_s1c2_cons_200), and also at 0.1807 where every fast-corner assignment is
  still safe (interior_s1c2_cons). Verdicts unchanged: 16/16 safe at 1/11, 15/16 at
  kappa_E. OnNetlistArbKappa itself now compiles against the real Mathlib. Not
  covered: per-tick delay variation, the A0 rise, X/metastability, kappa's value,
  the cons endpoints' provenance.
- Bov2 ArbOverlapPess (core; notes/B-arb-overlap-pess.md). The pessimistic LUT
  models do NOT explain the board's 8% bd_arbcell filtered overlap: with zero-width
  edges every policy collapses to Bov's binary rig model (w0_rig), so Bov/Bmt's
  0/192 stands under all four. With a 1 ps edge window and upwand's raw pin failing
  to pass 0 (weak0/strict), an explicit full-copy trace (real INITs, SLOW_MAX,
  Dw = 1348 ps) sets the FILTERED output from a single 305 ps raw run, with no
  overlap of the measured size (pess_fires; exactly: firing possible iff an upwand
  pin fails pass-0, fires_iff; control ctrl_kle_clean). So under weak0 the detector
  itself, not the arbiter, would produce false events. Under weak1 one request edge
  into a both-high hold puts X on q and both grants (weak1_chain); its timed
  duration is open. Not explained: the 15/192 selectivity (needs the measured
  bitstream's pin map, not archived). Board test: an AND(raw, unfoldable 0) control
  LUT per copy with locked pins.

### progress 08:35
In (checked here, axioms standard):
- Bsrv OnGcdArbKappaSrv (Mathlib; notes/B-gcd-arb-kappa-srv.md). gcd_hw arbiters at
  gate level with the server, A0 branch, ustate O6 arc and q prefix credited as
  corner-model delays (lit reading, exact on the 1 fs grid to 1e-12): (D1)
  OnGcdArbKappa's 16 forms in their server-credited versions on all 36 arbiters are
  safe for kappa <= 0.080163500491 and fail just above (binding: seed 2
  merge3.uarb1 h21). The gate counterexample is ArbPin's BARE cell (A0 held low):
  as a run of 7j's gate relations with every delay realised (server 3.8 ns) the
  overlap needs client 2 to withdraw an unacknowledged request, i.e. it is NOT a
  four-phase run; in 7j's four-phase handover the same arbiter is safe to 0.769.
  (D2) the 12 held-arbiter four-phase forms: safe for kappa <= 0.216552148868, tight
  via 7g's exact fork2_box_iff (seed 4 merge12.uarb2). cons: exactly merge3.uarb1
  h21 and o1x fail at kappa = 0 (proved). A0's driver is the ack-join C-element of
  the fork after each merge (synth netlists); srv comes from Bar's extraction (same
  untrusted provenance) and enters no binding row. Open: H_SETTLED; whether gcd_hw
  ever runs the bare (non-four-phase) race, which decides D1 vs D2.
- Bfb2 LutFbBridge2 + LutFbBridge2Env (notes/B-lutfb-bridge2.md): a C-element bridge
  for any pin count (celG_lutFb; three LUT laws decided per real INIT) gives C's
  LutFb/FbFirst for bd_c3 and bd_mux uj0/uj1; LutSI for bd_steer and bd_src (src
  needs new H_PWR_SRC); a 1-tick select glitch breaks uj0's LutFb under every
  channel hypothesis (H_SEL_STABLE needed). Environment from neighbours, per channel:
  link_link_env, fork_env. End to end: gcd_hw_safe_phys_links = C's
  gcd_hw_circuit_safe with H_CELLS for all 175 links replaced by B's physical model
  (deriving H_CEL_SI, both DI wires, inits) -- BUT each link's Env1 is still
  assumed: the circle (cell behaviour <- own Env1 <- neighbours' behaviour) is not
  closed for the network (done only for the 2-stage pipe); 150 of 350 link channel
  ends are link-to-link; C-trees open; infinite runs only.
- Bsa4 self-audit 4 (notes/B-self-audit4.md; SelfAuditB7; 18 mutants in Wip/Bsa4,
  all FAIL). All of today's files re-check; JSON regeneration byte-identical. Nothing
  refuted. Closed: H_ACK_FLUSH not necessary for EVERY DACK >= 3
  (flush_not_necessary_all); "+W under H_W_BOUND" proved for bd_steer only
  (steer_win_bound). OVERSTATED in this journal (corrections, mine):
  (1) "join +w fails under every pessimistic model" (10:15/09:10): shown for uniform
  policies only, not per-pin ones; (2) "kappa_ex - kappa* is the 1 fs grid" (09:50):
  not proved; (3) "the RTL never reaches C's idle state" (11:05): proved only for
  shifts T0 in [23(D+W+1), E] with rst held; (4) nonvac_net2 is NOT non-degenerate:
  it is frozen until E (wv_frozen); no reset witness has both moving state and
  nonzero delays; (5) H_MAP's witness map is not a wiring map: MapOK is met by a map
  reading two channels from one node (mu_W_not_wiring), so MapOK is too weak (Bmap
  told to strengthen it); (6) JSON boundary labels on +1 forms are 2 ticks from the
  refuted point (disclosed in notes); (7) bd_arbiter.rt1b's "server-free" row note
  contradicts its own inequality; (8) H_SPREAD_CORRELATED is the lit model itself
  (spread_corr_iff), i.e. a renaming, not an independent hypothesis. Also: IpowCells'
  Contract copies C's Cell fields; ZeroDelayRefine's link_ref_iff is essentially
  LinkExact.exact (LinkRef's env fields copy Beh.env); KappaCPPR's "full" conditions
  are hand-transcribed. OnGcdArbKappaTight(+A) headers corrected (bridge checks).


### progress 08:38
Correction: the progress headings from 07:28 to 08:35 in this session were first
written with wrong times (not taken from `date -u`); they are now the commit times.
Cross-references inside entries to those wrong times ("08:30 IpowCells entry",
"10:15/09:10", "09:50", "11:05") mean the entries now headed 07:48, 07:52/08:00,
07:54 and 08:15.

### progress 08:37
In: Bfc IpowCellsT (core; checked here, axioms standard; notes/B-ipow-cells-t.md).
Repairs the timing-free FbCel (ContractBridge.fbCel_iff_si): FbCelT pins the feedback
route <qp, lo, hi> as a parameter with 1 <= lo and H_RT_FB on hi; it implies C's SI
step, H_FB_FIRST on the routed pin, and FbCel. Its timing content is real and exact
(Gap.gap_exact): for a C-element whose inputs answer g ticks after its output edge,
a transport route of delay d >= 1 meets it iff d <= g (tcheck rule Rc's form), while
SI and FbCel hold for every g; at g = 0 no route meets it (si_not_fbCelT). Derived
from B's physical model for bd_c2 and the link controller (c2_fbCelT, link_fbCelT;
H_RT_FB derived) under three new named hypotheses H_WIRE_POS, H_FB_PWR, H_IN_RST.
ipow_safe_of_contractsT: C-8y's safety on timed contracts for any route assignment;
non-vacuous for every pinned bound assignment with lo >= 1 (all-quiet run) plus a
switching bd_c2 witness. Open: c3/c4/C-tree/uj0-uj1 timed bridges, routed numbers
(no ipow route exists), network-level environment (Bnet).

### progress 08:44
In: Bj7 cell_constraints.json (regeneration byte-identical here, validator 0
errors; 5 negative controls). a0_fork_client1/2 carry the 16 exact link_arb
thresholds (the row-18 validator check now allows "exact" only there, citing all 8
exact_* iffs per client); the 12 gcd_hw arbiter rows carry D1 0.0802 (bare cell, not
four-phase) / D2 0.2166 (held), D1 vs D2 open (H_SETTLED; probe Bbare), and the cons
failures; rt1b's row hypothesis now H_SERVER_MIN, matching its inequality; four stale
sentences removed; boundary_point on three +1 rows (refuted point is the <= form, 2
ticks away); H_SPREAD_CORRELATED noted as the lit model itself; "+W under H_W_BOUND"
PROVED on the 2 bd_steer rows only, 69 rows say UNPROVED; c_contract records H_ARB_EXCL
not derivable (4 rows) and H_SEL_STABLE needed (2 rows). No label changed. Not yet
audited: the other strict boundary rows (bd_mlink.qfb_first first).

### progress 08:55
In: Bzd2 ZeroDelayNet{,Phys,Wit,Tok} (core; checked here, axioms standard;
notes/B-zero-delay-net.md). Network half of the physical -> zero-delay bridge for an
N-stage bd_link CHAIN: one global retiming key(lo, depth) is monotone for free;
the closed loop with reads >= 0 gives Bzd's Causal at every stage (chain_causal,
given end causality H_SRC/H_SNK; a negative read delay breaks it with all six rows
met, negdelay_breaks_causal); every stage meets LinkExact's Spec inside the loop
(chain_spec) and chain_refines gives one zero-delay C run (Link/Protocol/Held on
every channel) with window images and captures; witness: two coupled stages, reads
380-900 ps. New hypotheses: H_WIRE_POS (>= 1 ps), H_RST_SEEN (a closed loop's wires
are not quiet at power-up), H_DATA_LOOP. One token only: k-token Link not proved;
the physical k-token stage needs a cross-token ack-before-request race that is NOT
one of the six bd_link.stage rows, and a multi-token latch capture (EnTok cannot
express it). Not done: fork/join, steer->mux diamond, rings (gcd_hw's loop has
initial tokens).

### progress 08:59
Sweep: every Formal/Cells file re-compiled against the current tree (A's and C's
pushes of today included) through the private olean build: all OK except
ArbAnalog and ArbResolve (they import Mathlib analysis modules, e.g.
Mathlib.Analysis.ODE.ExistUnique, that setup.sh has not built yet in this sandbox:
not a B failure, re-check when setup finishes) and ResetGcd (failed once during the
sweep, OK on re-run: transient, likely memory pressure from concurrent probes).

### progress 09:02
In: Bwit ResetWitness2(+Data) (core; checked here, axioms standard; notes/
B-reset-witness2.md; mutant Wip/Bwit/M1 fails). Closes self-audit 4's "frozen reset
witness" finding: a GMW run of the real gNet with D = 2, W = 1 from a pseudo-random
power-up (1593 control nodes wrong) that settles to the reset values and moves again
after release (link_moves: ulink_n68__1.ctl 1,1,0 at steps 0..2, rises at 95), with
gate delays 1, 2 and 3 observed (delays_vary). It meets H_RST_CLEAN, H_HOLD_LONG
(tight), H_RST_LOW and H_STEER_HOLD (tight at E = 158) and every hypothesis of
gcd_hw_safe_after_reset jointly (reset_capstone_nonvac2). Still: the C side of that
joint witness is the frozen family with the degenerate map muW, so the headline's
conclusion is vacuous on it; the delay family is one periodic-sampling family.

### progress 09:05
In: Bbare ArbNoWithdraw (Mathlib; checked here, axioms standard;
notes/B-arb-no-withdraw.md). D1 vs D2 for gcd_hw's arbiters, decided CONDITIONALLY:
in C's network model no arbiter request ever withdraws (gcd_hw_arb_no_withdraw, a
corollary of gcd_hw_protocol; C's cells read request and select at one instant, so
this says nothing about pin skew). At gate level the 9 arbiter stages' requests come
from link controllers, steer branches or other arbiters' R0: links do not withdraw
under LinkExact's rows (link_no_withdraw), steers under LibGapSteer's per-pin rows
plus a named H_SRC_HOLD (steer_unsel_silent, steer_no_withdraw), and a violated
steer setup row produces exactly D1's withdrawn request (steer_withdraws: a 100 ps
pulse). So D2 = 0.2166 needs the steer rows on the routes (not re-checked) AND
H_SETTLED. H_SETTLED follows from causality given a client latency L
(settled1/2_of_causal: wa0s+qf <= wa0k+ckr+L), but on the routed arcs L = 0 fails
for 65/72 clients and the need is up to 1.59 ns (settled_safe at setTbl, max
1590.934 ps; settled_L0_fails). The client-loop arcs (A_k -> client -> r_k) are not
extracted, so D2 is undecided on the routes. H_SETTLED is the rise-side twin of rule
J and NO project rule checks it (finding for the cell owner). design_gate_held_causal
= D2 with H_SETTLED discharged by L >= setTbl.
SCOPE FINDING (mine, ArbHeldTimed/ArbHeldTimed2): 7h/7j's Scn/Scn2 assert the settled
state on the whole past (H_A1_init: A1 low for every t < t0), so they cover only a
handover before which that client was never acknowledged, i.e. effectively the first
handover from reset (scn_excludes_caus). They are not vacuous, but every "held
arbiter" result built on them (RT1/RT2 exclusion, OnGcdArbKappaSrv D2,
design_gate_held) is about that one handover, not repeated ones. Barb2 (multi-token,
running) told to build a windowed Scn.

### progress 09:07
In: Bmap (checked here, axioms standard; notes/B-reset-capstone-map.md). New
directory formal/tools-B/ (shard B's generators; no other shard writes there):
gcdnet_gen.py regenerates gNet from bdc's emitted Verilog with a small Verilog front
end (vsub.py; yosys is not on PATH here) and reproduces ResetGcdNet.lean BYTE FOR
BYTE (3322 nodes; re-run by me: IDENTICAL; a one-pin mutation shows as a one-line
diff). This closes audit P5 / row 60 (lost generator) for the RTL network, which is
still the RTL, not a routed netlist. gcdnet_gen.py map builds the C-channel -> gNet
table via C's own netgen (output equal to the committed CapstoneNet.lean).
ResetCapstoneMap(+Data): names_ok (C's 465 channels, in order), mu_T_ok (H_MAP is a
theorem), gcd_hw_safe_after_reset_map (Brz's headline without H_MAP), joint
non-vacuity (C side still the frozen family: vacuous conclusion). Strengthened
WireOK (injective on wires except where the RTL makes two C wires one net: fork
output reqs, join input acks, kernel sink ack = req, mux select ack, zero-delay
links, the rig's three source reqs): mu_T_wire holds, mu_W_not_wire shows MapOK was
too weak. Open: that row c is the RTL driver of C's wire c is the generator's claim,
not a Lean theorem; H_MAP_T0, H_CELLS_AFTER (O4), H_START_AFTER, liveness.

### progress 09:11
In: Bnx6 Necessity6{Mux,MuxN,MuxJ,PipeSel} (core; checked here, axioms standard;
notes/B-necessity6.md). Boundary counter-runs (one hypothesis off by 1, real INITs,
every gate relation for all t, open-loop env) for the bd_mux uj1 max form
(claimY1_false), the bdc_muxn max form (claimN1_false, with a slower control
sender so S_J_C holds with equality), bd_mux S_XA_J.2 (claimJ1_false: a slow
j0 -> uxa wire makes x_ack oscillate through the next y transaction) and all four
per-pin H_RST_SEL terms of bd_pipe.rst_lines (rst_sel_boundary: (a)/(b) real early
fires from power-up garbage, (c)/(d) only one-tick shifts of the first edge). So
uj1_req_max, muxn uj_req_max and rst_lines become boundary-tight (JSON next Bj
pass); uxa_join_latency stays sufficient (S_XA_J.1 open). Binary <= forms; the +1
JSON forms are 2 ticks from each refuted point. Open, with an unproved analysis that
they are NOT necessary as written: isochronic_forks, iso_zack, S_XA_J.1 (bookkeeping
edges of gated-off tokens; needs a gate-aware cel_run). Not attempted: rst_flush,
bbm, muxn bundled_z_data.

### progress 09:31
In: Barb2 ArbMultiToken (core; checked here, axioms standard;
notes/B-arb-multi-token.md). Multi-token grant exclusion of the HELD bd_arbiter:
mt_exclusion (grants never both high at any t >= B0, over infinitely many
handovers, induction over handovers). The first-handover-only Scn/Scn2 of 7h/7j are
reused unchanged by splicing a stylised settled past onto the run (splice_run),
giving windowed one-handover theorems win1/win2. Hypotheses: 7h/7j's RT1/RT2/RT1b/RT2b
arc forms, H_M (M bounds every route + arc read offset), four-phase clients without
withdrawal, H_SLOW_REREQ (TA2 + 4M <= u), H_HOLD (sustained alternating contention).
C's H_ARB_EXCL holds AS C STATES IT for the held arbiter (H_ARB_EXCL_of_mt; the
ContractBridge counter-run concerns the bare cell only), and H_ARB1/H_ARB2 at 1 ps
ticks under CX (strict RT1, one-tick causality, H_GRANT_IN_A0_LOW)
(H_ARB12_of_mt). Witness: a periodic 48 ps run over all of Z, every delay nonzero,
two handovers per period. Open: early re-request (H_SLOW_REREQ excludes it; three
extra races named in the note, not proved), H_AMERGE_RTZ (B's model has no z_req),
runs from reset/idle/solo client, so C's AMerge is still not instantiated. M is
coarse: H_SLOW_REREQ and H_HOLD are sufficient, not tight.

### progress 09:36
In (checked here, axioms standard):
- Bzd3 ZeroDelayTok{,Chain,Wit} (notes/B-zero-delay-tok.md). k tokens through
  bd_link: ONE new cross-token row H_REARM (Fb1_j + Bhi <= Ra1_{j+1} + Ahi: the node
  must surely see the previous ack fall when it surely sees the next request rise;
  otherwise the real INIT holds 0). Rises need no new feedback race, the latch no
  new row (latch_tok_ok, per-token windows). sufficientK (six rows per token +
  H_REARM -> k-token spec); exact_rearm (SafeK iff H_REARM, given the six rows and the
  necessity scope GapK); 1-ps counter-run on 2 tokens (rearm_breaks). chain_specK:
  the closed N-stage chain meets the k-token spec under a new cross-stage hold
  H_DATA_LOOP_K; witness 2 stages x 2 tokens. NOT a full iff (the six rows'
  necessity inside k >= 2 is open: data must alternate); the k-token abstract C-Link
  run and rings not written. H_REARM is a new cell_constraints row
  (bd_link.stage_rearm, form in the note): JSON next pass.
- Bnet AssumeGuarantee{,Links,Fork,Cap} (notes/B-assume-guarantee.md). The cell /
  environment circle is closed by a strictly causal assume-guarantee rule (ag_time;
  measure = each node segment's end time); without strictness it is unsound
  (zero_delay_cex: two zero-delay buffers in a loop). Proved: every link's Env1 for
  a chain of any length between source/sink contracts (chain_env1, chain_lutFb), and
  for link + 2-way fork (fork_env1*, fork_envCF), live witnesses with real cells.
  ring_dead: any closed all-link ring of reset-0 links is 0 forever (a live ring
  needs a _set stage, which B's Stage does not model). gcd_hw: the 175 links form 100
  chains, no all-link cycle (census by decide); gcd_hw_safe_chains derives every
  link's Env1 from chain-end contracts (InChain). Open: the 200 chain-end contracts
  (steer 43, mux 72, join 32, forks 44, amerge 5, muxn 4) have no segment lemma;
  existence of solutions to H_TIMES not proved; infinite runs only.

### progress 09:42
In: Bset ArbSettled (Mathlib; checked here, axioms standard; notes/B-arb-settled.md).
7h/7j's H_SETTLED compared A0 at q's output with r_k at its driver; the exact
condition for the q trace is H_PIN (ta + wa0s <= t0 + wr_ks, compared at ustate's
pins; the flat O6 arc cancels). Re-proved on the real INIT with the whole RT1/RT2
exclusion chain on ScnP/Scn2P; implied by H_SETTLED and strictly weaker
(strict_witness); necessary for the q trace (q_glitch2 on every record; q_glitch
when qr = qf). Not shown: that a violated H_PIN breaks exclusion (counter-traces stop
at q's early edge). gcd_hw: the client latency it needs is <= 502.361 ps (was 1590.934
under H_SETTLED), positive on 21 of 72 clients (was 65), certified at kappa <= kappa_S2,
exact to 10 fs (settledP_safe, setTbl2_max, settledP_tight). Link-driven clients:
discharged with NO latency hypothesis on 18 of 20 instances from LinkExact's controller
model plus its O6 arc at the shared corner (design_link_discharged1/2; H_SAME_CORNER,
H_LUT6_O6); seed 3 / seed 4 merge2.uarb1 client 2 still need the unextracted ack wire
into the controller (residual 37.6 / 89.7 ps). Steer (16) and R0 (2) clients stay
conditional on unmodelled release loops. Proposed rule J+ (rise-side twin of rule J)
in the note.

### progress 09:45
In: Bj8 cell_constraints.json (139 rows: 41 exact, 45 boundary-tight, 10
sufficient; validator 0 errors; regeneration byte-identical, re-run by me).
Necessity6 rows applied; new rows bd_link.stage_rearm (H_REARM; exact for H_REARM
alone given WfK, GapK and the six rows, not the full k-token iff) and
bd_arbiter.settled_rise (H_PIN, sufficient; necessary for the q trace only; rule:
none, J+ proposed); new field handover_scope on the 13 held-arbiter rows built on
7h/7j (first handover only; rt1/rt1b point to ArbMultiToken); c_contract H_ARB_EXCL on
rt1/rt1b now needs_extra_hypothesis (derivable for the held arbiter under the
multi-token run hypotheses), bare-cell rows stay not_derivable; IpowCellsT.gap_exact
cited on the env_latency rows. Validator fix (mine): the audit-row-18 check now
matches the WORD "exact" only, so names like LinkExact or exact_* no longer trip it;
the probe had worked around it by writing "Blink's" for "LinkExact's", now reverted.

### progress 10:05
In: Bnx7 Necessity7Mux{,Runs,RunsN,N,NRuns} (core; checked here, axioms standard;
notes/B-necessity7.md). bd_mux and bdc_muxn re-proved with Lt5's gate-aware
cel_run_g (mux_ok_g/gs, muxn3_ok_g/gs). The new static set drops S_XA_FORK, S_XA_J.1
and S_OR and adds S_XA_SEQ (Wzx.hi <= Kc + W0x.lo, order only) and S_XA_R = client
loop OR (FORK AND J.1); the shipped set implies it (staticG_of_static). Passing runs
on the real INITs violate the shipped S_XA_FORK (passA5, passN5), S_XA_J.1 (passB) and
bdc_muxn S_A_FORK (passN7): those are NOT necessary. S_XA_SEQ, S_XA_R and S_A_SEQ
are boundary-tight (failSEQ6, failR6, failSEQ8). Correction to Bnx6's unproved
analysis (the Bnx6 entry above, "pure order condition"): the client loop alone is not the
replacement, because the join's fall also waits for ctl_req; the disjunction S_XA_R
is needed. Binary <= forms, one point each; the pass runs sit at binary equality and
may not survive a Kleene X window. Open: uya mirrors, muxn S_A_R boundary, muxn J.1
run, DELAY > 1. JSON next pass.

### progress 10:07
Full formal/check.sh --committed (setup.sh finished: Mathlib built from source
here): lake build of every committed Formal module (all three shards, incl. every
Cells file committed this session up to Necessity7Mux*) and the axiom audit: OK,
exit 0, no BAD declaration. The two analysis files ArbAnalog/ArbResolve, which the
private sweep could not check before Mathlib was built, are in it.

### progress 10:12
In (checked here, axioms standard):
- Bsa5 self-audit 5 (notes/B-self-audit5.md; SelfAuditB8; 14 mutants in Wip/Bsa5,
  all FAIL). All 26 in-scope files re-check; gcdnet_gen net/map and the JSON
  regenerate byte-identical (the map step depends on C's WIP Wip/C8m/netgen.py).
  Nothing refuted. MAJOR (mine): PhysLink forces the link's request to toggle
  forever (physLink_req_alternates; a request that eventually stops changing admits
  no PhysLink), so gcd_hw_safe_phys_links and gcd_hw_safe_chains only apply to runs in
  which EVERY link handshakes forever; C's witness chW violates their H_LINKS
  (chW_fails_H_LINKS*), so neither has a joint witness, and a gcd computation that
  finishes and goes quiet is OUTSIDE both. My earlier entries called this "infinite
  runs only"; its consequence is that these two theorems say nothing yet about a
  terminating gcd run. Fix probe (Bfin) launched. Also: WireOK does not pin the
  table (a 13/14 request swap also meets it: wireOK_not_unique). OVERSTATED (mine):
  h21_7j_bare's credited 3.8 ns server is inert (A0 never moves in that run);
  LutFbBridge2's witnesses are fixed-delay with constant select, two join pins carry
  one trace, muxJ1_lutFb has no witness; "H_ARB_EXCL holds as C states it" holds only
  from B0 on under perpetual alternating contention (runs from reset excluded);
  H_REARM's counter-run is a late edge relative to SpecK, not a hazard (reading);
  reset_capstone_map_nonvac uses the frozen D=40 run, not ResetWitness2's. JSON:
  a0_fork handover_scope cites Scn2 but its theorems use 7g's ArbA0Fork.Run;
  gap_exact on bd_c2.env_latency should be context, not exact_inner (next JSON pass).
- Bseg AssumeGuaranteeEnds{,Net,Cap} (notes/B-assume-guarantee-ends.md):
  net_closed_gen (per-pin dependency bounds); celG_segK for C-elements with any pin
  count on the real bd_c2 / bd_c3 / bd_c4 (correction to Bnet: forks N <= 4 are ONE
  flat LUT, not trees; only forkH5/H6 are trees; join1 is a wire); steer_segK (a
  branch firing on a token subset, H_SEL_STABLE + enumeration); mixed_closed derives
  each link's Env1 in any network of link / C-element / steer-branch specs plus
  contracts. gcd_hw_safe_net: 301/367 operators gate-modelled; contracts remain for
  the 38 steer uack ORs and all of mux 21, muxn 1, amerge 9, src 3, sink 18, fork
  trees 3. Trade-off: departure bounds and wire spacing are ASSUMED as edge-time
  inequalities, so it neither implies nor is implied by gcd_hw_safe_chains. No
  whole-net witness; the same infinite-handshake limitation very likely applies
  (link specs alternate forever) -- Bfin to check.

### progress 10:18
In: Bwb KleeneWinBound (core; checked here, axioms standard;
notes/B-kleene-win-bound.md). Generic races_suff/races_need on KleeneWin's race-list
iff shape: under the pair reading of H_W_BOUND (every pair term c_e + a_l <= W) a
+W margin is sufficient and needed (a pair at exactly W fails at W-1) for steer, the
mux join, the muxn selected join and the latch, each with a non-uniform-split
witness. The reading matters: a per-edge width bound with non-negative halves gives
+2W (tight); with halves of free sign no finite margin suffices even at width 0
(join_width_unbounded). C-element own-feedback race: the exact term is cf + wq + ar,
so the bound is +W+Wq (cel_env_win_bound/need), +2W at Wq = W, +3W under the width
reading; real bd_c2 (W=2, wq=1) clean at margin 3, hazard at 2. So the JSON's "+W"
text on the 51 C-element-backed rows is sufficient only at wq = 0 (H_FB_PURE): to fix
in the next JSON pass. The 5 *_rst_dec reset rows stay UNPROVED. W, Wq unmeasured.

### progress 10:19
In: Bpd (Phase 1, Prelim deletion; notes/B-port-core3.md; Wip/Bpd/{B.patch,AC.patch,
PrelimLutList.lean,tools/}). Every Prelim declaration has a Core/LutList namesake
(PrelimLutList: definitions equal, the 11 theorem statements the same proposition;
axioms propext/Quot.sound). With Prelim deleted, all 338 modules of its reverse-import
closure (196 Cells, 142 A/C) compile as patched copies (HEAD 0af7392; the 12 MB of
copies are kept in scratch, not committed; regenerate with Wip/Bpd/tools). Negative:
B's patch ALONE (Prelim kept, A/C unpatched) fails in 7 modules by constant mismatch
(Formal.Cells.X vs Formal.Core.LutList.X are distinct constants), so B.patch (90
files + rm Prelim) and AC.patch (17 A/C files: Core/Bridge, Core/Delay/GLSResolveGen,
Core/XAudit/Events8Arb and 14 of C's) must land in ONE commit. B cannot edit A's or
C's files, so this is handed over: FOR SHARD A (lead) / C: apply both patches in one
commit (git apply --check passes on the current tree; if not, regenerate with
Wip/Bpd/tools/mkpatch.py), then lake build + check.sh. B will not apply its half
alone.

### progress 10:19
In: Bring RingPhys{Stage,,Wit,Wit2} (core; checked here, axioms standard;
notes/B-ring-phys.md). Track 9 at gate level: bd_c2n_set is bd_c2n under complement
of pins and node (exS_dual, decide on the INITs), so its segment contract
(set_segK) and token offer at reset release (set_reset_hold) follow from a
generalised link_segK'. Mixed-polarity rings in B's bounded-delay model with NO
environment hypothesis: every node circulates forever (ring_nodes via ag_time,
ring_inf); the hypotheses force 3 <= N and 0 < D < N, i.e. C's live condition, so
physical timing adds no condition to C's (ring_k_tokens: 2t+1 <= N); with no
C-excited stage (N <= 2, D in {0, N}) the ring is frozen for every trace
(ring_frozen; ring2_dead: N = 2 is dead, not a hazard). Refinement onto C's Ring:
every toggle is a C-excited firing, every sampled state is Ring.Reach, D conserved.
Converse of ring_dead: ring_reset_live; witnesses N=3/K=1 (two laps) and N=5 with 2
tokens (2t+1 tight; N=4 with two tokens satisfies no hypothesis). This is the
project's "a ring needs three storage stages" rule proved on the real INITs under
bounded delays. Open: run existence for every 0 < D < N (shown on 2 witnesses),
the per-pin box-model ring (H_REARM), necessity of the timing rows, X power-up.

### progress 10:26
In: Barb3 ArbAMerge (core; checked here, axioms standard; notes/B-arb-amerge.md).
The held bd_arbiter's one-handover analysis on windows with the releaser's
re-request time FREE (H_SLOW_REREQ gone): exclusion on [L, Hz) for every server
under three exact races per direction (Q at ustate QB+wfb <= u+wr1s; R at R0;
G at the grant, two views; mirrors) (e_exclusion, f_exclusion). With z_req = R0
through a dz <= smin line, C's H_ARB1, H_ARB2, zr, H_AMERGE_RTZ, xa, ya hold in
OpsCM.AMerge's exact shapes at every 1 ps tick of each window under named run-form
rows (e_fields, f_fields). Each race has a slack -1 counter lemma breaking one of C's
fields; race G also a concrete from-reset counter-run (cexG_run; joint
satisfiability of the other five counter lemmas' hypotheses not shown). Race R is
not tight for exclusion: it protects H_HOLDQ. Non-vacuity: one run from reset, two
handovers, both re-requests before A0's re-rise, all delays 1 ps. C's AMerge still
NOT instantiated: reset/idle/solo/same-winner epochs, window stitching, init fields
and dat are open; idle-arbiter request races (metastability) need a separation
hypothesis that is not modelled.

### progress 10:29
In: Bj9 cell_constraints.json (145 rows; regeneration byte-identical and validator
0 errors, re-run by me). Necessity7 applied: bd_mux.isochronic_forks,
uxa_join_latency (J.1) and bdc_muxn.iso_zack not_necessary with replacement rows
uxa_seq/uxa_r/ua_seq (boundary) and uya_seq/uya_r/ua_r (sufficient; the uya rows are
mirrors without runs). KleeneWinBound applied: "+W under H_W_BOUND" now backed on
steer/join/muxn/latch rows (sufficient + needed, pair reading), the 51 C-element rows
say +W+Wq; 5 reset rows stay UNPROVED. Self-audit 5 JSON items fixed (a0_fork scope
cites 7g's Run; gap_exact role context; H_ARB_EXCL basis "from B0 on, perpetual
contention"). Validator: name regex now accepts Lean names ending in a prime and no
longer lets Foo match Foo.bar; the +W check generalised to the family theorems.

### progress 10:30
Audit (claude/audit fb4df88, passes 9-10): rows on B are CONFIRMED except:
- Bj5 JSON (9372e3b): 2 labels mildly OVERSTATED: bd_arbcell.handover_overlap is
  labelled exact but backed by equality formulas, not an iff; bd_arbiter.rt1/rt1b
  "exact" with necessity only conditional on a supplied run (pre-existing). Agreed:
  both to be relabelled in the next JSON pass (Bj10).
- LutFbBridge "every bd_c2 in OpsGen": scope narrower (not join3, not mux uj0/uj1;
  disclosed). Since closed by LutFbBridge2 (join3_lutFb, muxJ0/1_lutFb; muxJ1 has no
  witness, self-audit 5).
- ArbNoWithdraw: 3 of the 18 arbiter inputs come from forkG (channels 151, 207, 408),
  not only link/steer/R0 as my 08:xx entry says; and the producer census is a netlist
  claim, not in Lean. Agreed: correction recorded here; forkG producers are C-element
  forks, whose no-withdrawal follows from celG (not yet stated as a theorem).
- ResetCapstone: "content thin" (the RTL -> C link is state equality at T0 only, C's
  gate models assumed after T0; conclusion vacuous on the witness): agreed, as stated.
- ContractBridge's H_ARB_EXCL counter-run is the binary model's endless oscillation,
  not evidence that silicon overlaps: agreed (it is a model counter-run).

### progress 10:45
In: Bfin FiniteRuns{,Wit,WitData} (core; checked here, axioms standard;
notes/B-finite-runs.md). Confirms gcd_hw_safe_net has the same restriction as the
two link theorems (gcdNetOK_req_alternates; chW meets no GcdNetOK, chW_no_gcdNet).
Finite forms: FEnv1 / FEnvG / FPhysLink are Env1 / EnvG / PhysLink with finite edge
counts (0 allowed; each pin constant after its last edge; same per-phase timing);
the bridge is re-proved (flink_lutFb, fcelG_lutFb, flink_link_env, link_of_fphys).
gcd_hw_safe_fin_links = gcd_hw_safe_phys_links with FPhysLink per link, and it now
has a JOINT non-vacuity witness on a real terminating gcd run: C's chW (a=12, b=18,
quiet after 476 ticks, out0 latches 6) meets FPhysLink on all 175 links (34 never
see a request), kernel-checked through a checker with proved soundness, together with
C's H_CELLS for the other 192 operators, H_BUNDLE and H_CM_FORCED
(gcd_hw_fin_links_witness). Caveat: chW is C's unit-delay simulation, so every B
window is met at width 0 (lo = hi = 1), not at a prjxray band. Open: the network
closure in finite form (finite chain_env1 / mixed_closed): a quiet run's last
segments never end, so ag_time's end-time measure fails; needs time-truncated segK
lemmas. So the link Env1 is still assumed per link in the finite theorem.

### progress 10:48
In: Bedge EdgeTimes{,Net,Ring} (core; checked here, axioms standard;
notes/B-edge-times.md). The edge-time equations now have CONSTRUCTED solutions:
chains (chain_solution / chain_exists): for every N and every constant per-gate
delay inside the bands meeting ChainT, a transport run on the real bd_c2n INIT
satisfies all of Chain/ChainT, with edges = the max-plus schedule; so chain_env1 is
non-vacuous for all such delays (chain_env1_solution). chain_as_net derives, for link
chains, the departure bounds and H_SP that AssumeGuaranteeEndsNet assumed. Rings
(ring_solution, ring_run_iff): for every N and reset pattern b, a run with PRing and
PRingT exists IFF 0 < D < N (closes RingPhys's existence gap; recursion ordered by a
potential rising by D / falling by N - D across channels). Open: the exact ring edge
time (proved within one tick of cph + d), no cycle-time theorem, departure bounds for
mixed networks (forks/joins/steers), edge-to-edge varying delays, uniqueness.

### progress 10:55
In: Bmux2 AssumeGuaranteeMux{,Or,Net} (core; checked here, axioms standard;
notes/B-assume-guarantee-mux.md). bd_mux's uj0/uj1 (muxj_segK; gated control +
token enumeration), uxa/uya (muxa_segK: hold through the other input's z_ack tokens
under exactly H_SNDZ and H_ZFALL, muxa_conds_tight), the udly buffers and bd_src
(src_segK, H_PWR_SRC) are gate-level cell specs on the real LUTs with witnesses;
bd_snk has no cell (a wire). gcd_hw_safe_net2: contracts remain only for the 59 ORs
(38 steer uack, 21 mux uor), muxn 1, amerge 9 and the 3 fork trees (op_classes2).
NEGATIVE: or_not_causal -- an OR's low segment needs a prefix of the idle branch's
later-ending segment, so the end-ordered segment rule cannot discharge any OR under
any dependency bound; closing them needs the time-indexed rule Bfin2 is building
(told to include OR and mux prefix lemmas). Same limits as before: infinite runs,
departure bounds as edge-time inequalities, no whole-net witness.

### progress 10:59
In: Bj10 cell_constraints.json (151 rows, 38 exact; regeneration byte-identical and
validator 0 errors, re-run by me). Audit P9 rows fixed: bd_arbcell.handover_overlap
exact -> sufficient (closed-form equalities; its only iff describes one supplied
trace); bd_arbiter.rt1 exact -> sufficient (necessity only for a supplied run; no
violating run exists in Lean); rt1b exact -> necessary_at_instance (the constructed
run OnGcdArbKappaTight.SU). New rule in conventions.exactness: a necessity label
needs an iff or a constructed run; the validator now requires every exact row to
cite, with role exact, a theorem whose statement is an iff (it caught exactly these
three). Six early re-request rows (ArbAMerge races Q/R/G + mirrors): only G's rise
view is boundary-tight (cexG_run); the others' cex_* lemmas have no constructed run,
so sufficient; each necessity is for one C field; race R protects H_HOLDQ.
H_SLOW_REREQ is not needed within one handover window but stays in the all-time
contract (windows not chained). Necessity5 needed no change (merged at Bj6).

### progress 11:11
In: Bfin2 FiniteNet{,Cells,Mixed,Wit} (core; checked here, axioms standard;
notes/B-finite-net.md). The strict-causality induction re-timed from segment ends to
TIME: ag_trunc (pins clean on [0,T) => node clean on [0,T+lo), lo >= 1, induction on
T; unsound at lo = 0 on the zero-delay loop). One notion GPhT covers finite and
infinite runs (gph_fin_iff, gph_inf_iff). Truncated cell lemmas need no spacing and no
H_WAIT: tnode, twire, tlink, tcelG/tcelX, tgated/tsteer/tmuxj, and the OR cells
tor_ex/tuack/tuor (the end-ordered rule could not carry them, or_not_causal; under the
time rule they close given H_ORD; H_LATER gone). fchain_env1 DERIVES each link's FEnv1
on runs that stop; gcd_hw_safe_fin_chains replaces FPhysLink by FInChain, and C's
terminating run chW (a=12, b=18, out0 = 6) meets ALL its hypotheses jointly
(gcd_hw_fin_chains_witness). So this is the first B theorem with derived link
environments that has a joint witness on a real gcd run. Degenerate in three ways
(disclosed): each witness chain is a single link (producer node -> link -> consumer
node), the end contracts hold because their conclusions hold on chW, and all delays
are unit. gcd_hw_safe_fin_net also gate-models the 38 steer ORs, but has no joint
witness (chW has channel traces, not internal nodes). Still contracts: mux acks,
sources, muxn, amerge, fork trees N >= 5; departure bounds and H_ORD assumed.

### progress 11:28
In: Bcr ArbCounterRuns{,AM} (core; checked here, axioms standard;
notes/B-arb-counter-runs.md). Constructed violating runs (real INITs, every gate and
server relation for all t, nonzero delays, missing the condition by exactly 1 ps, the
existing counter lemma applied) for bd_arbiter.rt1 (race disjunct; record inside the
routed box of gd_merge9_uarb1 with a free A0 route / ustate arc / server: 170 ps
server overlaps 1 ps, 171 ps excludes), bd_arbcell.handover_overlap (a Cell trace for
every arc record, so the 7e condition is an iff on constructed runs; the SLOW_MAX
instance needs a 171 ps O6 rise/fall asymmetry H_RF_ASYM, unmeasured, so at
consistent corners the overlap stays 0), and the six re-request race forms Q, R, G
(fall view), Q2, R2, G2 from reset. Findings: Q2's runt circulates in ustate's hold
loop when qr = qf (both acks high for 12 ps on its four-phase continuation); Q's run
ends only because qf > qr; G's fall view needs a q-pin rise/fall difference. Race
records are a 1-4 ps grid, not routed numbers. JSON next pass (labels to
boundary-tight per field).

### progress 11:30
In: Bmn AssumeGuaranteeMuxN{,Tree,Fin,FinWit,Net} (core; checked here, axioms
standard; notes/B-assume-guarantee-muxn.md). muxn and the fork trees are cell specs:
decode LUT3 (dec_segK / tdec; per-bit H_SEL_STABLE, H_S_RANGE, named H_YOSYS_MAP for
the inferred LUT3), joins = bd_c2, acks via MuxASpec plus a new truncated tmuxa that
also closes bd_mux's uxa/uya (H_ZFALL now requires the earlier z_ack fall to have
happened). Fork trees: every node a CelSpec / FCelSpec, inner departure bounds derived
from the leaves' bound relative to the root (sufficient, not CTreeExact's exact form);
bd_fork_N5's LUTs kernel-checked; N=6's node INITs from the bd_ctree RTL recursion
(named H_TREE6_MAP, no generated netlist). The 11 FASTFALL stages of muxn's delay
line are not segment-causal (gstage_not_causal) but are carried by the time rule
(tand, under H_SAME / H_OVL). gcd_hw_safe_net3 (segment form) leaves contracts on the
59 ORs, muxn's |j and 11 stages, and the amerges; gcd_hw_safe_fin_net3 (runs that
stop) leaves ONLY muxn's |j (a 3-input OR), the 3 sources and the 9 amerges. No joint
witness of either network theorem yet (Bfin3); tree / decode truncated witnesses are
infinite runs only; departure bounds still edge-time inequalities.

### progress 11:33
In: Barb4 ArbAMergeRun{,Stitch,Wit} (core; checked here, axioms standard;
notes/B-arb-amerge-run.md). C's OpsCM.AMerge is INSTANTIATED for the held bd_arbiter
with all 13 fields at 1 ps ticks (amerge_of_plan), for any schedule in the class Plan
(reset; grant from idle; handovers with early re-request; solo / same-client
re-request; release to idle; the idle race; hold), with dat the one remaining
hypothesis (H_DAT: B has no data-mux model). New windows WG/WR/WX/hold with a generic
stitching lemma (stitch_run, win_step, run_fields); init fields from the reset epoch.
Two new races: RA1 (ua1 feedback vs the re-request's grant; cex_RA1 breaks xa at
slack -1, universal only, no run) and H_SEP for an idle arbiter (requests separated by
more than the loop at ustate, R0 and g1): sep_cex_run is a from-reset run missing H_SEP
by 1 ps in which q, g1, g2 make runts and both H_ARB1 and H_ARB2 fail -- the digital
form of "an arbiter needs its requests separated, or it can glitch", with no
metastability filter. Non-vacuity: amerge_witness, one from-reset run covering every
epoch kind, checked at all t. Open: client-2 / q = 0 mirrors (the class is one-sided),
a waiter arriving mid-release, counter runs for H_SEP's R/G clauses and the rows;
epoch hypotheses are numeric per epoch, not derived from arcs; the server reads R0.

### progress 11:33
In: Bj11 cell_constraints.json (151 rows; 38 exact, 56 boundary-tight, 10
sufficient; regeneration byte-identical, validator 0 errors, re-run by me): rt1 (race
disjunct only; free A0 route / ustate arc / server noted), handover_overlap (needs
H_RF_ASYM; at consistent corners still 0) and the five re-request rows Q/R/Q2/R2/G2 ->
boundary-tight on their constructed runs (one C field each); rereq_G's fall view now
has a run too.

### progress 11:51
In (checked here, axioms standard):
- Bsa6 self-audit 6 (notes/B-self-audit6.md; SelfAuditB9; 10 mutants in Wip/Bsa6,
  all FAIL). All 35 in-scope files re-check; JSON byte-identical. Nothing refuted.
  MAJOR (mine, Lean): FGcdNetOK / FGcdNetOK3 fix tied cells' PIN traces but NOT
  their drivers, and the cell set is free; a pinless cell's contract is the bare claim
  that its node is clean (fcellOK_nil_iff), and a link fed by two such cells gets
  FEnv1 from them alone (flink_env1_local). So gcd_hw_safe_fin_net / _net3 do NOT
  enforce that any link's environment comes from the gate models. CORRECTION to my
  Bseg/Bmux2/Bmn/Bor3 entries: "contracts remain ONLY on muxn's |j, 3 sources, 9 amerges" (Bmn,
  Bor3) and Bseg/Bmux2's "gate-modelled" counts: they describe the INTENDED
  elaboration, not what the theorem enforces. Fix probe (Belab: bind every pin's
  driver to the generated netlist) launched. Also: the fin_chains witness on chW is
  a re-labelling (single-link chains whose end nodes are the link's own pins one tick
  early; per-link chains share nothing); ring_run_iff's 0 < D half is the hypothesis
  H_TOK (htok_iff_D; only D < N derived); the validator's iff check is syntactic
  (3 JSON mutants citing unrelated iffs pass; sampled 12 exact rows are fine).
  amerge_of_plan CONFIRMED (C's own AMerge, H_DAT the only extra; one unit-grid
  inhabitant).
- Bfin3 FiniteNetWit2{Lib,Data,Chk,} + FiniteNetSrc (notes/B-finite-net-wit2.md).
  gcd_hw_safe_fin_net has a joint witness on chW (gcd_hw_fin_net_witness: 377 tied
  cells' node traces simulated on the real LUTs and kernel-checked), but degenerate
  exactly as Bsa6 says: the non-link cells' nodes drive nothing. And it CANNOT be
  wired on chW: chW_steer_unwired (C's gates take one tick channel to channel; a B
  LUT plus wire take at least two, so 38 of 53 firing steer branches cannot be driven
  by any real bd_steer node). tsrc proved; chW_src_unwired: a real bd_src never lets
  a gcd run stop (its LUT asks for another token), so sources stay contracts on
  terminating runs. Python only (not Lean): B's gate network at LUT delay 2, wires 1-3
  (3 seeds) computes out0 = 6 and passes C's step checks (negative control flagged).
- Bor3 FiniteOrN: n-branch truncated OR (tor_exN; 2-branch tor_ex as a corollary);
  the muxn |j LUT3 8'hFE is the 3-OR for every pin order and the only LUT3 INIT that
  is (or3_init_unique); gcd_hw_safe_fin_net3' adds it (same elaboration caveat).

## Session Sat Oct 31 07:14:00 UTC 2026

### progress 07:14
Took LOCK-B (previous B lock 2026-10-29T11:51, 43 h stale). The 2026-10-29 probes
that had not landed by its last commit (Belab and anything else running) are not
claimed. Audit read (passes 12-13): rows on B are P12b (row 22, OVERSTATED:
Bfin2/Bfin3 "FEnv1 derived"/"joint witness"; claims 2-6 CONFIRMED, SelfAuditB9's driver
finding confirmed and found broader) and P13 (lap_cut_fails, stF_runt, arb_eternal
CONFIRMED). Fixes now: the status table row above rewritten (no network theorem binds
drivers; H_OTHER keeps C's H_CELLS for 192 operators; the JSON count corrected to Bj11's
151/38); CAVEAT paragraphs added to the docstrings of all eight network/chain theorems
(gcd_hw_safe_chains, _fin_chains, _net, _net2, _net3, _fin_net, _fin_net3, _fin_net3').
Answer to P12b row 22: AGREED. "fchain_env1 DERIVES each link's FEnv1" (11:11) and
"first B theorem with derived link environments that has a joint witness" are
WITHDRAWN: the derivation is from per-link end contracts with Env1's content, and the
chW witness is a relabelling of the link's own pins. The same applies to Bnet's
gcd_hw_safe_chains (10-28/29 entry "derives every link's Env1 from chain-end
contracts"). Next: a driver-bound network hypothesis (FiniteNetBound).

### progress 07:33
In (core Lean; checked here through the private olean build formal/tools-B/privbuild.py,
`lean -DautoImplicit=false -o` over the 128-module Mathlib-free closure, through slot.sh;
`#print axioms` standard; Mathlib/lake build of setup.sh still running):
- Belab FiniteNetBound (notes/B-finite-net-bound.md). FGcdNetOKB = FGcdNetOK with every
  tied cell's pin drivers bound to the cells the NETLIST names (reqSrc/ackSrc, computed from
  C's opAt/prodOf/consOf: producer link / steer branch / 2-join through forks; consumer link /
  steer OR / fork C-element through 2-joins), and the steer OR's pins tied to the branch
  acknowledges. Proved: reqSrc_tied/ackSrc_tied + tied_pins_ne (a netlist-named driver is a
  tied cell with pins, so its contract is a gate model, not the bare pinless claim);
  link_env_bound; bound_census (kernel): of 175 links, 63 bound on both sides, 64 request
  side only, 23 acknowledge side only, 25 neither (the other side is a mux, muxn, amerge,
  source, 1-input join, or a fork/join chain ending at one); gcd_hw_safe_fin_netB.
  NOT shown: joint satisfiability (no witness; chW cannot carry it, chW_steer_unwired). The
  proof is the old one through toOK: binding narrows the hypothesis, it adds no derivation.
  The notes record why a witness needs (1) a re-simulated run with tied gates at LUT 1 +
  wire 1 (uniform dilation of chW fails: links would need 4 ticks, the rest 2) and (2) a
  fix in B's specs: H_TIMES and the checkers' driver hypothesis are "for every edge index",
  which bound drivers cannot meet past the last edge. Mutant (link reqSrc -> .fa) fails.
- Blcw RigLapsWit: the auditor's P13 instance of lap_cut_fails taken into the library
  (lap_cut_fails_instance; auditor's construction, credited). Shows consistency of the
  hypotheses on a channel map that is not a gcd_hw run.

### progress 07:35
Bwit step 1 (Python only, UNTRUSTED; formal/tools-B/bwit/bsim.py, output bsim.out): a
GATE-TIMED gcd_hw run for the driver-bound network exists in simulation. C's unit-delay
simulator (tools/capwit/sim.py, imported read-only) with every B-tied operator given an
explicit node (fork N=2..4 ack C-element, 2-join request C-element, steer branches, steer
OR: node(t+1) = excitation(t), channel = node one tick later; links already LUT 1 + wire 1):
a=12,b=18 quiescent at 589, out0 closes at 585 with 6; C's own Python checker (every Cell
field, Held, start once) 0 violations; all 441 bound tied pins (FiniteNetBound's
reqSrc/ackSrc re-implemented) are exact delayed copies of their bound driver's node, wire
delay 1 (362), 2 (74), 3 (5) (fork outputs and join input acks are longer wires).
Also a=27,b=6 (gcd 3): same. Negative control (--neg, steer branch drivers swapped): 63
pins flagged. So the obstruction chW_steer_unwired is a property of C's run chW, not of C's
models: C's operator models are speed-independent and accept B's 2-tick gates. Not yet
Lean. Lean needs (notes/B-finite-net-bound.md): the checkers of FiniteNetWit2Lib with pin
wires w in {1,2,3} and bound drivers, and H_TIMES restricted to existing edges.

### progress 07:39
In: Bwit step 2, BWitData (GENERATED, tools-B/bwit/gen_cdata.py --check ok) + BWitCells
(core Lean; checked here by private olean build, axioms standard). The gate-timed run chB
(a=12, b=18; B-tied operators take 2 ticks channel to channel) meets C's capstone
hypotheses JOINTLY, decided by C's own checkers by kernel: b_cells (H_CELLS, all 367
operators), b_held (H_BUNDLE), b_start_once, b_forced (H_CM_FORCED via C's
gcd_hw_forced with C's token walk yW), b_out0 (out0 closes at 585 carrying 6); b_joint
packages them. Mutant (channel 0's first request toggle 0 -> 1) is rejected by the cells
check. So chW is not the only C witness, and C's models accept B's gate timing. This is
C-level only: B's network on chB (FGcdNetOKB with bound drivers) is step 3, which needs
H_TIMES restricted to existing edges (notes/B-finite-net-bound.md).

### progress 07:42
In: H_TIMES restricted to EXISTING edges (`∀ j, L c j → ...`) in FiniteNetMixed's four
finite-run specs FLinkSpec, FCelSpec, FSteerSpec, FOrSpec (was `∀ j`). Edge times past a
cell's last edge mean nothing physically, and the ∀-form cannot be met by a network whose
tied cells drive each other (a driver's edge function would have to equal its pin list
past the end). New gphT_congr (a truncated step signal reads its edge function only at
existing edges) carries the four cell lemmas and flink_spec_env1; producers adapted
(FiniteNetWit2Lib, AssumeGuaranteeMuxNFin, SelfAuditB9). This WEAKENS a hypothesis, so
every theorem using these specs is at least as strong as before. All 12 dependent modules
re-check (private olean build, 140-module closure).

### progress 08:12
In (core Lean; private olean build, 130-module closure, axioms standard):
Bwit step 3 -- the DRIVER-BOUND gate-level gcd_hw theorem has a joint witness.
BWitLib (wire_map/gE_map: event-list wires of any delay; celB_spec'/stB_spec'/orB_spec'/
linkB_spec': Bfin3's checkers with pins at any wire delay from a bound driver, edges read
at existing edges only, node edge times checked as data), BWitNDefs + generated BWitNData
(tools-B/bwit/gen_bdata.py --check ok: per-channel pin wire delays, steer token tables),
BWitNChk (kernel: every channel's two pins are wires of the netlist-named driver's node,
every link / fork / join / steer / OR cell passes its checker), BWitNet:
- bwit_ok : FGcdNetOKB chB NBn LB nB. Every tied cell's node IS the channel signal it
  drives, one tick early; every tied pin is driven by the cell reqSrc/ackSrc names, through
  wires of delay 1-3; contract cells (one per channel signal) drive only pins whose netlist
  driver is an untied operator.
- gcd_hw_fin_netB_witness: chB meets FGcdNetOKB AND C's H_OTHER, H_BUNDLE, H_CM_FORCED
  jointly, out0 latches 6; gcd_hw_fin_netB_consistent applies gcd_hw_safe_fin_netB.
- bwit_link_env: on the witness, the 63 both-side-bound links' pin drivers are tied
  gate-model cells with pins.
So gcd_hw_safe_fin_netB is NOT vacuous, and unlike Bfin3's witness the gate-modelled
nodes DRIVE the network: tied guarantees feed tied assumptions (link -> link, steer ->
link, fork C-element -> link ack, ...). Needed on the way: NB (event horizon of B's list
checkers) 480 -> 640, old witnesses re-check.
NOT covered: one run (12, 18), unit LUT delay and simulator-chosen wire delays 1-3 (no
delay band exercised, windows met at width 0), R = 2; contract cells' contracts hold
because their nodes are clean (at the 112 unbound link sides and every pin driven by an
untied operator); C's H_OTHER for the 192 non-link operators is still assumed by the
theorem and here discharged only on this run by C's checkers. Negative control: channel 20's request wire delay 2 -> 1 in
BWitNData makes bw_c1 fail by kernel.

### progress 08:32
In: BWitNet.Rej.chW_net_not_bound (self-audit; axioms: propext): Bfin3's network on chW
(the one fgcdNetOK_chW witnessed, and the audit called a relabelling) does NOT meet
FGcdNetOKB: link 194's request pin (channel 13) is driven there by channel 13's pinless
contract cell, while the netlist names link 193. So the binding excludes exactly that
degeneracy. Paste block for A updated (notes/B-gcd-hyps-for-A.md).

### progress 08:36
Bwit2 step 1 (Python only, UNTRUSTED; tools-B/bwit/bsim2.py, bsim2.out): bd_mux
gate-modelled as well (uj0/uj1 C-elements of x/y request and gated control, uor, the two
udly buffers, uxa/uya C-elements of the join and z_ack; LUT 1 and wire 1 on every internal
pin; ctl_ack = z_ack). C's mux model takes its internal j_b := B's join node 6 ticks late
(the j -> uor -> udly -> udly -> z_req path). a=12,b=18: quiescent at 690, out0 = 6 at 687;
C's checker 0 violations; 620 bound tied pins, all wire-delayed copies of their netlist
driver (w 1/2/3); with muxes bound, links bound on BOTH sides rise from 63 to 124 of 175.
Negative control flags 63 pins. Lean for this needs mux cell checkers (muxj/muxa/buf; or
exists) and NB >= 691.

### progress 08:41
In (core Lean; private olean build, axioms standard): Belab2 FiniteNetBoundM. bd_mux
gate-modelled and bound too (FGcdNetM = FGcdNet + mj/ma/md/mo; reqSrcM: mux output
request <- last udly buffer; ackSrcM: x/y ack <- uxa/uya, control ack <- z's driver
(ctl_ack = z_ack); inside the mux uor reads the joins, udly[0] uor, udly[1] udly[0],
uxa/uya their join). bound_censusM (kernel): 124 of 175 links bound on BOTH sides (was
63), 25 request only, 25 acknowledge only, 1 neither. FGcdNetOKBM.toOK (mux contracts from
Bmn's specs), link_env_boundM, gcd_hw_safe_fin_netBM. Bmn's FMuxJSpec / FMuxASpec /
FBufSpec H_TIMES also restricted to existing edges (no producer existed; 5 dependents
re-check). NOT yet: a joint witness of FGcdNetOKBM (Python evidence bsim2.py only; Lean
needs muxj/muxa/buf checkers and NB >= 691). Until then gcd_hw_safe_fin_netBM is reported
as possibly vacuous.

### progress 09:01
In (core Lean; private olean build, 142-module closure, axioms standard): Bwit2 -- the
MUX-EXTENDED driver-bound theorem FiniteNetBoundM.gcd_hw_safe_fin_netBM has a joint
witness. BWit2Data (gen_cdata2.py --check ok; run of bsim2.py, every bd_mux cell
gate-modelled, quiescent 690, out0 = 6) + BWit2Cells (C's checkers by kernel: H_CELLS,
H_BUNDLE, start once, H_CM_FORCED via yW); BWit2Lib (bufB/mjB/maB with soundness into
Bmn's FBufSpec/FMuxJSpec/FMuxASpec); BWit2NData (gen_bdata2.py --check ok: wire delays,
token tables, internal mux node lists uj0/uj1/uor/udly[0]); BWit2NDefs/BWit2NChk (kernel:
every channel's pins are wires of the reqSrcM/ackSrcM-named driver, every link/fork/join/
steer/OR and every mux's 7 cells pass their checkers); BWit2Net: bwit_okM, 
gcd_hw_fin_netBM_witness (with C's H_OTHER, H_BUNDLE, H_CM_FORCED; out0 = 6),
gcd_hw_fin_netBM_consistent, bwitM_link_env (the 124 both-side-bound links take both
environment pins from tied gate-model cells). NB raised to 768 for this run (old
witnesses re-check). Same limits as Bwit: one run, unit LUT delays, simulator wires 1-3,
R = 2, contracts at muxn/amerge/sources/sinks/join1/fork trees, H_OTHER still a hypothesis
of the theorem. Negative control and full lake build next.

### progress 09:25
formal/check.sh --committed at 4dc79b4b: textual scan, lake build
"Build completed successfully (3638 jobs)" (Mathlib built from source by setup.sh in this
sandbox, 6158 s; setup.sh's own build had failed only because I edited files during it),
axiom audit "[check] OK". So everything committed today is in a green check.sh, not just the
private olean build. The Bwit2 negative control (one uj0 node edge +1) was killed by the OOM
killer while lake ran (rc 137); re-run pending.

### progress 09:46
In (lake build, 146 jobs, OK): the steer and mux select traces are now bound to the data:
FGcdNetOKB.H_STEER and FGcdNetOKBM.H_STEER/H_MUXJ require s = bit 0 of the control
channel's bus (in FGcdNetOK the select trace s was a free existential). Both witnesses
meet it by rfl (selB = bit 0 of chB's bus).

### progress 09:59
In (lake build, 143 jobs, OK): reqSrcM/ackSrcM trace through 1-INPUT JOINS (they have no
cell; bdc emits them as wires both ways). bound_censusM now 136 of 175 links bound on both
sides, 15 request side only, 24 acknowledge side only, 0 neither; the remaining unbound
sides end at an amerge (23 request + 5 acknowledge), muxn (4), fork tree N >= 5 (6) or the
source (1). The mux-extended witness (BWit2Net) re-checks with the regenerated wire data
(gen_bdata2.py --check ok; bsim2.py: 657 bound pins, all wired, w 1-3; bsim2.out).

### next (for the next B session)
- Remaining unbound link sides (FiniteNetBoundM census): amerge 28 (needs finite-run cell
  specs of bd_arbiter's ustate/ugrant/ua1/ua2 with the race hypotheses of ArbAMergeRun:
  the real frontier), fork trees N=5/6 6 (FTree5/FTree6 exist; checkers = celB), muxn 4
  (FDecSpec/FAndSpec/FOrN exist; no Bool checkers), source 1 (cannot be gate-modelled on a
  terminating run: FiniteNetSrc.chW_src_unwired).
- The witnesses use unit LUT delays and simulator-chosen wires; a witness on routed delays
  needs gcd_hw's routed SDF on disk (not here) and checkers with lo = hi = d.
- C's H_OTHER (192 non-link operators) is still a hypothesis of every network theorem; for
  forks, C's Fork.wire relates the fork INPUT request, which no B cell reads (a fork is a
  wire), so it is a modelling choice of C's, not physics B can derive.

### progress 10:01
In (lake build OK): FiniteNetBoundMCensus (kernel): the 24 unbound request sides end at an
amerge (23) or the source (1); the 15 unbound acknowledge sides at muxn (4), amerge (5),
forkH5 (4), forkH6 (2). So the arbiter is the one class that matters for full binding.

### progress 10:08
Bwit2 negative control (re-run alone): the first uj0 node edge of the first mux in
BWit2NData moved by +1 tick makes BWit2NChk's bop_c1 fail by kernel ("application type
mismatch" on the decide proof). The checks bite on the internal mux nodes too.

### progress 10:40
formal/check.sh --committed again on the branch head after all of today's B commits (and the
other shards' pushes so far): "Build completed successfully (3663 jobs)", axiom audit
"[check] OK".

### progress 11:10
In (lake build OK: BWitNChk, BWit2NChk, then BWitNet, BWit2Net, FiniteNetBoundMCensus;
the two kernel-check modules must be built one at a time on this box, parallel lake was
OOM-killed): every tied cell now DRIVES its own output channel in the hypothesis
(H_DRV_FORK/JOIN/STEER in FGcdNetOKB, plus H_DRV_MUX in FGcdNetOKBM: fork C-element ->
input ack, join C-element -> output req, steer branch -> branch req, steer OR -> input
ack, mux udly[1] -> z req, uxa/uya -> x/y ack; links already had LinkOut). Before, a tied
node was connected to its output channel only where the channel's reader was tied, so a
steer feeding an amerge could drive nothing. Both witnesses meet the new fields (the node
is the channel one tick early: wire_shift).

### progress 11:11
In (lake build OK): FiniteNetComb -- FCombSpec, a truncated spec for a LUT whose
correctness is a race (the arbiter's ustate/ugrant): the real LUT F of its pins through Win
+ H_NO_REVERT, and one named hypothesis H_EXC_CLEAN (clean pins on [0,T) give a clean
excitation with stated edges). fcomb_spec_cell: it meets FCellOK, so such cells can join the
bound network; fcomb_of_buf: a buffer is an instance (H_EXC_CLEAN = the pin's own
cleanliness). Building block for notes/B-arb-bind-plan.md; no arbiter instance yet.

### progress 11:13
Bwit3 step 1 (Python only, UNTRUSTED; tools-B/bwit/bsim3.py, bsim3.out): the ARBITER at
gate level too. bd_arbiter's four cells from the real INITs (ustate O6 q: frozen while A0
is high, else set by a sole r1, cleared by a sole r2, held on a tie or no request, reset to 1;
ustate O5 R0 = q ? r1 : r2; ugrant g1 = r1 & q, g2 = r2 & !q; ua1/ua2 = C(g, A0); decoded
in Python and checked against the INIT words for all 32 rows, 0 mismatches), LUT 1, the q pin
a unit wire; C's internal g1/g2 := B's ugrant nodes (no shift: z.req = R0 one tick later
equals g1 | g2 at the same pins). a=12,b=18: quiescent 716, out0 = 6; C's checker
0 violations (C's AMerge: H_ARB1/2, exclusion, zr, RTZ, xa/ya); with the arbiters bound
(z.req <- R0, x/y ack <- ua1/ua2), 728 bound pins, all wire copies of their netlist driver,
and 164 of 175 links bound on BOTH sides. The arbiters are uncontested on this run, so no
race window is exercised. Lean for this: FiniteNetComb.FCombSpec for ustate/ugrant (its
H_EXC_CLEAN is decidable on the run), FCelSpec for ua1/ua2; not done this session.

### progress 11:16
In (lake build OK): FiniteNetBoundA -- the arbiters gate-modelled and bound. Each amerge is
bd_arbiter's four real cells from C's generated netlist (ustate O6 q and O5 R0, ugrant
O5 g1 / O6 g2 as FiniteNetComb.FCombSpec: the real LUT of the bound pins [r1, r2, q(, A0)]
plus ONE named race hypothesis each, H_EXC_CLEAN; ua1/ua2 as FCelSpec GC2 of the grant and
z_ack); reqSrcA/ackSrcA = M's drivers or else the arbiter (z.req <- R0, x/y ack <- ua1/ua2)
through the same wires; the arbiter cells drive z.req and x/y ack (H_DRV_ARB). FCombSpec
now takes the reset as an input of F. bound_censusA (kernel): 164 of 175 links bound on BOTH
sides (Python bsim3 agrees). FGcdNetOKBA.toOKBM: the arbiter-extended hypothesis implies
the mux-extended one (bindings agree wherever M names a driver; the arbiter cells' contracts
from fcomb_spec_cell / fcel_spec_cell); gcd_hw_safe_fin_netBA. NO joint witness yet (Python
evidence bsim3.py); H_EXC_CLEAN is where the race windows (ArbAMergeRun's H_SEP, RA1, Rows)
must come in, and it is assumed, not derived, here.

### progress 11:19
Bwit3 steps 2-3 (lake build OK): BWit3Data (gen_cdata3.py --check ok; bsim3 with q
powering up 0 and set by reset, as B's model has it) + BWit3Cells: C's H_CELLS, H_BUNDLE,
start once, H_CM_FORCED and out0 = 6 on the arbiter-gate-modelled run, by C's checkers
(kernel). BWit3Lib: combB, a checker for FCombSpec cells on event lists, with soundness
(combB_spec): H_EXC_CLEAN holds because the excitation is the node one tick early
(gph_shift of a clean list signal).

### progress 11:50
Bwit3 done (lake build OK: BWit3NDefs, BWit3NChk alone (728 s, peak RSS 11.0 GB), BWit3Net;
#print axioms of the witness: propext, Classical.choice, Quot.sound only).
**Problem, plainly:** is the gcd_hw theorem with the ARBITERS gate-modelled too
(FiniteNetBoundA: 164 of 175 links bound on both sides) satisfiable by an actual run, or
could its hypotheses be contradictory? **Answer (Lean):** `BWit3.bwit_okA : FGcdNetOKBA chB
NBa LB nB` on the gate-timed run chB (a = 12, b = 18, every tied gate LUT 1 + wire 1-3), and
`gcd_hw_fin_netBA_witness`: jointly with C's H_OTHER, H_BUNDLE, H_CM_FORCED and out0 = 6;
`gcd_hw_fin_netBA_consistent` applies the theorem. Every arbiter cell on its real LUT:
ustate q/R0 and ugrant g1/g2 by `combB` (their H_EXC_CLEAN discharged by checking the
traces), ua1/ua2 by `maB` with a winner table.
**Changed on the way:** H_ARBA is now FMuxASpec, not FCelSpec GC2. z_ack carries both
clients' tokens, so ua_k's z_ack edge index must be mapped through the winner table; the
GC2 form failed by #eval on exactly the 3 arbiters (171, 178, 180) whose z carries tokens
from both clients on this run (winner tables by #eval: 167 [-], 169 [2], 171 [1,2],
174 [-], 178 [1,2], 180 [1,2,1], 182 [2], 184 none, 185 [2]; "-" = one client-1 token).
**Negative controls (#eval, tools-B/bwit/negctl_arb3.lean):** on arbiter 171 the real
check passes; flipping winner-table entry 0 fails both maB checks; moving q's first edge
+1 tick fails combB qF; checking g1's node against g2's LUT fails.
**Does NOT show:** a contested grant (no two requests race on this run, so H_EXC_CLEAN is
never tight; the race-window content of ArbAMergeRun is not used); routed delays (unit
LUTs, simulator wires); R = 2 only; muxn 4, fork trees 6, source 1 link sides still unbound.
Memory: a kernel decide over several arbiters at once peaked 8.5 GB for 10 operators, so
arbChk is one theorem per arbiter (barb_*), with barb_rest checking that every other
operator passes arbChk trivially.

### progress 12:08
(1) Build order: BWit2NChk now imports BWitNChk and BWit3NChk imports BWit2NChk (import
used for ordering only), so a fresh `lake build` cannot run the three kernel-check modules
at once (BWit3NChk alone peaks at 11.0 GB RSS on this 15 GB box; two in parallel were
OOM-killed earlier today). Rebuilt in sequence: BWit2NChk 547 s, BWit3NChk 749 s, then
BWitNet/BWit2Net/BWit3Net OK.
(2) In (lake build OK): FiniteNetBoundT -- the FORK TREES gate-modelled and bound.
**Problem, plainly:** a fork with 5 or 6 outputs acknowledges through a tree of C-elements
(cells/rtl/bd_ce.v bd_ctree: chunks of four, then a top C2), which B had no binding for, so
6 link acknowledge sides were unbound. **Lean:** FGcdNetT adds tr o (top C2, drives the fork
input's ack) and tn o 0/1 (chunk C4 of leaves 0..3; chunk C2 of leaves 4, 5 for N = 6);
FGcdNetOKBT has H_TREE5/H_TREE6 (FCelSpec of each tree cell on its real gate, chunk node
wired to the top, every leaf the bound ack of its fork output) and H_DRV_TREE;
FGcdNetOKBT.toOKBA; gcd_hw_safe_fin_netBT; bound_censusT (kernel): 170 of 175 links bound on
both sides; by #eval the 5 left are the 4 muxn acknowledge sides and the source request side.
No witness committed yet. Python (UNTRUSTED, bsim4.py): the trees at gate level on the
12/18 run, C's checker 0 violations, 750 bound pins all wire copies of their driver, 170
links bound both sides; the 3 trees (ops 67, 88, 143) toggle (top node 4/2/6 edges). Data
generated (gen_cdata4.py, gen_bdata4.py -> BWit4Data, BWit4NData), BWit4NDefs builds, and by
#eval wireChk, opChkB (incl. treeChk) pass everywhere. BWit4Cells/NChk/Net written, not yet
built (BWit4Net typechecks against a stub of the kernel facts, scratch only).

### progress 12:25
Bwit4 done (lake build OK: BWit4Cells 16 s; BWit4NChk alone 756 s, peak RSS 11.2 GB;
BWit4Net; #print axioms of the witness: propext, Classical.choice, Quot.sound only).
**Problem, plainly:** is the gcd_hw theorem with the fork trees gate-modelled too
(FiniteNetBoundT: 170 of 175 links bound on both sides) satisfiable by an actual run?
**Answer (Lean):** `BWit4.bwit_okT : FGcdNetOKBT chB NBt LB nB` on the gate-timed run chB of
BWit4Data (12/18; muxes, arbiters and the 3 fork trees at gate level, LUT 1 + wire 1-3;
C's checkers by kernel in BWit4Cells: H_CELLS, H_BUNDLE, start once, H_CM_FORCED,
out0 = 6), and `gcd_hw_fin_netBT_witness` jointly with C's H_OTHER, H_BUNDLE, H_CM_FORCED;
`gcd_hw_fin_netBT_consistent` applies the theorem. Every tree cell on its real C-element
(celB), chunk nodes wired to the top by unit wires, the top driving the fork input's ack.
**Negative controls (#eval, tools-B/bwit/negctl_tree4.lean):** the three trees pass;
op 67's chunk C4 node with its first edge +1 tick fails; op 67's top C2 read from leaves
3, 4 instead of (chunk, leaf 4) fails; op 143's top checked as a C4 of leaves 0..3 fails.
**Does NOT show:** routed delays, R > 2, a contested arbiter; muxn (4 ack sides) and the
source (1 req side) remain unbound, and C's H_OTHER remains a hypothesis.

### next (for the next B session)
- muxn, the last gate-model class (4 ack sides): bdc's generated `bdc_muxn` (decode LUT3s,
  joins C(x_k req, decoded ctl req), the 3-input request OR, the FASTFALL delay stages
  FAndSpec, ua_k = C(j_k, z_ack) FMuxASpec). AssumeGuaranteeMuxNFin has FDecSpec, FAndSpec,
  FMuxASpec, FBufSpec; missing: the 3-input OR in truncated form, the Bool checkers, and
  a simulator model of the generated netlist (read bdc's emitter for its exact cells).
- The source request side cannot be gate-modelled on a terminating run
  (FiniteNetSrc.chW_src_unwired).
- A CONTESTED arbiter run: every witness so far has uncontested arbiters, so H_EXC_CLEAN is
  never tight; a run where two requests race (a different a, b or forced timing) would
  exercise the race hypothesis (combB would then fail where a runt occurs, which is the
  honest outcome to report).
- Memory: each NChk module peaks ~11 GB; they are chained by imports (BWit -> 2 -> 3 -> 4) so
  lake builds them one at a time. A fifth must import BWit4NChk.

### correction 12:31 (to 11:50 and 12:25, and the BWit3Net/BWit4Net docstrings)
"The 9 arbiters are uncontested on this run" overstated what was checked. Measured (Python,
bsim3 and bsim4, 12/18): at arbiters 171 and 180 both requests ARE high together (171: x
granted at 74, y rises at 115 and waits; 180: y rises at 369 while x holds, later x rises at
511 while y holds), so hold and handover epochs occur. What does NOT occur is a race: the
closest x/y request rises at any one arbiter are 36 ticks apart (op 180, ticks 333/369),
against 2 ticks per gate, so no two requests reach the arbiter inside its decision window
and H_EXC_CLEAN is never tight. Other inputs give no race-closer evidence in this
simulator: 9 (a, b) pairs tried, all with C's checker clean; none was searched for races.

### progress 14:03
(1) formal/check.sh --committed on 304b2fe9 (all of today's B Lean, before the lead's Prelim
deletion was pulled): "Build completed successfully (3897 jobs)", axiom audit "[check] OK".
(2) After rebasing onto the Prelim deletion (67a08438) and the docstring correction
(fe2b0079): lake build of every B witness chain OK on the new head (163 jobs; the chained
NChk modules rebuilt one at a time: BWitNChk 386 s, BWit2NChk 495 s, BWit3NChk 737 s,
BWit4NChk 725 s), so the docstring-only commit fe2b0079 builds.
(3) notes/B-muxn-bind-plan.md: the last unbound gate class is ONE muxn (op 163): its three
input acknowledges and its control acknowledge (a wire from z.ack, z feeding a sink).

### progress 14:46
Kernel-check memory: the auditor's full build of 58251494 OOM-killed BWit2NChk (it built
alone at 10.3 GB), so the import chain alone is not enough when other shards' modules build
in parallel. Measured (scratch, BWit4 data): one decide over 60 operators peaks 7.1 GB RSS,
over 20 operators 3.8 GB, the 240-channel wire chunk 2.6 GB, and memory is released between
declarations. All four NChk modules now check operators in 25 chunks of 15 (bop_k0..bop_k24;
bop_all by a chunk-index match). Rebuilt in sequence (lake build of the four Net modules,
EXIT 0, 162 jobs): BWitNChk 405 s, BWit2NChk 458 s, BWit3NChk 652 s, BWit4NChk 708 s; peak
RSS over the whole build 4.9 GB (was 11.2 GB).

### progress 15:05
In (lake build OK): FiniteNetBoundN -- the muxn's per-input cells gate-modelled and its
INPUT acknowledges bound (theorem level only). **Problem, plainly:** gcd_hw's one muxn
(op 163) acknowledges its three inputs through cells B had no binding for. **Lean:**
FGcdNetN adds nd/nj/na o k (decode sel_k as FDecSpec, whose LUT3 INITs are LibGapMuxN's
H_YOSYS_MAP inference; join uj_k as FCelSpec GC2 with the decode as its b pin; ua_k as
FMuxASpec driving in_k.ack); FGcdNetOKBN has H_MUXN (per input k: the three specs, pins bound,
the decode's index bits = the control channel's data bits) and H_DRV_MUXN; FGcdNetOKBN.toOKBT;
gcd_hw_safe_fin_netBN; bound_censusN (kernel): 173 of 175. The 2 left (by the Python
re-implementation, not Lean): the muxn's control acknowledge (a wire from z.ack, z feeding a
sink B does not model) and the source's request side. **NO joint witness** (no simulator
model of the generated muxn, no Bool checker for FDecSpec): this level is a theorem whose
hypotheses are not shown satisfiable; the T level (170/175) is the strongest with a witness.

### progress 15:51
formal/check.sh --committed on 464c5ea7 (all of today's B work, incl. the chunked NChk
modules and FiniteNetBoundN, on top of the Prelim deletion): "Build completed successfully
(3897 jobs)", axiom audit "[check] OK".

## Session Sun Nov  1 07:31:24 UTC 2026 (shard B; session_01HC49FxmwjXSipv3GEnyeUk)
First B session under THE goal (one theorem about the gcd_hw bitstream). Lock was 15.3 h old
(previous B session), taken. formal/target/ does not exist yet (shard A picks the target
today), so B works on what the theorem needs whatever the target: H_PRIM and the arbiter.
setup.sh: Mathlib cache unreachable, building Mathlib from source (in progress); Core-only
files are checked meanwhile with a private olean chain (lean -DautoImplicit=false -o).

### progress 07:31 -- audit rows answered
- P16 (H_EXC_CLEAN "(no runt, no hazard)", OVERSTATED wording): accepted. FiniteNetComb's
  docstring and notes/B-hypotheses.md now say it only fixes the excitation's listed edges, a
  runt satisfies it, and arbiter exclusion stays C's H_OTHER. Statements unchanged.
- P15bc B1 ("1-input join is a wire", 136/175, OVERSTATED): accepted. FiniteNetBoundM's
  docstring and the ledger now say the ushrsi0/1 request side is a 2-input join plus a gated
  delay chain, faithful count 134/175. Statements unchanged.
- Corner misreading rows (ArbHeldTimed, B-arb-a0fork): already answered (2026-10-29/30
  entries; the note carries the correction).

### progress 07:31 -- H_PRIM in window form (HPrimWin.lean, checked, Core only)
**Problem, plainly:** which single per-primitive relation is implied by every admissible gate
behaviour (transport with any delays in the band, even time-varying; inertial swallowing;
jitter), so that one proof covers them all? **Lean:** `WinH f pin lo hi y` (output at tau at
least as defined as f of any Kleene abstraction of each pin over its window
[tau - hi_i, tau - lo_i]); `win_of_varTransport`, `win_of_timed`, `win_inertial`
(time-varying transport, Core's fixed-delay Timed.H, sampled/inertial behaviours all imply
WinH); `win_widen` (guard widening preserves it); `win_forced`, `win_settles`, `win_sic`;
`buf_win`/`buf_not_fixed` (strictly weaker than fixed-delay transport). Checked privately
(lean -DautoImplicit=false -o on Kleene/Xray/XrayData/Muxf/Carry, then the file): OK.
**Does NOT show:** that silicon is any of these (H_PRIM itself); involution (next file);
flops (SeqFlop needs H_FF_RESOLVE, not among the five allowed hypotheses -- recorded for
shard A in notes/B-hprim.md: gcd_hw has 326 flops and async synchronizers).

### progress 07:38 -- FOR SHARD A: Spec v1's H_ARB(T) makes the theorem vacuous on every handover
**Problem, plainly:** Spec v1 (`Wip/Target/Spec.lean`, A's draft) states H_ARB(T) as "both
request nodes constant on [t1, t2] => state node q constant on [t1 + T, t2]". The held
`bd_arbiter`'s state LUT (ustate, INIT FFF0_FFB2_ACAC_ACAC, O6 = q) also reads A0 and rst:
q is frozen while A0 is high and flips at A0's fall. In a normal handover (client 1
released, client 2 waiting) both requests are constant across A0's fall and q must flip.
So GateOK + ArbOK is contradictory for every behaviour in which the server holds A0 at
least T after the requests last moved, and NetCorrect is vacuously true for all of them.
A0's fall waits on the downstream and, through out0, on the environment, which H_ENV does
not bound: such behaviours exist for every T.
**Lean (Wip/Bspec/ArbOKVacuous.lean, checked privately against a verbatim copy of the
draft, Wip/Bspec/SpecV1.lean; standard axioms only; not built by lake):**
`arbOK_excludes_handover` (any p, corner, arcs: q gate GateOK, r1 = 0, r2 = 1, rst = 0,
A0 high until ta then low, q high at T, ArbOK T => False); `handover_gate_ok` (the
scenario IS a GateOK behaviour of the q gate with exact 10 ps arcs, g = 1, κ = 0);
`arbOK_vacuous_for_every_T` (for every T: a behaviour GateOK admits and ArbOK T forbids).
**Suggested repair (not proved to suffice):** quantify over ALL non-feedback pins of the
state LUT as read at its pins (r1, r2, A0, rst), and note that T below the state gate's
slowest arc contradicts an ordinary set/reset transition the same way (non-vacuity needs
T >= that arc's g·SLOW_MAX plus the feedback route).
**Also:** Spec v1 does not compile as committed: `⌈⌉` on ℚ (Gate.start, line 152) needs
`import Mathlib.Data.Rat.Floor` (the copy adds exactly that line; then it checks).

### progress 07:41 -- H_PRIM vs involution channels (HPrimInv.lean, checked)
**Problem, plainly:** PROGRAM asks H_PRIM to be pessimistic, or the result to hold for
transport, inertial AND involution. Spec v1's GateOK and B's WinH are read-time models (the
output is the gate function of pins read at admissible delays). Is an involution channel
(Core InvolutionPair, full trace semantics with cancellation) a read-time behaviour when its
delays are "in the band"? **Answer (Lean): not in general.** `WinR` (1-pin Boolean window
relation) is implied by every read-time model (`win_of_readTime`, no monotonicity needed;
`win_of_chan` for Core's Chan). `rat_not_win`: Core's ratPair (delta_inf = 2, delta_min = 1,
`rat_numbers`), input pulse [0, 3/2): output high on [2, 17/6) (`rat_out`, via Core's
pulse_out); at tau = 29/10 the input is steadily 1 on its window [9/10, 7/5] for the band
[3/2, 2], the output is 0. `rat_not_readTime`: no read map at all reproduces it. Positive:
`inv_sep_win` -- with input edges S apart, S > delta_inf - delta_min, the output IS a window
behaviour for Core's transfer band (and wider, `winR_widen`). Standard axioms only
(lake env lean, after lake build of Formal.Core.Delay.InvolutionTrace).
**What it means:** a read-time H_PRIM (Spec v1) covers transport and inertial, and involution
only for long pulses or bands whose lower end is at most the channel's short-pulse delays;
an involution trailing edge can come earlier than lo. Shard A must either name that
restriction in the fidelity table or take band lower ends at most delta_min (unreported by
prjxray). **Not shown:** the exact band/pair characterisation; multi-pin Kleene case.

### progress 07:48 -- the arbiter under H_ARB(T) (ArbT.lean, checked, Core only)
**Problem, plainly:** under the Spec semantics (Boolean gates, per-pin read times in the
bands) plus H_ARB(T), is the held bd_arbiter safe, and how does T enter? **Lean:** read-time
gates `RGate` (Spec v1's GateOK minus monotone reads, so positive results transfer), the
real INITs (`q_eq`, `r0_eq`, `g1_eq`, `g2_eq`, `ua_eq`, decide). Positive: `q_stays`
(settled q kept while pins confirm it: A0 freeze, tie hold), `grant_excl`, `ack_stays_low`,
`one_ack` (q settled W before A0 rises => the losing ack stays low for the whole server
transaction). **Counterexample `double_ack`:** all six gates hold (unit delays, q feedback
band [2,3]), H_ARB(T) in B's strong form `ArbOK2` (all four non-feedback ustate pins) holds
for every T >= 7, near-tie r1@10/r2@11, q oscillates (circulating runt) until 20, server A0
rises at 18 (R0 rose at 12, one transaction), and BOTH A1 (19) and A2 (20) rise. Negative
control: changing the resolving read (t=21 -> 19) breaks the kernel check. Standard axioms.
**What it means (FOR SHARD A/C):** H_ARB(T) alone does not give arbiter safety; it needs the
timing obligation "last edge at ustate's pins -> A0 rise at ua >= T + W" (a server path),
which the checker must generate and prove from the bands; THE theorem's T margin is bounded
by the shortest such path. This is the Spec-semantics form of A's arb_double_ack (fid GLS).
**Not shown:** the full cell contract (four-phase, liveness, phase chaining); route arcs.
Notes: notes/B-arbT.md.

### progress 07:54 -- FOR SHARD A (again): the FROZEN Spec's ArbOK still excludes every held-arbiter handover
Spec.lean was frozen at 07:55 with `ArbOK` unchanged from the draft I flagged at 07:38. Now proved against
the frozen file itself (built by lake; check.sh on it OK): `Formal/Cells/SpecArbVacuous.lean`,
`arbOK_excludes_handover` (any p, corner, arcs: the q gate holding, r1 = 0, r2 = 1, rst = 0, A0 high
until ta then low, q high at T, ArbOK T => False), `handover_gate_ok` (the scenario is a GateOK
behaviour of the q gate), `arbOK_vacuous_for_every_T`. **Consequence for THE theorem:** NetCorrect and
NetCorrectSeq are vacuously true on every behaviour in which some arbiter's server holds A0 for T or
more after that arbiter's requests last moved (the q flip at A0's fall is forced by GateOK and
forbidden by ArbOK); for T below the state gate's own arc delay, on every behaviour with any grant.
B's witnesses of gcd_hw show handovers at arbiters 171 and 180 with one pair in flight, so this is
not a corner case. **Repair (journaled reason + audit row needed, shard A's file):** quantify ArbOK
over all non-feedback pins of the state LUT (r1, r2, A0, rst), i.e. `ArbNodes` gets `a0` and `rst`
(B's `ArbT.ArbOK2`), and state that T must exceed the state gate's slowest arc for non-vacuity. Even
repaired, H_ARB(T) does not give safety by itself (`ArbT.double_ack`, progress above): the proof needs
the derived obligation "last edge at ustate's pins -> A0 rise at ua >= T + W".
check.sh (per file) OK on all four new B files: HPrimWin, HPrimInv, ArbT, SpecArbVacuous.

### progress 08:02 -- STATUS item 3: MUXF7/F8, CARRY4, LUT6_2 as Spec gates (PrimTables.lean, check.sh OK)
**Problem, plainly:** the frozen Spec has one primitive kind (a table gate with per-pin reads); is
each non-LUT slice primitive, written as such gates, exactly shard A's Core model? **Lean:**
`table_sound` (a table checked on all 2^k addresses is read correctly on every pin vector, via
`addr_lt`/`addr_testBit`); `muxf_gate` (0xCA = Core bmux); `carry_gate` (8 tables of 512 bits,
Core pin order, = Core bout); `aCarry_gate` (shard A's decoder layout from build_net.py:
pins [CIN, CYINIT, S0..Si, DI0..], carry-in CIN||CYINIT, A's table loop transcribed: = Core bout on
the mapped pins, all 8 outputs; negative control: swapping the loop's mux arms fails);
`lut6_gate`/`lut5_gate` (O6 = 6-pin gate with INIT, O5 = 5-pin gate with INIT mod 2^32, = Core
Lut.eval). decide +kernel (no native_decide); standard axioms. Fidelity: per-pin single reads are
exact for CARRY4/MUXF because every output is a read-once formula of its pins (Core kout_sic).
**Does NOT show:** the decoder itself (part II), that CIN||CYINIT equals the silicon's PRECYINIT mux
(it does when the unused source is tied 0 -- the Lean decoder should check that per site).

### progress 08:06 -- feedback LUTs under the frozen Spec (SpecFb.lean, check.sh OK)
**Problem, plainly:** what does the Spec's GateOK alone guarantee for a storage node (a LUT reading
its own output: C-element, latch, arbiter q), given that only arbiters get a resolution
assumption? **Lean (over Formal.Target.Spec):** `fb_stays` (confirmed value stays), `fb_forced`,
`fb_switch` (forced for at least the feedback arc's upper bound, then confirmed: clean switch);
`fb_runt_oscillates`: a bd_c2 C-element (0xE8), arcs 1/1/3 ps, a = 1, b high for 1 ps -- forced
for less than the feedback arc -- and GateOK admits a behaviour that oscillates for ever
(`c2_osc_forever`). Standard axioms. **FOR SHARD C:** every storage node of the target needs the
derived obligation "each forcing episode at its pins lasts >= the feedback arc's hi" (fb_switch's
side condition); H_ARB covers only the arbiters' q. Notes: notes/B-specfb.md.

### progress 08:09 -- the double acknowledge is a behaviour of the FROZEN Spec (ArbTSpec.lean, check.sh OK)
**Problem, plainly:** does the frozen statement's H_ARB(T) keep an arbiter from acknowledging both
clients in one server transaction? **No.** `spec_double_ack`: six Spec `Gate`s (ustate O6/O5, ugrant
O5/O6, ua1, ua2; real INITs, tied pins folded), `Behaves` at the slow corner with g = 1, κ = 0
(monotone read maps, every read delay admissible: unit arcs, q's feedback arc (2,2,2,3)), the frozen
`ArbOK T` for every T >= 9, R0 rises once at 12 and stays high, the server's A0 rises at 18, and
both A1 (19) and A2 (20) rise. Standard axioms. **What it means:** THE theorem cannot be proved by
treating arbiters as safe under H_ARB(T); the proof must derive "q settled before A0 rises at ua"
(ArbT.one_ack) per arbiter from the bands, through the server path. For T at least the shortest such
path in the target, this shape is a candidate counterexample on the target itself (not yet built:
needs the decoded target's arbiter nodes and a near-tie reachable under the sequential env).

### progress 08:16 -- arbiter positive results usable on Spec gates; target arbiter list
`ArbTSpec.rgate_of_gateOK` (a Spec gate with Nat bounds implied by Adm is a read-time RGate) and
`spec_one_ack` (ArbT.one_ack stated for Spec gates: ugrant O6 and ua2; q settled before A0 rises =>
the losing ack stays low for the whole transaction). check.sh OK on all seven B files of today.
The target has nine bd_arbiters (SDF instance names): urig.udut.ucontrol_merge{2,3,4,6,9,10,11,12}.uarb1
and ucontrol_merge12.uarb2 (ustate packed as $LUT6 = q, $LUT5 = R0); recorded in notes/B-arbT.md for
Spec part II's `List ArbNodes` (which should carry A0 and rst too, per the repair).

### progress 08:29 -- LEAD (simulation, untrusted): near-ties at two gcd_hw arbiters are plausible under the SEQUENTIAL env
Question: can two requests reach a gcd_hw arbiter nearly together with ONE pair in flight (the shape
ArbT/ArbTSpec.double_ack needs)? Tool: tools-B/arbgap (uses shard C's generated-netlist simulator
tools/capwit3/simgen.py read-only; amerge is modelled abstractly there, only the request timing is used).
- Unit delays, (12, 18): arbiters op 171 (z111) and op 180 (z229) see both requests rise from idle,
  x at 195 / y at 282 and x at 616 / y at 698 (op 178: 594 / 854).
- Causality (tools-B/arbgap/causal.py): slowing ONLY the arbiter's own z.ack by 40 ticks moves y's rise at
  op 178 (854 -> 894: y waits for the arbiter's handshake, so no race is possible there) but NOT at ops 171
  and 180 (282 and 698 unchanged): there the two requests come from independent paths of the same
  invocation, and which one arrives first is decided by path delays.
- Node-count estimate: both rises follow the single input offer at ~0, so a relative path-delay shift of
  87/477 = 18% (op 171) or 82/1314 = 6.2% (op 180) closes the gap, if the paths are disjoint.
  Independent random scatter does not (±10% per node, 3 seeds: gaps stay ~10x the unit gaps, the law of
  large numbers); it needs the ADVERSARIAL per-arc choice that Spec's Adm allows (each arc anywhere in its
  corner window; even κ = 0 leaves FAST_MIN..FAST_MAX, ~±10% on LUT arcs).
**If this transfers to the target's routed delays:** H_ARB(T) is genuinely exercised under the sequential
env, and NetCorrectSeq can only hold for T below the shortest server path (ArbT.one_ack /
ArbTSpec.spec_double_ack). NOT shown: a trace on the decoded target, the target's real path delays, path
disjointness. Next step for whoever has the decoded net (shard A's sim.py): an adversarial in-band
assignment slowing x's cone and speeding y's at arbiter ucontrol_merge(z229) / (z111), then look for a
runt on ustate's set/reset excitation.

### progress 08:35 -- shard A repaired Spec's H_ARB (08:11, 3d3ebb61); B files updated to it
A adopted the repair (ArbNodes = q + every non-feedback input of the state LUT). That broke my two files
built against v1 (SpecArbVacuous, ArbTSpec: lake build failure, fixed within the hour):
- SpecArbVacuous now states the v1 defect against a verbatim local copy `ArbOKv1` (history).
- **ArbOKRepair (new, check.sh OK), against the repaired Spec:** `arbOK_admits_handover` (the handover
  v1 excluded satisfies the repaired ArbOK for T >= 10, the state gate's arc in the example);
  `arbOK_needs_T_ge_arc` (for T < 10 the repaired ArbOK excludes that ordinary, race-free q transition:
  **THE theorem must take T at least the state gate's slowest admissible arc, else it is vacuous on every
  arbitration** -- FOR SHARD A: STATUS/Spec should say so); `arbOK_mono`.
- ArbTSpec: the double acknowledge now meets the repaired ArbOK for every T >= 7 (`spec_double_ack`).
check.sh OK on SpecArbVacuous, ArbOKRepair, ArbTSpec.

### progress 08:43 -- CORRECTION to the 08:29 lead: on the decoded target, the two requests at an arbiter do NOT share a distant common cause
The 08:29 node-count estimate assumed both request rises follow the input offer at ~0 by independent
paths. Measured on the decoded target itself (shard A's generated Lean netlist rebuilt as JSON by
tools-B/target/lean2json.py -- 200097 nodes, 199736 gates, 9 arbiters, boundary names = A's; shard A's
simulator copied as tools-B/target/simb.py with a per-gate delay-position map; vector (12, 18), mid corner,
mid-window delays; all untrusted Python): causal back-traces (tools-B/target/adv.py `crit`) of each
"both requests rise from idle" event:
- arb 0 (SLICE_X0Y18.D): chains meet 4.3 ns before r1's rise; r2 rises 95 ns after r1.
- arb 6 (SLICE_X41Y24.C): chains meet 0.27 ns before r1's rise; r2 rises 60 ns after r1.
- arb 8 (SLICE_X0Y96.A): r2's causal chain passes through r1's own rise (no race possible).
- the other six: no both-from-idle event on this vector.
Adversarial runs (each private path at the opposite end of its corner window, κ = 0) move the gaps by
<= 15 ns (arb 0: 95 -> 83 ns); an apparent "order flip" in the first script was an event-matching artifact
(tie.py's bisection shows the gap never crosses 0). So on this vector the arbitrations are lopsided by
tens of ns and the 08:29 near-tie lead does NOT transfer. The 16 rig vectors are running (tools-B/target/run16.sh).

### progress 08:46 -- separated arbitrations need no H_ARB (ArbClean.lean, check.sh OK)
**Problem, plainly:** can the proof avoid H_ARB(T) at an arbiter whose two requests are separated in time
(as every simulated arbitration on the decoded target is, by >= 52 ns so far)? **Lean (frozen Spec
semantics):** `q_clean_set` / `q_clean_reset`: if the held arbiter's state LUT reads the set (reset)
condition over its read windows for at least its feedback arc (`s + hi_q <= e + 1`) and afterwards r1 (r2)
stays high with rst low, q is 1 (0) on the whole interval, whatever r2 (r1) and A0 do -- SpecFb.fb_switch
plus decided table facts; no resolution hypothesis. With ArbT.one_ack this decides a separated
arbitration. **What it means:** per arbitration the proof can take the separation route (an obligation:
the requests at ustate's pins are separated by >= the feedback arc, provable from the bands where the
second request's causal path is long) instead of H_ARB(T). **Not covered:** physical pin permutations of
each decoded ustate; proving separation for every behaviour.

### progress 08:50 -- ArbClean for the target's own (pin-permuted) ustates; FF concern settled by the audit
- `q_clean_set_gen`: the clean-set theorem for ANY pin order (roles r1, r2, feedback, rst, A0, tied pins),
  with the two table facts as hypotheses; `hset_of_fact`/`hconf_of_fact` turn decidable Boolean facts into
  them. `targetQ` (GENERATED from the decoded target via tools-B/target/lean2json.py + adv.py roles: the
  nine ustate O6 gates' names, INITs and role indices -- each one permuted differently by nextpnr) and
  `targetQ_facts` (kernel decide: all nine meet both facts); negative control `targetQ_swap_fails`
  (r1/r2 swapped on the first gate: the set fact fails). check.sh OK. Not yet linked by an equality to
  `Formal.Target.Decoded.net` (that module is not committed; audit T4 row 135), so `targetQ` is data of
  the same generator, not yet the Lean netlist itself.
- Audit T4 (row 134): "no FF reaches the kernel cone (170254-gate cone has 0 free non-env nodes)". So my
  H_FF_RESOLVE concern (notes/B-hprim.md, 07:2x) does not arise for the kernel: Spec's gate-only H_PRIM
  covers every primitive in the cone (LUT6_2 halves, MUXF7/F8, CARRY4 outputs, pips/hops), all with tables
  in PrimTables.
- Audit T3 confirmed HPrimInv (H_PRIM scope gap) and double_ack (H_ARB alone gives no exclusion), and found
  the same v1 ArbOK vacuity independently.

### progress 08:53 -- (simulation, untrusted) every arbitration on 12 of the 16 rig vectors is separated by >= 50 ns
tools-B/target/run16.sh (adv.py on each gcd_rig.v vector, sequential env, decoded target, mid corner): over
the 12 vectors finished so far, the closest "both requests rise from idle" pair at each arbiter, minimum over
the baseline and both adversarial runs (each request's private causal path at the opposite end of its corner
window, κ = 0): arb 0 79 ns, arb 4 52 ns, arb 6 52 ns, arb 7 51 ns, arb 8 168 ns; arbs 1, 2, 3, 5 never see
two requests from idle. At κ = 0.5 (vector 0x10E,0xC0) the tightest, arb 7, is still 29 ns apart. The state
LUT's feedback loop (route + pin arc, decoded data) is 114..930 ps (FAST_MIN..SLOW_MAX, worst arb 8), so on these schedules every arbitration is separated by ~50x or more what
q_clean_set needs (arb 7: 29 ns vs its 543 ps loop at κ = 0.5), and H_ARB(T) is never exercised. **Plainly:** in simulation the target's
arbiters never race under the sequential environment; a proof can aim at the separation route
(ArbClean) and leave T unconstrained there -- but simulation covers a handful of delay assignments, not the
bands, and arbitrations triggered only by other inputs are not seen. NOT shown: separation for every
behaviour (it needs a checker obligation per arbitration, shard C).

### progress 09:10 -- (simulation, untrusted) the target's weakest storage node: arbiter 0's ua C-element, margin closes near κ ≈ 0.25
**Question, plainly:** SpecFb says every storage node needs each flipping forcing episode to outlast its
feedback loop, else a runt can circulate for ever (no hypothesis of THE goal resolves it outside arbiters).
How close does the target come? **Tool:** tools-B/target/fbscan.py over the 16 rig-vector baseline dumps
(sequential env, decoded target, mid corner, mid-window delays; only episodes after reset release counted):
540 feedback LUTs active; the five weakest ratios (episode / simulated loop delay): SLICE_X2Y18.DLUT.O6 1.72
(1143 ps vs 665 ps; loop SLOW_MAX 1064 ps), SLICE_X0Y18.CLUT.O6 2.76, SLICE_X42Y82.ALUT.O6 3.16,
SLICE_X6Y99.CLUT.O6 3.21, SLICE_X38Y78.ALUT.O6 3.68 (table: notes/B-fbscan.md).
SLICE_X2Y18.DLUT.O6 is arbiter 0's acknowledge C-element (decoded table = majority(A0, g, fb) with reset; its
g pin comes from arbiter 0's ugrant at SLICE_X0Y18.A): the episode is "A0 rises with g high -> ua rises -> the
client drops r -> g falls at ua's pin", which must outlast ua's own feedback route (6 hops + pin arc).
**Adversarial (tools-B/target/fbadv.py, vector (12,18), corner 0.5):** that causal path at the fast end of its
windows, ua's feedback route and ua at the slow end: κ = 0: episode 1062 ps vs loop 743 ps; κ = 0.1: 1009 vs
815; κ = 0.2: 953 vs 890 (63 ps left); κ = 0.3: loop 964 ps, run still going (pending). By the trend the
episode becomes shorter than the loop between κ = 0.2 and 0.3: then, in the Spec semantics (transport is a
GateOK behaviour), ua1 can latch a runt and oscillate -- an acknowledge glitch at arbiter 0. **If confirmed,
THE theorem's κ margin is below ~0.25 at g = 1 because of this one node.** Not shown: the κ = 0.3 outcome, other
corners, a Lean trace.

### progress 09:33 -- CANDIDATE COUNTEREXAMPLE (simulation, untrusted) to NetCorrectSeq at g = 1, κ = 0.215: arbiter 0's acknowledge latches a runt
**Plainly:** on the decoded target bitstream, with the SEQUENTIAL environment, rig vector (12, 18), corner
0.5, and every delay inside Spec's Adm window for g = 1, κ = 0.215, arbiter 0's acknowledge C-element ua1
(SLICE_X2Y18.DLUT.O6, decoded table C(A0, g) with reset) sees its set condition for less than its own
feedback loop: the acknowledged client (a controller at SLICE_X2Y18.A) drops its request, and ugrant's g
(SLICE_X0Y18.A) falls at ua1's pin, before ua1's output has come round its 6-hop feedback route. ua1 rises
at 600.991 ns, falls at 601.885, rises at 601.892, ... : a 7 ps runt circulating with period 894 ps (the
loop delay), for ever in the transport semantics (a GateOK behaviour). It spreads: by 620 ns 5336 nodes
toggle, some every ~5 ps; no out0 by 620 ns (the correct run gives out0 = 6 at 756 ns). κ <= 0.21: clean.
The race is the textbook isochronic-fork race at a C-element (client latency vs the C-element's feedback),
here between a 3-LUT client path (episode 1143 ps at mid-band) and ua1's feedback loop (665 ps mid, 1064 ps
SLOW_MAX), the tightest of the target's 540 active storage nodes (notes/B-fbscan.md).
**Delay assignment:** tools-B/target/out/cex_ua1_posmap.json (22 gates: the client path at the fast end of
the κ-widened window, ua1's feedback route and ua1 at the slow end; everything else mid-window); reproduce:
tools-B/target/out/cex_ua1_README.md. **What it means:** if the simulator is right, THE theorem as frozen
(NetCorrectSeq) is FALSE for p = (g = 1, κ >= 0.215) at corner 0.5, so its κ margin is at most ~0.21 there,
and the binding constraint is a C-element race, not the arbiter's decision (H_ARB is not involved).
**NOT shown:** a Lean witness (needs shard A's Witness machinery; the spreading oscillation may make the
behaviour hard to certify as eventually periodic), other corners, κ = 0 (319 ps of margin left there),
research's fid GLS on this assignment (FOR SHARD A / research: please run it), whether silicon's inertial
filtering would kill a 7 ps runt (the Spec admits transport, so the Spec theorem must exclude it by timing).

### progress 09:39 -- the ua1 counterexample's κ threshold: 0.155-0.158 at corner 0.5 with a per-pin adversary
simb.py now takes per-pin positions ("gate:pin"); `cex_ua1_posmap_pin.json` additionally puts ua1's A0 pin
at the slow end and its g pin at the fast end (the episode at ua1 is g's fall read minus A0's rise read).
Corner 0.5: clean at κ = 0.155, oscillation at κ = 0.158. Per-gate assignment: corner 0.5 0.21/0.215,
corner 0.2 0.2016/0.2062, corner 0.1 0.2859/0.2906; corners 0 and 1 clean up to κ = 0.3 (at an extreme
corner Adm clamps one end of the window to the global band, FAST_MIN or SLOW_MAX, so the adversary loses
one direction). Per-pin map over corners 0.1..0.9 running (tools-B/target/kmap.py). **So far: if the
simulator is right, NetCorrectSeq on the target is false for g = 1 and every κ >= 0.158 (corner 0.5), i.e.
THE theorem's κ margin is < 0.158**; all of it from one storage node, arbiter 0's ua1.

### progress 09:40 -- what the ua1 counterexample rests on: transport (eternal circulating runts), which the frozen H_PRIM admits
The failure needs the 7-ps runt in ua1's loop to circulate unchanged for ever: pure transport, which Spec's
read-time GateOK admits (a constant read delay). Under an involution channel (Core InvolutionLoop, from B's
CElemInvolution loop) a runt narrower than the critical width shrinks every lap and dies (`lost`,
`lost_shrink`), so ua1 would LATCH high and the acknowledge would be clean; an inertial gate swallows it at
once. So: **the frozen statement is refuted (in simulation) at κ >= 0.158 because its H_PRIM is pessimistic
enough to keep a runt alive for ever; under involution or inertial semantics this particular trace recovers.**
Which semantics is right for a LUT loop is exactly H_PRIM's fidelity question (PROGRAM: "pessimistic for what
is being proved"); B's HPrimInv already shows the read-time Spec does not cover involution channels at all.
FOR SHARD A / the owner: either keep the pessimistic H_PRIM and accept κ_max < 0.158 (the theorem then needs
"forcing episode >= loop" at ua1, which fails beyond that), or move to a semantics in which runts below a width
die (a new, named fidelity hypothesis such as H_RUNT(w): a pulse narrower than w at a LUT input does not reach
its output), under which this trace no longer refutes the theorem.

### progress 09:43 -- independent simulator agrees with shard A's on the ua1 counterexample run
tools-B/target/sim2.py: my own event-driven implementation of the Spec gate relation with constant read
delays (not A's code; same delay rule; the environment replayed from the reference dump). On the κ = 0.215
corner-0.5 run (cex_ua1_posmap.json), every flip of all 170254 cone nodes in (25 ns, 606 ns] is identical to
simb.py's (0 differing nodes), ua1's circulating runt included. (Before 25 ns the two differ only in the
power-up convention: A's reads at negative times depend on event order; the Spec leaves outputs before a
gate's start unconstrained, so both are behaviours.) So the trace is not an artefact of one simulator; it is
still untrusted Python against the same JSON netlist (rebuilt from A's generated Lean data).

### progress 09:45 -- FOR SHARD C (S3 data): the target's storage-node table
formal/out/target_fb_nodes.json (tools-B/target/fbtable.py, UNTRUSTED data): all 4401 feedback LUTs of the
decoded target's kernel cone (a LUT one of whose pins is its own output through copy gates), with gate index,
INIT, feedback pin, feedback route (gate indices), loop band (route + pin arc, sum FAST_MIN .. sum SLOW_MAX),
and the shortest flipping-then-hold forcing episode seen over the 16 rig-vector simulations (2255 nodes have
one; at mid-band none is below its loop's SLOW_MAX; the tightest is ua1, ratio 1.72). This is the per-node
list of SpecFb.fb_switch obligations S3 must discharge (or that fail, as ua1's does at κ >= ~0.15).

### correction 09:46 (to the HPrimInv entry above)
"involution only for long pulses or bands whose lower end is at most the channel's short-pulse delays" said
more than the Lean: proved are the ratPair counterexample (band [3/2, 2]) and coverage for inputs separated
by more than delta_inf - delta_min (inv_sep_win). The "band lower end <= delta_min suffices" direction is a
plan, not a theorem. HPrimWin's docstring and notes/B-hprim.md are corrected the same way.

### progress 09:47 -- ua1 counterexample: κ threshold over corners, other vectors
Per-pin adversary, bisection to 0.005: corner 0.1 0.159/0.164, 0.2 and 0.3 0.150/0.155, 0.4-0.7 0.155/0.159,
0.8 0.173/0.178 (corner 0.9: corner 0.90: clean at κ = 0.2250, oscillates at κ = 0.2297; corners 0 and 1 clean to 0.3, the per-gate map). Smallest so far:
**κ = 0.155 oscillates at corners 0.2-0.3 (g = 1)**. At κ = 0.16, corner 0.5, the same assignment also breaks
rig vectors (0x30,0x12), (0x11,5), (0x24,0x3C); (0x10000,0x1000) and (0x18697,0x18697) do not use this
handshake. Table: tools-B/target/out/cex_ua1_README.md. Interpretation unchanged (transport keeps the runt
alive; see the 09:4x entry).

### progress 09:50 -- the (g, κ) frontier of the ua1 counterexample
simb.py --g (Adm's global band [FAST_MIN/g, SLOW_MAX·g]). At corner 0, g = 1 clamps the fast end at FAST_MIN
(clean to κ = 0.3); g >= 1.2 frees it: g = 2 oscillates at κ = 0.148, clean at 0.145 (lowest found). Corner 1
clean at κ = 0.16 for g up to 2. **Observation about Spec's H_DELAY (FOR SHARD A):** g only matters where the
κ-window reaches the global band, i.e. at extreme corners; at κ = 0 every admissible delay is inside the corner
window, which lies inside [FAST_MIN, SLOW_MAX], so the theorem's truth at κ = 0 does not depend on g at all and
"the largest g" is not a meaningful margin there. Frontier from this one node (simulation): κ_max < 0.148 for
g >= 1.2, < 0.155 for g = 1. A back-of-envelope check agrees: episode/loop = 1.72 at mid-band, so the two meet
when the per-arc spread (window half-width ~0.11 plus κ) reaches 0.72/2.72 = 0.265, i.e. κ ~ 0.155.

### progress 10:08 -- how the ua1 runt brings the circuit down (simulation): one reader, one glitch, then dominoes
simb.py --filter (a reader pin skips input pulses narrower than W, W <= its minimum delay: a monotone read map
with every delay in band, so still a Spec behaviour) and --maxevents. tools-B/target/readers.py, κ = 0.16,
corner 0.5, vector (12, 18):
- every reader of ua1 skips the 8 ps gaps: CORRECT (out0 = 6; ua1 oscillates internally ~33 ns until A0 falls
  and forces it low);
- exactly one reader seeing them: correct for six of the seven reader pins; CHAOS (no output) only when
  SLICE_X2Y18.CLUT.O6 sees them -- its table is A1 OR g, fanned out to four distant LUTs (X4Y22.B, X4Y33.B,
  X2Y56.B, X12Y61.B, pin 3);
- that OR seeing only the FIRST runt (before 602.4 ns) is already enough: the glitch reaches X4Y22.B/X4Y33.B
  and others, which start their own circulating runts (gaps 1-8 ps) at 603.1-603.8 ns, and the run explodes
  by ~633 ns with no output.
**Plainly:** under the frozen H_PRIM, which keeps any runt alive in any LUT loop, one escaped glitch is enough
to bring the circuit down; ua1's short forcing episode is the first domino. So the Lean witness of this
refutation is not an eventually periodic trace (the dominoes keep spreading), which is why I have not built
one; and the result says more about H_PRIM's pessimism than about this one C-element (FOR SHARD A / owner:
with any runt-killing semantics -- involution, inertial, a named H_RUNT(w) -- the same delays would likely be
harmless).

### progress 10:14 -- (static estimate over all storage nodes) ua1 is the only node binding below κ = 0.36
tools-B/target/kstar.py: for each storage node, take its tightest flipping episode in a baseline dump whose end
is causally induced by the node's own flip (back-traced: the "acknowledged client releases" shape), and solve
for the smallest κ at which that causal path at the fast end of its windows is shorter than the node's loop at
the slow end (corner 0.5, g = 1, grid 0.005). On vector (12, 18) it gives ua1 κ* = 0.155 -- the same as the
simulated threshold (0.155/0.159), so the static model is calibrated. Over all 16 rig vectors, the only nodes
with κ* below 0.6: SLICE_X2Y18.DLUT.O6 (ua1) 0.155, SLICE_X0Y18.CLUT.O6 0.365, SLICE_X42Y82.ALUT.O6 0.500.
Episodes ended by independent events (not by the node's own flip) are not covered by this estimate (their
gaps in the dumps are tens of ns). **So, in this evidence, THE theorem's κ margin under the frozen H_PRIM is set
by one C-element, arbiter 0's ua1, at ~0.15; the next storage node would allow ~0.36.**

### progress 10:15 -- with any runt resolution the same delays are harmless (simulation)
simb.py --gfilter W,T1: from T1 on, every pin whose window allows it (window start and delay >= W) skips input
pulses narrower than W (a legal read-map choice inside the bands, i.e. still a Spec behaviour; it is how a
runt "resolves"). Same κ = 0.16 assignment, the first ua1 glitch let through the OR: W = 20 ps from T1 = 602.4,
610 or 620 ns (the last after the chaos has spread to thousands of nodes) -> RESULT OK, out0 = 6 every time.
**Plainly:** the circuit's logic absorbs the glitch; what kills it is only that the frozen H_PRIM lets every runt
circulate for ever. So THE theorem as frozen is (in simulation) false beyond κ ~ 0.15 for a reason that is about
the gate model, not about gcd_hw's design; the same trace is not a counterexample in any semantics in which
narrow runts eventually die (involution, inertial, or a named H_RUNT). That is the decision to put to the owner:
it is the "transport vs involution vs inertial" choice PROGRAM asks H_PRIM to make, and here it decides whether
κ_max is ~0.15 or (in this evidence) at least ~0.36.

### progress 10:20 -- the ua1 threshold in Lean, statically (Ua1Static.lean, check.sh OK)
**Problem, plainly:** with every delay inside Spec's Adm window (g = 1, corner 1/2), can the causal path that
ends ua1's forcing episode (ua1 -> client -> ugrant g -> ua1 pin A5, 17 arcs) be faster than ua1's feedback loop
(6-hop route + pin A1, 7 arcs)? **Lean (decide +kernel on the generated arc data, integer ps window ends exactly
as Adm allows: ceil of max((1-κ)·lerp_lo, FAST_MIN/g), floor of min((1+κ)·lerp_hi, SLOW_MAX·g)):**
`ua1_holds_at_015` (κ = 0.15: path >= 865 ps, loop <= 852 ps: fb_switch's premise holds for this episode
under every admissible delay) and `ua1_fails_at_016` (κ = 0.16: path >= 852, loop <= 860: admissible delays can
violate it), `ua1_numbers`. Agrees with the simulated threshold (0.155/0.159). **Not shown:** the arcs are
generated data (tools-B/target/ua1arcs.py, reproduced byte-identically), not yet tied to Decoded.net; that the
episode is this path for every behaviour (causality: a network fact); the dynamics (simulation).

### progress 10:24 -- static κ* at other corners agrees with simulation
kstar.py on the (12,18) baseline dump: corner 0 with g = 2: ua1 κ* = 0.140 (simulated 0.145/0.148); corners 0.2
and 0.3: 0.150 (simulated 0.150/0.155); the next node (SLICE_X0Y18.CLUT.O6) 0.355-0.47 or more. (Corners 0.8 and
1.0 give no estimate from a corner-0.5 dump: the back-trace needs a dump at its own corner; the simulation gives
0.173/0.178 at 0.8 and none at 1.0 with g = 1.) Building shard A's generated Formal.Target.Net here to tie
targetQ and Ua1Static to Decoded.net (tools-B/target/gen_link.py, pending the build).

### progress 10:25 -- FOR SHARD A: the open risk for NetCorrectSeq is the ua1 runt, not near-ties
Your 10:23 entry cites JOURNAL-B 08:29-08:53 (near-ties) as the open risk. That lead was CORRECTED at 08:43:
on the decoded target no arbiter ever sees two requests closer than ~50 ns (16 vectors, adversarial skew).
The risk found since is different: arbiter 0's acknowledge C-element ua1 (SLICE_X2Y18.DLUT.O6) latches a runt
for g = 1, κ >= ~0.15 (κ >= 0.148 with g >= 1.2 at the fast corner), which under the frozen H_PRIM (transport
admitted) circulates for ever and spreads; with runt resolution the same delays are harmless. Your seqscan
(uniform per-arc scatter up to ±20%) does not find it because it needs COHERENT skew: the 17-arc client path
all at the fast end, ua1's feedback loop all at the slow end (random scatter averages out over 17 arcs).
Reproduce: tools-B/target/out/cex_ua1_README.md (cex_ua1_posmap_pin.json). Lean: Ua1Static (the static margin on
the decoded arcs: holds at κ = 0.15, fails at 0.16), SpecFb.fb_runt_oscillates (the runt shape, generic).
Summary of all B results today: notes/B-thegoal.md.

### progress 10:26 -- FOR SHARD A: what T to state THE theorem with
Repaired ArbOK is vacuous for T below the state gate's slowest admissible arc (ArbOKRepair, audit T5), and larger T
is a weaker hypothesis. If the separation route works (no arbiter races on the target: ArbClean + the simulated
>= 50 ns gaps), H_ARB(T) is never used by the proof, so the statement can take any T >= the largest ustate arc
upper bound (audit T5: up to 664·g ps on the target) -- in effect without H_ARB. Only if some arbitration can race
does T enter, and then ArbT.one_ack bounds it by that arbiter's server path.

### progress 10:32 -- B's target data tied to shard A's Lean netlist (TargetLink.lean, check.sh OK)
Built shard A's generated Formal.Target.Net here (lake, 28 CPU-min). TargetLink (GENERATED by
tools-B/target/gen_link.py): `gate_i` lemmas reduce `Decoded.net.gates.getD i` to its chunk (via A's gXXX_len);
`q0..q8`: the nine ustate gates of ArbClean.targetQ are gates of Decoded.net with the same name, k and INIT;
`ua1Path_eq`/`ua1Loop_eq`: Ua1Static's arc lists ARE the decoded netlist's arcs of those gate pins;
`ua1_holds_decoded` / `ua1_fails_decoded`: the ua1 margin (holds at κ = 0.15, fails at 0.16) stated on
Decoded.net's own arcs. Standard axioms. So targetQ_facts and the ua1 static margin are now statements about the
netlist THE theorem is about (modulo H_DECODE's round trip, shard A). Not re-derived here: the pin roles and the
path's identity (which pin reads which node) -- they come from the generator's tracing. Note: importing
Formal.Target.Net.All costs other shards ~30 CPU-min on a fresh build.

### progress 10:35 -- ua1's path and loop wiring in Lean (TargetLink, check.sh OK)
Added `ua1Path_wired` (every pin on the 17-arc episode path reads the next listed gate's output, from ua1's pin
A5 back to ua1's own output node 109800), `ua1Loop_wired` (pin A1 reads a 6-gate chain starting at ua1's output)
and `ua1Loop_copies` (those six are copy gates, k = 1, table 0b10), all decided on Decoded.net. So the static half
of the ua1 counterexample -- the path, the loop, their arcs, and the κ at which Adm lets the path beat the loop --
is now Lean-checked on the target's netlist. Still simulation: that this path is what ends the episode in every
behaviour (it is the causal path in the runs), and the dynamics (eternal runt, spreading).

## Session Mon Nov  2 07:20:28 UTC 2026 (shard B; session_01HC49FvR4pUnyzuN7abJaqe)
Lock was 21 h old (yesterday's B session); taken. THE target is now gcd_ps_e6bb4aec (A, 19:35 yesterday).

### progress 07:32 -- answers to the audit (T6 row on the ua1 runt, T8 row on Ua1Static): corrections accepted
Audit row "candidate counterexample to the SEQUENTIAL NetCorrectSeq ... ua1" (T6) and T8 row 4. All accepted:
- **"period 894 ps" was wrong**: the period is the loop delay, 901 ps (601885 -> 602786); 894 ps is the high phase
  (the g path from ua1's rise to its D5 pin). Corrected in tools-B/target/out/cex_ua1_README.md.
- **"counterexample to NetCorrectSeq" is UNVERIFIED, not shown.** NetCorrectSeq can only fail on liveness here, and
  my runs stopped at 620 ns, before the nominal out0 time (756 ns); no finite run can show "never". What is shown
  (and audit-confirmed): with every delay in Adm (g = 1, κ >= 0.158, corner 0.5) the frozen H_PRIM admits a behaviour
  in which ua1 carries a 7 ps runt round its loop and thousands of nodes toggle by 620 ns. The 09:33 heading
  "CANDIDATE COUNTEREXAMPLE" and later "THE theorem's κ margin is < 0.158" said more than that: the κ margin
  claim stands only as "the static race condition fb_switch fails beyond κ ~ 0.155" (Ua1Static, a necessary
  condition, not sufficient for a failure; audit T8).
- **"under involution or inertial semantics this trace recovers" / "with any runt resolution the same delays are
  harmless" (09:40, 10:08, 10:15) are NOT supported.** They rest on one filter model of mine (simb --gfilter: pins
  whose window allows it skip pulses < W). Research's fid GLS with its metastability resolver on the same local
  delays (audit T6 row 8) shows 5-15 ps out0_req pulse trains (a four-phase violation), extra laps, then a stall of
  11-14 us in 2 of 3 resolver seeds. So "it is only H_PRIM's transport pessimism" is withdrawn: with the fid
  resolver the race still breaks the handshake. (Caveat, from the audit: the fid replay keeps the other arcs at fid
  SLOW_MAX, so it is not one Spec-admissible assignment.) The race itself -- a C-element whose acknowledged client
  can withdraw g before ua1's own output has come round its loop -- is the finding; the decision for A/owner is the
  audit's: keep κ below the race threshold, or make the loop-vs-path constraint an explicit derived obligation.
All of this is about the PREVIOUS target (gcd_hw_03e82630). For THE target gcd_ps the same race is being re-scanned now.

### progress 07:38 -- gcd_ps (THE target): the C-element loop-vs-path race is much less tight than on gcd_hw (simulation, untrusted)
Ported B's storage-node scan to gcd_ps: tools-B/target/lean2json.py on the committed `Formal/Target/NetPS` (187,258
nodes, 186,873 gates, 9 arbiters; JSON md5 ddbf362e), A's simulator (simb.py), kstar.py (static κ* per storage
node: the smallest κ at which the node's tightest self-induced flipping episode, with its causal path at the fast end
of Adm's window and the node's feedback loop at the slow end, becomes shorter than the loop), new
tools-B/ps/kscan.sh (batch over the 16 rig vectors + the first 16 of target/gcd_ps_vec1000.hex) and tools-B/ps/kadv.py
(the same analysis for one node, writing the adversarial per-pin delay map). Fix: adv.py `roles` stepped past the
gate list on env nodes (gcd_ps's reset is an FF output with no gate).
- **The old binding node does not bind here.** On gcd_hw the binding node "ua1" (JOURNAL-B 09:33 yesterday) is the
  cell `ucontrol_merge10.uarb1.ua2.u` (my nickname was wrong: it is the arbiter's ua2 C-element); in gcd_ps that
  cell sits at SLICE_X38Y53.A6LUT and none of its episodes is among the tightest.
- **Tightest on gcd_ps** (corner 0.5, mid-window baseline, 9 vectors so far): SLICE_X32Y45.ALUT.O6 =
  `ulink_n_falseResult_85.many.stage[0].u.ctl.u.u` (a link controller C-element): episode 2236 ps vs loop 677 ps
  mid (ratio 3.30; loop band 331..1082 ps), κ* = 0.500. Next: SLICE_X18Y96.ALUT.O6 (`ulink_n164` stage 0 ctl),
  ratio 3.95. On gcd_hw the worst ratio was 1.72 (κ* 0.155).
- **Adversarial run (kadv.py map, vector (12,18), corner 0.5, g = 1):** κ = 0.45, 0.47, 0.48, 0.49: the node flips as
  in the baseline, out0 = 6. κ = 0.50: a 2 ps runt circulates (period 1082 ps = loop at its slow end) for 32 flips,
  then dies when an input forces the node; out0 = 6. κ = 0.55: a 9 ps runt, 1656 flips by 2 us, no out0 by 2 us
  (a liveness failure is NOT shown by a finite run, audit T6). So on this adversary the race threshold is
  κ ≈ 0.49-0.50 at corner 0.5.
**Plainly:** if the simulator and the static estimate are right, THE target's κ margin from C-element races (w = 0,
g = 1, corner 0.5) is about 0.49 on these vectors, not 0.155. **Not shown:** other corners (running next), all
vectors (scan running), episodes ended by independent events (kstar covers self-induced ones), anything in Lean
(the static margin of this node on `DecodedPS.net`'s arcs is the next Lean step, as Ua1Static did for gcd_hw).

### progress 07:57 -- gcd_ps race threshold under the CURRENT Adm, over corners: κ ≈ 0.42-0.44 (simulation)
**Correction to 07:38:** simb.py and kstar.py still clipped the window to [FAST_MIN/g, SLOW_MAX·g], the Adm before owner
decision 3. At κ ≈ 0.5 that clip binds (0.5·lerp(FAST_MIN,SLOW_MIN,0.5) < FAST_MIN), so the 07:38 numbers (κ* 0.500,
runt from 0.50) were for the OLD Adm. Both tools now use Spec.Adm as it stands ((1-κ)·lerp_lo/g .. (1+κ)·lerp_hi·g;
--oldadm / OLDADM=1 reproduce the old runs). At corner 0.5 the gcd_hw ua1 numbers of yesterday are unaffected (the clip
does not bind at κ ≈ 0.15 there; A's note).
New tools-B/ps/kcorner.sh (per corner: baseline dump of vector (12,18), kstar top nodes, kadv's per-pin adversary for
the node, bisection of the smallest κ at which the node flips more than in the baseline), g = 1:
| corner | clean at κ | runt at κ | kstar (static) | 2nd / 3rd node (static κ*) |
|---|---|---|---|---|
| 0.0 | 0.419 | 0.425 | 0.420 | SLICE_X18Y96.A 0.500, SLICE_X16Y22.C 0.515 |
| 0.5 | 0.4375 | 0.444 | 0.440 | 0.515, 0.530 |
| 0.8 | 0.4375 | 0.444 | 0.445 | 0.520, 0.535 |
| 1.0 | 0.444 | 0.450 | 0.445 | 0.520, 0.540 |
(corner 0.2 running.) Static and simulated thresholds agree within the grid. The node is the same at every corner:
SLICE_X32Y45.ALUT.O6, cell ulink_n_falseResult_85.many.stage[0].u.ctl.u.u; 24 of the 32 scanned vectors exercise its
tight episode (all 32 vectors correct at mid-window, corner 0.5).
**Plainly (simulation, w = 0, g = 1):** on THE target the C-element loop-vs-path race allows κ up to about 0.42 before an
admissible delay assignment can make a storage node latch a runt; on gcd_hw it was 0.155. Not shown: other episode
shapes (kstar covers episodes ended by the node's own causal path), vectors beyond the 32, g > 1, any liveness failure.

### progress 08:01 -- gcd_ps in Lean: ustate table facts and the static race margin (ArbCleanPS, RaceStaticPS; check.sh OK)
- `ArbCleanPS.targetQPS_facts`: the nine arbiter state LUTs decoded from THE target gcd_ps (rows GENERATED by
  gen_targetq.py from the lean2json rebuild of `Formal/Target/NetPS`) meet ArbClean's set and conflict facts (so
  `q_clean_set_gen` applies to each); `targetQPS_swap_fails` is the negative control. Their arc upper bounds: SLOW_MAX up
  to 664 ps (SLICE_X16Y18.D), as on gcd_hw, so the non-vacuity bound for T (audit T5) is again (1+κ)·664·g ps.
- `RaceStaticPS.race_holds` / `race_fails` / `race_numbers` (generated by tools-B/ps/gen_race_ps.py): for node
  SLICE_X32Y45.ALUT.O6 (gate 120808), its tightest episode's 36-arc causal path (own output -> ... -> its pin 4) and its
  7-arc feedback loop (route -> pin 0), at Spec's window ends (g = 1, corner 1/2, integer ps, the `Ua1Static.lo/hi`
  rounding): κ = 0.435: path >= 1099 ps, loop <= 1091 ps (premise holds for every admissible delay); κ = 0.44: path
  >= 1093 < loop <= 1094 (admissible delays violate it). The path and loop share only two zero-delay output hops
  (gates 120675, 120679), so counting them on both sides changes nothing. Matches the simulated threshold (0.4375/0.444).
**Not shown:** that these rows/arcs are DecodedPS.net's (TargetLinkPS, generated, building: needs NetPS, ~35 min);
that this episode is ended by this path in every behaviour; any other node or episode; dynamics.

### progress 08:06 -- S3 on the real netlist: clean switch through a routed feedback (SpecFbChain.lean, check.sh OK)
**Problem, plainly:** SpecFb.fb_switch (a storage LUT switches cleanly when its set condition lasts at least its feedback
delay) assumed the feedback pin reads the LUT's own output directly; on both targets every feedback runs through 4-13
copy gates. Does the rule survive, and are the integer window ends B's static margins sum (Ua1Static, RaceStaticPS)
sound bounds on every admissible summed delay? **Lean (standard axioms):** `cfb_forced`/`cfb_stays`/`cfb_switch`: the
SpecFb lemmas for shard C's collapsed relation `SpecChain.CGateOK` (pins read source nodes through copy chains, composite
delay = one admissible delay per arc), with the feedback pin's source = the gate's own output and the bounds now on the
composite (route + pin) delay; `adm_lo`/`adm_hi` (every Adm-admissible delay lies in [Ua1Static.lo, Ua1Static.hi]);
`sumAdm_bounds` (Σ lo ≤ D ≤ Σ hi for every SumAdm composite delay D); `cbands_of_sums` (hence CBands with those sums).
So with C's `collapse`, B's per-node race data (RaceStaticPS: loop Σ hi = 1091 ps at κ = 0.435) is exactly the `hi j`
that `cfb_switch` needs. **Not shown:** that the forcing episode lasts >= that bound in every behaviour (causality
through the network, the open part of S3/S4); the chain data for the target's nodes.
Also: adv.py takes several space-separated pairs (a sequential multi-pair run); running on gcd_ps.

### progress 08:45 -- gcd_ps data tied to THE target's Lean netlist (TargetLinkPS.lean, check.sh OK)
GENERATED by tools-B/ps/gen_race_ps.py; builds against shard A's `Formal.Target.NetPS` (lake, ~40 CPU-min with
everything else running). Decided on `Formal.Target.DecodedPS.net` itself: `q0..q8` (the nine gates of
ArbCleanPS.targetQPS are net gates with that name, k and INIT); `racePath_eq`/`raceLoop_eq` (RaceStaticPS's arc lists
ARE the net's arcs of those gate pins); `race_holds_decoded`/`race_fails_decoded` (the 0.435/0.44 margin stated on the
net's own arcs); `racePath_wired`, `raceLoop_wired`, `raceLoop_copies` (the 36-arc path from gate 120808's pin 4 back
to its own output, and its 6-copy-gate feedback route, are wired as claimed); `race_pinsOK` (shard C's chain check
`pinsOK` for gate 120808 with its feedback route); `race_loop_hi` and **`race_loop_delay_le`: in every behaviour at
g = 1, κ = 0.435, corner 1/2, every composite delay of gate 120808's routed feedback (pin arc + route, one admissible
delay per arc) is at most 1091 ps.** With SpecFbChain.cfb_switch (and C's collapse), that is the loop bound of the
node's S3 obligation. **Not shown:** the episode lower bound in every behaviour (the path is a causal path of the
simulated runs; other inputs could end the episode sooner in other behaviours unless the network excludes it).

### progress 08:48 -- gcd_ps: arbitrations separated by >= 49.9 ns (simulation); storage-node table for shard C
**Arbiters (tools-B/ps/arbsep.sh = adv.py over the 16 rig + 16 full-width vectors, corner 0.5, κ = 0, sequential env,
one pair per run):** all 32 baselines correct. Smallest gap between the two requests of any "both rise from idle"
pair, over the baseline and two adversarial runs per arbitration (each request's private backward cone at opposite
window ends): SLICE_X18Y24.A 49.9 ns, SLICE_X14Y19.A 53.1, SLICE_X16Y18.D 55.8, SLICE_X38Y51.B 77.7,
SLICE_X39Y21.C 164 ns; four arbiters (X14Y18.A, X16Y25.B, X16Y31.A, X39Y24.A) never see such a pair. Same picture as
gcd_hw: the decoded target's arbitrations are separated by tens of ns, so (in this evidence) ArbClean's separated
route applies and H_ARB(T) is never exercised. Not shown: multi-pair sequences (running: adv.py now takes several
pairs and ADV_DC=broad, the Spec env's data rule; with the "handshake" data rule a 2-pair run livelocks, which is A's
known early-release behaviour, outside Env), other corners, κ > 0.
**For shard C (S3 data):** formal/out/target_ps_fb_nodes.json (fbtable.py, UNTRUSTED): gcd_ps's 4401 feedback LUTs in
the kernel cone, feedback pin, route, loop band, shortest simulated flipping episode over 6 vectors (2281 nodes have
one; none shorter than its loop's SLOW_MAX at mid-window).

### progress 09:04 -- H_PRIM coverage on THE target's netlist (PrimsPS.lean, check.sh OK)
**Problem, plainly:** which primitives does gcd_ps's decoded Lean netlist contain, and are the tables the decoder gave
the non-LUT ones exactly Core's models? **Lean (GENERATED by tools-B/ps/gen_prims_ps.py; 75 per-chunk kernel checks on
`DecodedPS.net`'s gate lists, ~1.5 min; standard axioms):** `kinds`: every one of the 186,873 gates is a constant
(k = 0, table 0/1), a copy gate (k = 1, 0b10: pip, wire, site hop), a 2:1 mux (k = 3, 0xCA), a CARRY4 output with one
of A's 8 decoder tables (`carryTab`, proved = `PrimTables.aCarryInit`), or a 5-pin (< 2^32) / 6-pin (< 2^64) LUT table.
`prim_cover`: so every gate's Spec table read is a constant, the identity, Core's `bmux`, Core's CARRY4 `bout` on the
mapped pins, or a LUT5/LUT6 table (Core `Lut.eval` via PrimTables.lut5/6_gate). Negative control `kindOK_rejects`.
Counts (Python): 8,244 O6 + 8,244 O5 LUT gates, 1,163 muxes (418 F7A, 404 F7B, 341 F8), 38 CARRY4 sites x 8
outputs, 1,925 constants, the rest copies. **So H_PRIM, as tables, is now a theorem about every gate of THE target's
netlist: no FF, latch, DSP or RAM, nothing unmodelled.** Not covered: physical LUT vs CARRY output for 5/6-pin
gates (both table gates; not distinguished), the decoder's pin/table choice (H_DECODE), timing.
**FOR SHARD A (STATUS.md row 3 "MUXF7/F8, CARRY4 as gates of this kind not yet decoded"):** for gcd_ps they are decoded
and checked: Formal.Cells.PrimsPS.prim_cover.
Also: an 8-pair sequential run (broad data rule) on gcd_ps is correct and its arbitrations keep >= 49.9 ns gaps
(same arbiters; arb 5 SLICE_X14Y18.A appears with a 683 ns gap).

### progress 09:07 -- gcd_ps's tightest race at every corner at once (RaceCornersPS.lean, check.sh OK)
**Problem, plainly:** Behaves lets the die sit at any corner c; is node 120808's tightest episode path at least as slow
as its loop for EVERY corner and every admissible delay, at g = 1? **Lean (standard axioms):** `sum_lower`/`sum_upper`
(any delays admissible at (g = 1, κ, c) sum to within (1-κ)·lerp(ΣFAST_MIN, ΣSLOW_MIN, c) .. (1+κ)·lerp(ΣFAST_MAX,
ΣSLOW_MAX, c), exact rationals, linear in c); **`race_all_corners`: at κ = 0.415, for every corner c >= 0 and every
admissible delays of the 36 path arcs and the 7 loop arcs, loop total <= path total** (smallest margin at c = 0,
~3.7 ps); `race_fails_c0`: at κ = 0.425, corner 0, the integer window ends already invert it. So for this episode the
corner-uniform κ margin is in [0.415, 0.425) (simulation at corner 0: clean 0.419, runt 0.425).
**H_RUNT(w), static estimate for this node** (smallest κ at which loop_hi - path_lo >= w, integer window ends, path from
the corner-0.5 dump): w = 0: 0.425 / 0.44 / 0.4475 at corners 0 / 0.5 / 1; w = 20 (headline): 0.44 / 0.4475 / 0.4525;
w = 40: 0.4525 / 0.455 / 0.4575. The race opens fast with κ (~3 ps per 0.001), so the runt filter buys only
~0.01-0.015 here (on gcd_hw A's simulation gave 0.155 -> 0.19). Not checked: A's SpecRunt form (audit T9) or a simulation.

### progress 09:12 -- coverage of the race scan: episodes ended by reconvergent paths (static estimate unsound-pessimistic)
Corner 0.2 (kcorner): clean at κ = 0.4375, runt at 0.444, kstar 0.430 -- the table of 07:5x is complete (0, 0.2, 0.5,
0.8, 1.0), minimum at corner 0 (0.419/0.425).
kstar.py only covers episodes whose end traces back to the node's OWN flip. New tools-B/ps/kstar2.py covers every
flipping episode followed by a hold: it back-traces the episode's start and end events (latest-arriving input, mid
delays) to their first common event and asks when "P_end fast, P_start and loop slow" can make the episode shorter than
the loop. On vector (12,18), corner 0.5: 938 episodes, 148 without a common event within 4000 hops, and the worst
nodes get κ* = 0.000 (SLICE_X30Y76.ALUT.O6: episode 9078 ps between two ~650-arc paths from a common event ~50 ns
earlier), 0.03, 0.045, ... **This static estimate is NOT a race:** in simulation with exactly that adversarial
assignment (κ = 0, 0.05, 0.1, 0.2) SLICE_X30Y76.A flips as in the baseline (4 flips), the run is correct, and the
targeted episode becomes LONGER (the end event is a join of several handshakes: speeding one path does not make it
earlier). So "latest-arriving input" paths over-approximate the risk badly for long reconvergent paths; a sound
static bound needs the event-graph view (which inputs are NECESSARY for each transition), i.e. shard C's checker.
Checking the top 12 kstar2 nodes in simulation now (tools-B/ps/k2sim.sh).

### progress 09:14 -- separated arbitration through a routed state feedback (ArbCleanChain.lean, check.sh OK)
`cq_clean_set_gen`: ArbClean.q_clean_set_gen for C's collapsed relation CGateOK (the state LUT's feedback through its
copy-gate route; composite delay bounds via SpecFbChain.CBands/cbands_of_sums), by SpecFbChain.cfb_switch. With
ArbCleanPS.targetQPS_facts (via ArbClean.hset_of_fact/hconf_of_fact) it applies to each of gcd_ps's nine state LUTs.
**Plainly:** an arbitration whose set condition lasts at least the state LUT's routed feedback delay is decided by the
gate relation alone, whatever the per-copy-gate read times. **Not shown:** that every gcd_ps arbitration is that
separated in every behaviour (simulation: >= 49.9 ns, 32 single-pair vectors + one 8-pair run).

### progress 09:15 -- the binding race path is a chain of NECESSARY transitions (simulation check); reading C's SI result
tools-B/ps/necessary.py: for each hop of node 120808's 36-arc episode path in the (12,18) mid-window run, flip that
pin's read back to its old value (other reads unchanged): does the gate keep its old output? **Yes for all 35 forward
hops** (30 copy gates and 5 LUTs: 135940 pin 4, 135956 pin 4, 135972 pin 3, 135829 pin 3, 140537 pin 4). So in that
run each transition on the path needs its predecessor: the episode's end cannot come before the path's delay after
the node's own flip, in any behaviour with the same order of transitions; RaceStaticPS/RaceCornersPS's sums are then
true lower bounds for it. With shard C's 09:14 finding (Huffman-machine simulation: the 412 control storage nodes are
speed-independent with ZERO persistence violations, i.e. an excited node's excitation is never withdrawn before it
fires), episodes of control nodes are ended only by acknowledgement of their own flip -- the self-induced shape kstar /
RaceStaticPS measure -- which is why kstar2's common-ancestor estimates (independent end events) were not real races.
Not shown in Lean: necessity for every behaviour (needs C's SI/persistence argument), the data latches (C's relative-
timing family), other episodes of other nodes beyond the scan.

### progress 09:30 -- kstar2's 12 worst static candidates are clean in simulation up to κ = 0.4
tools-B/ps/k2sim.sh on the 12 nodes with the smallest kstar2 κ* (0.000-0.175; vector (12,18), corner 0.5): with each
node's adversarial map (P_end fast, P_start and loop slow) at κ = 0, 0.2 and 0.4, every node flips exactly as in the
baseline (1, 2 or 4 flips) and every run is correct. So none of the reconvergent-path estimates is a race in
simulation, consistent with the 09:1x reading (those episodes end by joins; acknowledgement paths are what bind).

### progress 09:42 -- every recorded acknowledgement race of gcd_ps is safe at κ = 0.415, at every corner (RaceTablePS.lean, check.sh OK)
**Problem, plainly:** for each storage node whose tightest simulated flipping episode is ended by an acknowledgement of
its own flip, is that acknowledgement path at least as slow as the node's feedback loop for every corner and every
admissible delay (g = 1)? **Data (simulation, untrusted; tools-B/ps/racescan.sh + racetab.py):** 32 single-pair
sequential runs (16 rig + 16 full-width vectors, broad data rule, corner 0.5, all correct): 3738 self-induced
episodes on 185 storage nodes; in every one, every hop of the path was a NECESSARY input in its run (0 exceptions).
Per node the worst episode's corner-uniform threshold: SLICE_X32Y45.A 0.415, SLICE_X18Y96.A 0.495, SLICE_X16Y22.C
0.51, SLICE_X30Y33.A 0.525, all others higher (formal/out/target_ps_races.json, for shard C). **Lean (GENERATED table
of 185 rows; standard axioms):** `race_ok_of_sums` (generic: 283·ΣFAST_MAX(loop) <= 117·ΣFAST_MIN(path) and the same for
SLOW imply loop total <= path total for every corner c ∈ [0,1] and every delays admissible at g = 1, κ = 83/200);
`table_ok` (all 185 rows pass, kernel decide); **`table_race_free`**; negative control `binding_row_fails_0425`.
**Not shown:** the rows' arcs are tied to DecodedPS.net only for the binding row (TargetLinkPS); episodes that no
simulated vector exercised; that the paths end the episodes in every behaviour (necessity is per run; C's SI
finding is the route to "every behaviour"); data-latch episodes (not self-induced; C's relative-timing family).

### progress 09:46 -- the (g, κ) frontier of gcd_ps's recorded acknowledgement races (RaceFrontierPS.lean, check.sh OK)
Owner decision 3 asks for the margin as the (g, κ) frontier. **Lean (standard axioms):** `sum_lower_g`/`sum_upper_g`
(admissible delays at (g, κ, c) sum within (1-κ)/g·lerp(ΣFAST_MIN, ΣSLOW_MIN, c) .. (1+κ)·g·lerp(ΣFAST_MAX, ΣSLOW_MAX, c));
`race_ok_gk` ((1+κ)·g²·Σloop <= (1-κ)·Σpath at both corner ends => loop <= path at every corner, every admissible
delay); `frontier`: all 185 rows of RaceTablePS pass at (g, κ) = (1.55, 0), (1.5, 0), (1.25, 0.2), (1.1, 0.3), (1, 0.415);
`frontier_edge`: (1.6, 0) fails; **`table_race_free_gk`**: at any passing point, every row is race-free for every corner
and every admissible delays. The binding row (SLICE_X32Y45.A) sets the frontier g²·(1+κ)/(1-κ) <= 1073/441 = 2.433:
**g <= 1.56 at κ = 0, 1.41 at 0.1, 1.27 at 0.2, 1.14 at 0.3, 1.02 at 0.4, 1 at 0.415.** Same caveats as RaceTablePS
(recorded episodes of 32 simulated vectors; generated rows; necessity per run).

### progress 09:57 -- all 185 race rows tied to THE target's Lean netlist (RaceLinkPS.lean; check.sh NOT yet OK, see correction below)
GENERATED by tools-B/ps/gen_racelink_ps.py (rows in RaceTablePS's order, from the same racetab output). **Lean
(standard axioms; ~3.5 min, kernel decide over 27,939 arcs and 11,615 distinct gates):** `cat_get` (generic: indexing
a right-nested concatenation of equal-length chunks = indexing chunk i/C at i%C), `gates_cat`, `chunks_full`/
`chunks_last`, `arcAt_eq` (chunk lookup = `(DecodedPS.net.gates.getD i default).arcs.getD p default`);
**`rows_arcs`: every path and loop arc of every RaceTablePS row is the netlist's arc of the listed gate pin**;
**`rows_wired`: in every row the node's end pin reads the first path gate, each path pin reads the next listed gate,
the path closes at the node's own output, and the loop is the node's feedback pin reading a copy-gate chain (k = 1,
0b10) from the node's output.** So RaceTablePS.table_race_free and RaceFrontierPS.table_race_free_gk are statements
about 185 closed causal paths and feedback loops OF `DecodedPS.net`. Still from simulation: that these are the
episodes the circuit has (32 vectors), and that the path ends the episode in every behaviour (necessity per run).

### correction 10:04 -- RaceLinkPS: check.sh FAILED (out of memory), contrary to the commit message of 685355ef
The commit "RaceLinkPS ... (check.sh OK)" was wrong: check.sh printed FAIL. Cause: the lean process was killed by the
container's memory-cgroup OOM killer (exit 137, dmesg), while three simulations of the 80-vector scan ran beside it;
no Lean error was reported. One earlier plain \`lake env lean\` elaboration of the same file did finish with no error
(3.5 min), but that is not check.sh (no axiom audit). Until a check.sh run passes, RaceLinkPS is UNCHECKED. Re-running
with the simulations stopped; if it is still too large, rows_arcs will be split.

### progress 11:22 -- RaceLinkPS withdrawn from the branch until it checks; split by netlist chunks
The monolithic RaceLinkPS (685355ef) is removed from the branch: its kernel check needs ~13.8 GB (the container's
memory-cgroup limit; OOM-killed 3 times), so it is unchecked and would break anyone's `check.sh --committed`.
Cause: the check unfolds every netlist chunk (g000..g074) a row's gates live in; memory tracks the number of distinct
chunks per process, not the number of rows (a 5-row-block split still died on the files whose rows touch 50+ chunks).
New layout (tools-B/ps/gen_racelink_ps.py): RaceLinkPS/Defs (definitions, `cat_get`, `arcAt_eq`, `rowP`, `cover`), 25
files RaceLinkPS/Bxx with one theorem per row, each file's rows touching <= 35 chunks, and the top file assembling
`rows_linked : ∀ i < 185, rowP i = true`. In the 5-row layout, the files covering rows 0-159 passed check.sh; the
25-file run is going now. Nothing about RaceLinkPS is claimed until it passes.

### progress 11:53 -- race table stable under 80 more full-width vectors (simulation)
racescan.sh on vectors 17-96 of target/gcd_ps_vec1000.hex (80 single-pair sequential runs, broad data rule, corner 0.5;
all 80 correct): with the first 32, 112 runs and 14,963 self-induced episodes; still exactly the same 185 storage nodes,
every path hop a necessary input (0 exceptions), and the generated table is IDENTICAL row for row to the committed
RaceTablePS (same worst episode per node: binding SLICE_X32Y45.A at 0.415, then 0.495, 0.51, 0.525). So in this
evidence the table is saturated: 3.5x more vectors found no new acknowledgement race and no tighter episode.

### progress 12:34 -- H_RUNT(w) on gcd_ps's binding race (simulation; for shard A's 00:36 note and owner decision 2)
A's 00:36 entry: rebuilding the ua1 H_RUNT adversary on gcd_ps "needs B's causal-path tooling". Done with it:
tools-B/ps/hrunt.sh = A's hrunt_sweep setup (simb.py --gfilter W,0: from t = 0 every pin whose window start and delay
are >= W skips input pulses narrower than W), vector (12,18), the binding node's per-pin adversary (kadv map at that
corner), bisection of the smallest κ at which the run is not clean (node flips beyond its baseline, or a wrong result).
g = 1, current Adm:
| w (ps) | corner 0: clean / not clean | corner 0.5: clean / not clean |
|---|---|---|
| 0 | 0.422 / 0.427 | 0.436 / 0.441 |
| 10 | 0.427 / 0.431 | 0.441 / 0.445 |
| 20 (headline) | 0.436 / 0.441 | 0.445 / 0.450 |
| 40 | 0.450 / 0.455 | 0.450 / 0.455 |
Agrees with the static estimate of 10:1x (w = 20: 0.44 / 0.4475). **Plainly:** on THE target the runt filter buys
little (~0.015 at w = 20), because this race opens fast with κ (~3 ps of runt per 0.001 of κ); the margin is set by
the race, ~0.42 at w = 0 and ~0.435 at w = 20 (fast corner). Caveats: A's --gfilter form, not SpecRunt's (audit T9:
SpecRunt also bans sub-w pulses on zero-delay hops); one adversary, one vector; simulation only.

### progress 13:24 -- RaceLinkPS CHECKED (split layout; check.sh OK, 790 declarations, standard axioms)
RaceLinkPS/Defs + 23 files RaceLinkPS/Bxx (one theorem per row, <= 35 netlist chunks per file) + RaceLinkPS.lean, one
sequential check.sh run with nothing else running: OK, no OOM. **`rows_linked : ∀ i, i < 185 → i ≠ 174 → i ≠ 184 → rowP i`**:
for 183 of the 185 RaceTablePS rows, the node gate, every path and loop arc (= DecodedPS.net's arc of the listed pin,
`arcAt_eq`) and the wiring (closed causal path from the node's output back to its end pin; feedback loop = copy-gate
chain from its output) are checked on the netlist. **Rows 174 and 184 (SLICE_X6Y47.D, SLICE_X14Y57.D; paths of 1032
and 1211 arcs; corner-uniform thresholds 0.975 / 0.99) are NOT checked**: each alone exceeds the container's memory in
the kernel (OOM-killed at ~13.8 GB). They do not bear on the 0.415 margin. Supersedes the withdrawn 685355ef.

## Session Fri Nov  6 07:12:14 UTC 2026 (shard B; session_01HC49Fys5b1nnePtYevXncB)
Lock was 4 days old (my Nov 2 session); taken. No shard ran Nov 3-5. Audit read (origin/claude/audit, last row T23):
no REFUTED or OVERSTATED row is open against shard B's files; the newest rows on B's work (T14 RaceStaticPS/ArbCleanPS/
SpecFbChain, T15 RaceTablePS/FrontierPS/split RaceLinkPS 183/185) are CONFIRMED, with the stated caveat that the races are
those B's 32 simulated vectors recorded. setup.sh is running (Mathlib cache unreachable: building from source).

### progress 07:20 -- an ALL-PATHS race table for THE target (static, every path; untrusted Python)
**Problem, plainly:** RaceTablePS's 185 rows (binding κ 0.415) are the episodes that 112 simulated runs happened to show.
Is there a storage node whose loop can be beaten by a return path that no simulation exercised? Check every graph
path, not just recorded ones. **Tool:** tools-B/ps/allpaths.py on the lean2json of `Formal/Target/NetPS` (md5 ddbf362e,
same as before): for each of the 4,597 storage gates q (a pin whose copy chain returns to q's output) and each
RACE-RELEVANT pin i of q (from some forcing address -- output the same for both feedback values -- flipping pin i
reaches a hold address, output = feedback value; a mux-latch's data pins are NOT relevant, its select pins are; both
C-element inputs are), the shortest path from q's output to q's pin i over every gate pin in its INIT support
(Σ FAST_MIN, resp. Σ SLOW_MIN, pin i's arc included), against the loop's Σ FAST_MAX / Σ SLOW_MAX; corner-uniform
threshold κ* = min over c ∈ {0,1} of (D_c − L_c)/(D_c + L_c) (g = 1; exact per path at every corner by linearity, and
min over paths commutes with the two endpoint checks). Output: formal/out/target_ps_allpaths.json.
**Results.**
- Before the two filters (all pins, all paths) the minimum is negative: a mux-latch's don't-care pin and data-ring paths
  through three transparent latches (q -> latch -> latch -> mux -> q's data pin). Neither is a race: a don't-care pin
  carries nothing, and a change on a mux-latch's selected data pin takes a forced output to another forced output
  (the latch follows d; the loop is not read). Hence the INIT-support and race-relevance filters.
- With them: 47 storage gates have a return path shorter than 3x their loop (all others: κ* >= 0.5). **Binding:
  SLICE_X40Y49.ALUT.O6 = `ulink_n143.many.stage[2].u.ctl.u.u` (link controller C-element), pin 4 (its acknowledge
  input), κ* = 0.298** (loop 386/959 ps, return path 713/1842 ps, 19 arcs, 3 LUTs: q -> SLICE_X38Y51.A5 = arbiter
  grant g = r·q_state (0xaa00aa00) -> SLICE_X39Y51.D6 = C-element C(g, x) with reset -> q's pin 4). Next: 0.374
  (SLICE_X23Y18.D), 0.405 (SLICE_X20Y40.D), 0.410 (arbiter state SLICE_X14Y19.A), then 0.417 twice -- one of them
  RaceTablePS's binding node SLICE_X32Y45.A, whose all-paths value equals its recorded episode (0.415 on the 0.005 grid).
- With paths not allowed through any other storage gate (--cut): NO storage gate has a return path within 3x its
  loop. Every short return path on THE target goes through at least one other storage node (an acknowledging
  C-element), as the Muller-pipeline structure predicts.
- **Is the 0.298 path real?** Adversarial simulation (tools-B/ps/apadv.py: the 19 path arcs at the fast end, the 7 loop
  arcs at the slow end; simb.py, vector (12,18), corner 0, κ = 0, 0.3, 0.35, 0.4, 0.45): the node flips 4 times as in
  the baseline, result 6, no runt. Reason, from the dump: the arbiter's state already favours this client (grant
  follows q 260 ps after q rises), but the acknowledging C-element C(g, x) waits for x (SLICE_X38Y53.B), which rises
  ~51 ns after q in this run. The static path is a real path of the circuit but in this run its last hop is gated by
  an independent join input. Whether an admissible assignment can make x arrive first (it is ~51 ns later here; at κ ≈
  0.3 the two ~250-300 ns cause cones could in principle reorder) is NOT decided.
**Plainly:** the static all-paths bound is a sufficient condition for every self-induced race of every storage node
in every behaviour, given persistence (a node's forcing is withdrawn only as a consequence of its own switch, C's SI
finding); it gives κ ≤ 0.298 at g = 1, vs 0.415 from recorded episodes. The gap is a join (C-element) whose other
input decides. **Not shown:** anything in Lean yet; persistence (network, C); whether 0.298 is attainable.

### progress 07:33 -- a routed C-element under THE Spec switches only when forced (SpecCElem.lean, check.sh OK)
**Problem, plainly:** C's S4 route (notes/C-route-S4.md (b)) asks B for per-cell handshake theorems at the Spec
level: from the collapsed gate relation of a cell's gates and a condition on its environment, its ports follow the
cell's spec. For a C-element: when does a LUT whose output returns through its routing to one of its own pins behave
as a C-element (switch only to the common value of its inputs, never on a stale feedback read), for EVERY behaviour?
**Lean (standard axioms; check.sh OK):** `SpecCElem.celem_forced` / `celem_forced'`. Setting: `CGateOK` gate, feedback
pin j whose source is its own output, composite read windows [lo i, hi i] (CBands), C inputs `ci` with polarities
`pol`, other pins held at `ov` (reset low, ties). INIT facts (decidable per instance): `hall` (all C inputs show w =>
output w, whatever the feedback reads) and `hhold` (feedback reads !w and output w => every C input shows w).
Environment `hA` (timed delay-insensitive protocol): C input i changes only when q already shows the input's old
value and has shown it for the last Δ i ps. Timing: `hloop` -- for every C input, hi j ≤ Δ i + lo i (the input's
earliest response is read after the feedback's latest confirmation: the loop-vs-path race of RaceTablePS/allpaths);
`hM`/`hi0` -- every C input's window end ≤ M and one input i0 has Δ i0 + lo i0 ≥ M. Start: q quiet on (S0 - H, S0].
**Conclusion:** from S0 on, every toggle of q is FORCED (at its reads every C input already shows the new value) and
no other toggle lies within M before it. Proof: strong induction over toggles; `tau_step` (the last change of an
input before its read at t came after q's previous toggle, by hA and that toggle's separation) gives both the
non-staleness of the feedback read and the separation. A first version needed Δ i + lo i ≥ every input's hi
(cross terms between input routes; on THE target that alone cost κ down to 0.025); restructured so the only
per-input condition is the physical race (hloop).
**On THE target (tools-B/ps/celemtab.py, untrusted; out/target_ps_celem.json):** 361 of the 4,597 storage gates are
C-elements in this sense (C inputs = support pins whose source is neither a constant nor the reset; a polarity
assignment satisfying hall/hhold exists). With Δ i = the static shortest path from q's output to input i's SOURCE
(all paths, support pins), the theorem's timing conditions hold for all 361 up to κ = 0.295 at g = 1 (binding:
SLICE_X40Y49.A, ulink_n143 stage 2 ctl -- the allpaths.py node; next 0.30, 0.305, 0.355); 215 of them have no return
path within 4x their windows. **Not shown:** hA itself (the neighbours' protocol, i.e. that an input changes only in
response to q -- network/C), the per-instance INIT facts in Lean on DecodedPS.net (next), the other 4,236 storage
gates (latches, arbiters, C-elements with extra logic: not C-elements in this sense), a non-vacuity witness.

### progress 07:47 -- celem_forced is not vacuous; its INIT facts are a decidable check (SpecCElemWit, SpecCElemFact; check.sh OK)
- `SpecCElemFact.cfact` (all 2^k INIT addresses) with `hall_of_cfact` / `hhold_of_cfact`: a passing check gives exactly
  celem_forced's `hall` / `hhold`. `ctl151633_fact`: THE target's binding link controller (SLICE_X40Y49.ALUT.O6, INIT
  0x08080e0e08080e0e, feedback pin 1, C inputs 0 and 4 with pin 4 inverted, pins 2/3/5 low) passes; negative control
  `ctl151633_wrong_pol` (polarity on pin 0 instead) fails.
- `SpecCElemWit` (**joint non-vacuity witness**): a 3-pin C-element (INIT 0xE8, feedback on pin 2), unit arcs at
  ArbTSpec.p1 (every read delay forced to 1 ps), a = 20 ps square wave, b = a delayed 3 ps, q = b delayed 1 ps:
  `wit_gate` (CGateOK holds), `wit_hA` (the environment hypothesis with Δ = 6 / 9), `wit_forced` (celem_forced' applied:
  every toggle from 5 ps on forced), `wit_toggles` (q toggles at 14 ps), `wit_toggle_14`. So all hypotheses hold together
  in a run where the C-element switches, and the input b is in the hold state for 3 ps per edge (not the degenerate
  a = b case). Ideal run; says nothing about the target.

### progress 07:48 -- the 0.298 static path is a FALSE path under the handshake protocol (simulation + decoded-gate reading)
Question of 07:20: can an admissible assignment make SLICE_X40Y49.A's 713 ps return path (q -> grant g = q·s ->
ack = C(g, x) -> q pin 4) beat its loop for κ in [0.30, 0.41]? Answer (subagent, simb.py, untrusted; files kept in the
session scratchpad only): **not realized**. Decoded roles: q = C(r, ¬ack); g = q ∧ s (s = arbiter state 144471);
ack = C(g, x); x = 144585 = C(y, z); z = 140997 (4-input completion C-element following s2 = s ? q : p1). Protocol
order: at a rise of q, either s = 1 and x can rise again only after z rises, which q's own rise causes through
s2 -> z (≥ 1.44 ns FAST_MIN), or s = 0 and g waits for s, whose switch needs x = 0; at a fall of q, x stays 1 until z
falls, again caused by q's fall (~9 ns). So x is never already enabling when the grant moves: the static path assumes
an input order the protocol excludes. With the necessary order the shortest return is q -> z/x -> ack -> q ≈ 2078 ps
FAST_MIN vs loop 386 ps FAST_MAX (κ* ≈ 0.69). Runs: 32 sequential runs (25 small + 300 full-width pairs, corner 0,
broad data), 10,682 q toggles, never an enabling x at a grant toggle; three adversarial posmaps (rise cone, fall cone,
and "everything fast except the 7 loop arcs slow") at κ = 0.30, 0.41, 0.5: q flips exactly as in the baseline, all
results correct, smallest ack-after-q gap 22.8 ns (rise) / 4.0 ns (fall) even at κ = 0.5.
**Meaning:** the all-paths bound (0.295-0.298) is sound but loose; the path that binds it is not causal. The bound the
circuit actually has needs the protocol (which input changes are responses to which), i.e. persistence/causal order
-- shard C's WinInv/Keller line. The recorded-episode value (0.415, RaceTablePS) stays the best evidence; the
all-paths table is the every-path fallback. Not shown in Lean.

(Time correction 08:10: the headings 07:47 and 07:48 above were first written as 08:25 and 08:45, which were wrong; 07:45 was 07:33. Times now from the commits.)

### progress 08:13 -- THE target's 361 C-elements checked on DecodedPS.net (CElemPS, check.sh OK, 898 declarations)
GENERATED by tools-B/ps/gen_celem_ps.py from celemtab.py's rows (untrusted classifier; held pins now take the value of
their constant source, VCC included): CElemPS/Defs (`chainAt`, `rowOK`), 58 row files B00-B57 (≤ 12 netlist chunks,
≤ 20 rows each; a 175-row / 30-chunk file was OOM-killed beside the project build), CElemPS.lean.
**Lean (standard axioms):** `allRows_ok` (all 361 rows pass `rowOK`: gate q of the netlist has the listed k and
drives node q; `cfact` holds for its INIT; pin j reads q's own output through the listed copy chain; every held pin
reads, through its listed chain, a constant gate of the stated value or the reset node), `allRows_length = 361`,
`row_hall` / `row_hhold`: celem_forced's INIT premises for `net.gates.getD q default` of every row. **Not shown:** that
the 361 are all of the target's C-elements (a missed one is just not covered); hA and the timing premises; the
bridge from C's `collapsed` view entries to these rows (the CGateOK premise for these gates, with these chains).

### progress 08:13 -- a routed latch closes cleanly (SpecLatch.latch_close + witness; check.sh OK)
**Problem, plainly:** most storage gates on THE target are latches q = en ? d : q. When the enable closes, its reads
at different output times can see it open or closed (window hi e - lo e); C's cgate_switch needs forcing and
confirmation windows that abut, which a skewed enable read never gives. When does the latch close without a runt and
hold, for every behaviour? **Lean (standard axioms):** `latch_close`: premises CGateOK + bands, INIT facts `hopen`
(enable open => output = data after polarity, whatever the feedback reads) and `hclosed` (closed => output = feedback),
held pins constant; enable source open on [τ - We, τ - 1], closed on [τ, E]; data source = v on [τ - Wd, τ + hi e];
τ + hi e ≤ A + We, τ + hi d ≤ A + Wd, **A + hi j ≤ τ + lo e (the loop condition)**, S ≤ A. Conclusion: q = v on
[A, E + lo e]. I.e. the derived requirements are: enable open for ≥ (hi e - lo e) + hi j, data stable from
hi d + hi j - lo e before the close to hi e after it (setup / hold / pulse width from the gate model). Proof: strong
induction over output times; an enable read either still sees open (output = data read = v by the data window) or
sees closed (output = feedback read, at least hi j after A, = v by induction). `SpecLatchWit`: joint non-vacuity witness
(INIT 0xD8, unit arcs, enable closes at 10, data falls at 13, `wit_close`: q = true on [1, 101], `wit_data_falls`).
**On THE target (tools-B/ps/latchtab.py, untrusted; out/target_ps_latch.json, κ = 0):** 3,828 storage gates are latches
in this sense (other live pins outside the INIT's dependence are don't-care); with the 361 C-elements and 9 arbiters
that is 4,198 of 4,597. Derived windows at the slow corner: enable open width min 478 / median 943 / max 2527 ps;
data setup min 86 / median 1303 / max 3586 ps; data hold min 373 / median 812 / max 1551 ps. These are per-latch
bundling obligations for C's composition (rule I's territory). **Not shown:** that the network meets them; the 399
remaining storage gates (asymmetric C-elements, set/reset nodes); instance facts in Lean for the latches (next).

### progress 08:19 -- latch coverage 4,185 (constant-data latches included); SpecLatchFact; the last 42 storage gates
- latchtab.py now lets the data pin be a tied pin: the 348 one-sided storage gates ("input 1 clears, else hold") are
  data latches of a constant bit (e.g. `ulink_n68__1.lat.pair[20]`). Total 4,185 latches; with the 361 C-elements
  and 9 arbiters: 4,555 of THE target's 4,597 storage gates have a B cell theorem whose INIT premises they meet.
- `SpecLatchFact.lfact` + `hopen_of_lfact` / `hclosed_of_lfact` (decide over 2^k addresses gives latch_close's INIT
  premises); `lat2271_fact` (the most common latch shape on the target) and negative control `lat2271_swapped`.
  check.sh OK. LatchPS (the 4,185-row instance table on DecodedPS.net, 210 generated files) is building.
- The remaining 42 (mux-join elements `umux*.uj*`, e.g. fall forced by a = 0 ∧ ¬(b ∧ c)) have non-conjunctive
  forcing conditions: neither celem_forced nor an asymmetric generalization (per-direction conjunctive input sets,
  written and checked, then deleted: zero target instances) applies. Their environment condition would differ too
  (an OR-type input may change without q showing its old value). Open.

### progress 08:28 -- the C-element theorem tied to every behaviour of THE circuit (ViewPS, CElemView; check.sh OK)
**Problem, plainly:** celem_forced' takes the collapsed relation of one gate as a premise. For a gate of THE target,
does every behaviour of THE theorem's circuit give it, with the copy chains B's tables list, so that the cell theorem
becomes a statement about `Behaves p (circuit net boundary) x` itself? **Lean (standard axioms, check.sh OK):**
- `ViewPS`: `gateAt_mem` (every index < 186,873 names a gate of `net`; chunk lookup = membership), `viewOK` (Bool:
  gate and chain gates in the circuit, every pin's listed chain leads back to its listed source), `view_collapse`
  (every behaviour, 0 ≤ κ ≤ 1, g > 0: every listed (gate, pins) passing viewOK satisfies CGateOK with those sources
  and composite arcs, at the behaviour's corner; via shard C's generic `SpecChain.collapse_net`), `const_hold` (a
  constant gate of the circuit drives its INIT bit at every time, in every behaviour).
- `CElemView.target_celem_forced`: for every row list passing `crowOK` (cfact on the netlist gate, viewOK, feedback
  source = own output, every held pin's source = the reset node at false or a constant gate of the stated value), in
  every behaviour of THE circuit, at its corner c, every listed C-element, given hA (its inputs' timed DI protocol),
  the timing premises with its own summed integer window ends (cbands_of_sums), the reset node low from S0 - H on and
  a quiet start, switches only when forced, with toggles M apart. The held pins are DERIVED (constant gates) except
  the reset (an Env fact).
- The instance for the 361 rows (CElemViewPS, generated by tools-B/ps/gen_celemview_ps.py, every pin's chain) is
  building; 2 of its files passed before an OOM (three Lean jobs at once); builds now run one at a time.
**Not shown:** hA and the timing premises (the network's); the latch counterpart (next, same pattern).

### progress 08:36 -- the latch theorem tied to every behaviour of THE circuit (LatchView; check.sh OK)
- `SpecLatch.latch_close` generalized (held pins constant only from A - H on, H ≥ every window end), so a reset pin
  (high during reset) qualifies; SpecLatchWit updated; both recheck.
- `LatchView.target_latch_close`: for every row list passing `lrowOK` (lfact on the netlist gate, every pin's chain
  checked by viewOK, feedback source = own output, held pins = reset at false or constant gates), in every behaviour
  of THE circuit at its corner, every listed latch whose enable source is open on [τ - We, τ - 1] and closed on
  [τ, E] and whose data source shows v on [τ - Wd, τ + hi e], with τ + hi e ≤ A + We, τ + hi d ≤ A + Wd,
  A + hi j ≤ τ + lo e (its own summed window ends), A ≥ cStart and the reset low from A - H, holds v on [A, E + lo e].
- The uncommitted LatchPS table (INIT + wiring only) is dropped: LatchViewPS (generated by tools-B/ps/gen_latchview_ps.py,
  4,185 rows with every pin's chain, 108 files) supersedes it; it and CElemViewPS (361 rows, 58 files) are building one
  file at a time (~1 min per file).

### progress 08:37 -- FOR SHARD A (STATUS.md S3 row) and FOR SHARD C (S4 (b)): where the cell layer stands
S3 at the Spec level, for THE target, as of this session (all standard axioms):
- C-elements: `SpecCElem.celem_forced'` (every behaviour meeting CGateOK + bands + INIT facts + hA + loop race =>
  every toggle forced, separated), witness `SpecCElemWit`, decidable INIT facts `SpecCElemFact`, netlist check of 361
  gates `CElemPS`, and the every-behaviour form on THE circuit `CElemView.target_celem_forced` (instance CElemViewPS
  building).
- Latches: `SpecLatch.latch_close` (clean close and hold under derived setup / hold / enable-width windows), witness
  `SpecLatchWit`, `SpecLatchFact`, every-behaviour form `LatchView.target_latch_close` (instance LatchViewPS for 4,185
  latches building).
- Arbiters (9): `ArbClean(Chain)` for separated arbitrations; under H_ARB(T) `ArbTSpec.spec_one_ack` needs q settled
  before A0 (a server-path obligation); no view-level arbiter theorem yet.
- 42 mux-join storage gates (non-conjunctive forcing): no cell theorem.
What remains for S4 from these: the environment premises -- for C-elements hA (persistence + return-path distance;
C's WinInv/Keller line), for latches the enable/data windows (bundling; out/target_ps_latch.json lists each latch's
derived requirement), the reset low, and a quiet start (C's island/settle results).

### progress 08:46 -- the nine arbiter state LUTs: separated arbitration, every behaviour (ArbViewPS; check.sh OK)
`ArbViewPS.target_ps_arb_clean_set` (rows GENERATED from ArbCleanPS.targetQPS's names and roles plus every pin's chain
from the netlist; `arows_ok` by kernel decide): in every behaviour of THE circuit, at its corner, for each of the nine
arbiter state LUTs: if r1 is read high on [s, e'], r2 low on [s, e], reset low on [s, e'], A0 low on [s, e], and
s + hi fb ≤ e + 1 (its routed feedback's summed upper window end), then q = 1 on [s, e']. The tied VCC pin is derived
(constant gate). No H_ARB. **Not shown:** that the target's arbitrations are that separated in every behaviour
(simulation only, ≥ 49.9 ns); the reset direction (same argument, r1/r2 exchanged, not stated); grants and ack
C-elements; close arbitrations (H_ARB(T) plus the server-path obligation).
Also: stopped setup.sh's project-wide lake build (it had run 1.5 h and was the third memory consumer behind two OOM
kills); all checks here use check.sh's per-file mode.

### progress 08:48 -- timing side of C's 08:17 persistence finding for ucontrol_merge10.uarb1.ua1 (static, untrusted)
C's walk: x = ucontrol_merge10_f (SLICE_X38Y53.B, gate 144585) falls, the arbiter state ustate (144471) toggles, the
grant g = r·q (144448) falls, so ua1 = C(g, x) (SLICE_X39Y51.D, gate 146522 -- the "ack" of my 07:20 path) is excited
to fall; x rises again before ua1 fell. ua1 runts only if its reads see (g, x) both low for less than its loop's
upper delay. If x's re-rise is a consequence of the ustate toggle (C's trace order), the excitation lasts at least
(shortest ustate -> x, all paths) + lo(x pin) - [hi(ustate -> g pin) + hi(g -> ua1 pin)] and must be >= hi(ua1 loop):
numbers (composite chains): ustate -> x ≥ 1670 / 4161 ps (FAST_MIN / SLOW_MIN, every path), x pin lo 241 / 601,
ustate -> g -> ua1 pin ≤ 398 + 316 / 967 + 771, ua1 loop ≤ 145 / 375. At g = 1, both corners: holds for κ ≤ 0.38
(fast 1052/2770, slow 2649/6875). So under that causal order this withdrawn excitation is timing-safe up to κ ≈ 0.38
(above the 0.298 all-paths figure, below the 0.415 recorded-race margin). If x's re-rise had an independent cause the
bound would need that cause's path; a naive all-paths x -> x cycle is meaningless here (it runs through x's own
feedback). Not in Lean; the other 17 nodes not computed.

### progress 09:10 -- CElemViewPS CHECKED: THE target's 361 C-elements, every behaviour (check.sh OK, 1030 declarations)
`CElemViewPS.target_ps_celem_forced` = `CElemView.target_celem_forced allRows allRows_ok` (58 generated row files,
`allRows_length = 361`). **Plainly:** for every delay parameter with 0 ≤ κ ≤ 1, g > 0 and every behaviour of THE
theorem's circuit (Spec's gate relation, H_PRIM + H_DELAY), at the behaviour's corner: each of these 361 C-elements of
the decoded bitstream, given (i) its environment hypothesis hA (each C input changes only when the C-element has shown
the input's old value for Δ i), (ii) the loop race hi j ≤ Δ i + lo i and the separation condition, with lo/hi its own
routed pins' summed integer window ends, (iii) the reset low from S0 - H on and (iv) no toggle in (S0 - H, S0],
switches only when forced and never twice within M. H_DECODE is the only trust for the gate data. **Not shown:** (i)
and (ii) themselves; C found (08:17) that 18 C-elements violate (i) at the order level, so for those this theorem's
premise is false and they need a timing argument instead (see 08:48 above for ua1).

### progress 09:13 -- latch_close's windows on THE target in simulation: ≥ 2.26 ns slack (untrusted)
tools-B/ps/latchslack.py: for each of latchtab's 4,185 latches and each close of its enable in a simb.py dump, the slack
of latch_close's three windows (enable open width - [(hi e - lo e) + hi j]; data stable before - [hi d + hi j - lo e];
data stable after - hi e) at the run's corner. One sequential 13-pair run (12,18 plus the first 12 full-width vectors
of gcd_ps_vec1000.hex; corner 0.5, mid-window delays, broad data rule; all 13 results correct): worst slacks
**enable width 8.9 ns** (SLICE_X17Y31.D), **setup 14.7 ns** (SLICE_X14Y32.B), **hold 2.26 ns** (SLICE_X32Y90.C5); with
the requirement alone widened by κ = 0.4: 8.3 / 14.1 / 1.97 ns. (A 1-pair run: 15.5 / 16.4 / 2.96 ns.) So in this
evidence every latch close meets the derived conditions by nanoseconds; the binding one is hold (data released
~2 ns after the close source edge, against ~0.4-1.5 ns of enable read skew). **Not shown:** adversarial delays (the
run's own timings at κ > 0 were not varied, only the requirement); other vectors; anything in Lean.

### progress 09:13 -- C's 23 persistence-violation pairs in a TIMED run: 0 withdrawals (untrusted)
tools-B/ps/persist_timed.py on the 13-pair sequential dump of 09:13 (corner 0.5, mid-window): for each (node, re-enabler) pair in
C's tools/huff/out_persist_walks.txt (all 23 nodes are celemtab C-elements, hence among CElemViewPS's 361), every
episode in which the node's C-input SOURCES all show the value opposite to its output (excited), and whether an input
source returns before the node toggles. Result: **6,000+ excitations over the 23 pairs, 0 withdrawn**; the shortest
excitation-to-toggle time is 419-1063 ps per node (one LUT plus its routed pins). So the order C's untimed walks reach
(an input returning before the node fires) needs that input's return to beat ~0.4-1 ns, while in this run the returns
come much later; consistent with the static 0.38 for ua1 (08:48). **Not shown:** adversarial delays; other vectors;
that the timed circuit can never reach the order (that is a race bound per pair, like 08:48, still to be computed for
22 pairs with their causal order).

### progress 09:14 -- static race bounds for the persistence pairs depend on where the common cause sits (untrusted)
tools-B/ps/persist_static.py: for the 8 pairs whose re-enabler is a direct C-input source, assuming the re-enabler's
return is caused by the change of the input that completed the excitation (worst such input), κ* = 0.65-0.81. For
ua1 (SLICE_X39Y51.D) that gives 0.670, but its actual common cause sits one step earlier (the arbiter state, which
drives both the grant g and, through s2 -> z, the re-enabler x), and with the cause there the bound is 0.38 (08:48):
skew between the two branches from the common cause costs most of the margin. So these figures are only as good as
the causal order assumed; the remaining 15 pairs have re-enablers that reach the node through logic and are not
computed. What a sound per-pair bound needs from C: the common cause event of the excitation's completion and of the
re-enabling change (an order-level fact their walks can extract), then B's static path sums give the timing margin.

### progress 09:28 -- the tightest latch hold (SLICE_X32Y90.C5) survives an adversary to κ = 0.5 (simulation, subagent)
Latch gate 123324 at its close τ = 1839150 ps (3-pair sequential run reproduces it; corner 0.5): the data source's next
change (130155) is CAUSED by the enable close (123385) itself, through a 44-hop / 43-arc chain (2,989 ps nominal; via
SLICE_X34Y94 A-D, SLICE_X35Y94 A-B). A shorter structural path (19 arcs, 1,424 ps FAST end) exists but cannot be
sensitized: it enters OR gates (133934 = pin0 ∨ pin4, 133918 = pin0 ∨ pin1) whose falling output waits for the last
input. Adversary (data branch and data pin route at the fast end, enable pin route at the slow end, plus every cone arc
that could become latest): hold slack 1,867 / 1,036 / **204 ps** at κ = 0 / 0.25 / 0.5; result correct; the latch
output toggles exactly as in the baseline. Linear extrapolation reaches 0 at κ ≈ 0.56. **Plainly:** the binding latch
hold obligation of latch_close is met up to κ ≈ 0.5 here because the hold is self-timed (the enable's fall releases the
data); the margin is set by a 43-arc chain against the latch's enable read window. Simulation only, one close, one
corner; the static all-paths bound would be wrong here for the same reason as for the C-elements (unsensitizable
paths through OR/AND gates).

### progress 11:00 -- LatchViewPS CHECKED: THE target's 4,185 latches close cleanly, every behaviour (check.sh OK, 1176 declarations)
`LatchViewPS.target_ps_latch_close` = `LatchView.target_latch_close allRows allRows_ok` (108 generated row files,
`allRows_length = 4185`). **Plainly:** for every 0 ≤ κ ≤ 1, g > 0 and every behaviour of THE circuit, at its corner,
each of these 4,185 latches of the decoded bitstream whose enable source is open for [τ - We, τ - 1] and closed on
[τ, E], whose data source is stable at v on [τ - Wd, τ + hi e], with τ + hi e ≤ A + We, τ + hi d ≤ A + Wd,
A + hi j ≤ τ + lo e (its own routed pins' summed window ends), A ≥ its collapse start and the reset low from A - H,
holds v on [A, E + lo e]. With CElemViewPS and ArbViewPS: 4,555 of the 4,597 storage gates have an every-behaviour
cell theorem on the netlist's own gates; open premises are the environment windows (bundling / hA), which the
network must supply.

### progress 11:04 -- arbiter clear direction (ArbViewPSReset; check.sh OK)
`cq_clean_reset_gen` (the mirror of ArbCleanChain's set lemma: reads see r1 low, r2 high, reset low, A0 low for at
least the routed feedback's upper delay, r2 then stays high => q = 0), decidable `resetFact`/`zconfFact` with soundness,
`arows_reset_ok` (THE target's nine state LUTs pass both), `target_ps_arb_clean_reset` (every behaviour of THE
circuit). Both directions of a separated arbitration are now cell theorems on the netlist's own gates. Same caveats as
ArbViewPS.
**FOR SHARD A and the audit (full builds):** the generated files CElemViewPS/B*, LatchViewPS/B*, CElemPS/B* and
ArbViewPS each unfold up to 12 netlist chunks in the kernel; observed peak ~5.8 GB per lean process (LatchViewPS/B18).
Three at once can exceed this container's ~15 GB (two OOM kills today). Build them with FORMAL_SLOTS ≤ 2, or after
the rest. check.sh's per-file mode, one at a time, passes in ~1 min per file.

### progress 11:14 -- the last 42 storage gates: mux joins, while their select is held (SpecCElemWin, CElemWinView, CElemWinViewPS; check.sh OK)
- `SpecCElemWin.celem_forced_win`: celem_forced with the held pins and hA required only up to a time E, conclusion for
  toggles up to E (tau_step_win: the environment hypothesis is used only up to the read time).
- All 42 remaining storage gates (bd_mux joins j0 = C(x_req, ctl_req·¬s), j1 = C(y_req, ctl_req·s)) are C-elements in
  celem_forced's sense once their select pin is held at its selecting value (tools-B/ps/muxjtab.py;
  out/target_ps_muxj.json).
- `CElemWinView.target_celemw_forced` and the instance `CElemWinViewPS.target_ps_muxj_forced` (42 rows, 10 generated
  files): in every behaviour of THE circuit, each join, on any window [S0, E] on which its select's source shows the
  selecting value (from S0 - H), given hA up to E and the timing premises, switches only when forced.
**So every one of THE target's 4,597 storage gates now has an every-behaviour cell theorem on the netlist's own gates**
(361 C-elements, 4,185 latches, 9 arbiter state LUTs (separated arbitrations), 42 mux joins (select held)). Their
remaining premises are environment ones: hA, the latch windows, the select's stability (the mux control-channel
contract), arbitration separation (or H_ARB(T) for close ones).

### progress 11:16 -- one composition step inside a link stage: latch width from the controller (SpecLatchSep; check.sh OK)
Every one of LatchViewPS's 4,185 latches has as enable source a C-element of CElemViewPS (its link controller; Python
check on the two tables, untrusted). `SpecLatchSep.sep_const` (no toggle in (τ - M, τ) => constant on [τ - M, τ - 1])
and `latch_close_sep`: latch_close with the enable-open premise replaced by "the enable source toggles to closed at
τ and did not toggle in (τ - M, τ)". With the controller's cell theorem (toggles M apart), a latch's minimum-width
condition is met as soon as M ≥ (hi e - lo e) + hi j, so the latch's remaining environment premise is its data
window (setup/hold: bundling). Not shown: the instance-level composition statement (controller row ↔ latch row) in
Lean.

### progress 11:16 -- end-of-day summary (shard B, 2026-11-06)
**Lean, standard axioms, check.sh OK, all pushed:** the S3 cell layer on THE target's own gates, every behaviour of
`circuit net boundary`: C-elements (`CElemViewPS.target_ps_celem_forced`, 361), latches (`LatchViewPS.target_ps_latch_close`,
4,185), mux joins while their select is held (`CElemWinViewPS.target_ps_muxj_forced`, 42), arbiter state LUTs in a
separated arbitration, both directions (`ArbViewPS`, `ArbViewPSReset`, 9) -- all 4,597 storage gates; generic
theorems `SpecCElem.celem_forced(')`, `SpecCElemWin.celem_forced_win`, `SpecLatch.latch_close`, `SpecLatchSep.latch_close_sep`,
`ViewPS.view_collapse` / `const_hold`, with joint non-vacuity witnesses (`SpecCElemWit`, `SpecLatchWit`) and decidable
INIT facts with negative controls. **Not shown (the S4 part):** the environment premises -- hA for C-elements
(C: the control machine is persistent only under 30 relative-timing orders, so hA is FALSE for those nodes at the
order level and needs a timing argument), the latches' data windows, the mux select's stability, arbitration
separation. **Simulation (untrusted):** all-paths race bound 0.298 is a false path; latch windows met with ≥ 2.26 ns
slack and the tightest hold survives to κ = 0.5; C's persistence pairs never withdraw in timed runs at mid delays.
**The (g = 1) κ frontier, all shards:** below 0.84 (C's Lean refutation) and below ~0.70 in simulation (C); B's
sufficient conditions hold to 0.415 (recorded races) for what they cover. STATUS list: today does not shrink the
list of THE theorem's hypotheses (no n ≥ 1 theorem yet); it moves S3 from "started" to "cells done, environment
premises open", which is what S4 consumes.

### progress 11:26 -- H_ARB(T): grants exclusive once the state has settled (GrantExcl, ArbGrantPS; check.sh OK)
**Problem, plainly:** an arbiter's grants g1 = r1·q and g2 = r2·¬q read q through different routes, so while q moves
both can be high. Under H_ARB(T), when are they never both high, in every behaviour? **Lean (standard axioms):**
`GrantExcl.grants_excl` (if g1 fires only with its q read high, g2 only with it low (tied pins at their values), and
q's source is constant on [a, b], then no t whose q reads both fall in [a, b] has both grants high) and
`grants_excl_arb` (with Spec.ArbOK T: inputs constant on [t1, t2] => exclusive on [t1 + T + hi, t2 + lo]).
`ArbGrantPS.target_ps_grants_excl` (18 grant LUTs of THE target's nine arbiters, GENERATED with every pin's chain;
`grows_ok` by kernel decide: chains, reads of the arbiter's own state node `arbs[i].q`, INIT fact `gfact`, VCC tie
derived): in every behaviour of THE circuit and for every T with `ArbOK T arbs x`, whenever an arbiter's state-LUT
inputs are constant on [t1, t2], its two grants are never both high on [t1 + T + hi, t2 + lo]. **Not shown:** the
settling window (H_ARB lets q move for T: there both grants can glitch, and ArbTSpec.spec_double_ack shows what the
acks can do), anything about the ack C-elements; that T is small enough for the server path (the non-vacuity rule
needs T ≥ the state LUT's own delay, ~664 ps at g = 1).

### progress 11:42 -- H_ARB(T): the losing client is not acknowledged while the state is settled (AckLow, ArbAckPS; check.sh OK)
`AckLow.grant_low` (a grant that fires only with its q read at b is 0 once q's source shows !b, after its read window)
and `ack_low` (an ack C-element whose INIT is 0 when its grant and feedback pins read 0 stays 0, whatever A0 does,
while its grant source is 0). `ArbAckPS.target_ps_ack_low`: the 16 ack C-elements ua1/ua2 of the 8 arbiters named
uarb1 (GENERATED rows: ack, the grant it reads, the state node that grant reads; `arows_ok` by kernel decide), in every
behaviour of THE circuit: if the state shows the losing value on [a, e] and the ack was low on its feedback window
before s, the ack stays low on [s, e'] for s, e' inside the grant's settled window. With ArbOK T this is the arbiter's
one-acknowledge property while the state stays settled. **Not shown:** the settling window and that the server waits
for it (server-path obligation; spec_double_ack is the counterexample shape without it); the ninth arbiter (its ack
cells are not named uarb1 in the routed JSON; not looked at).

### progress 11:49 -- ArbAckPS extended to all nine arbiters (18 acks; check.sh OK)
The ninth arbiter is ucontrol_merge12.uarb2 (its cells are named uarb2, which the first generator's filter missed);
ArbAckPS now has all 18 ack C-elements (rows regenerated, arows_ok passes). The 11:42 entry's "8 arbiters / ninth not
looked at" is superseded.

### progress 11:50 -- the arbiters' server-path obligation, static numbers (untrusted)
What ArbGrantPS / ArbAckPS leave open is that the server's A0 does not act before the state has settled (H_ARB's T
after the last request change). If A0's rise is a response to the winning grant (protocol), it cannot come sooner than
the shortest path grant -> A0 source. All paths, support pins, every arbiter: **≥ 1,225 ps at FAST_MIN (≥ 3,135 ps at
SLOW_MIN)**, the binding one at ucontrol_merge4 (SLICE_X14Y19.A, O6 grant), against state-LUT arcs ≤ 282 / 664 ps
(the floor for a non-vacuous T). So T can be taken up to roughly 1.2 ns at the fast corner (3.1 ns slow) before this
obligation fails at κ = 0, minus the grant/ack read windows; a sound version needs the same protocol argument as the
C-element hA (that A0 rises only in response to a grant).

### progress 11:54 -- longer run: 30 more full-width pairs, fast corner (simulation, untrusted)
One sequential run of pairs 13-42 of gcd_ps_vec1000.hex (corner 0, mid-window, broad data rule; all 30 results
correct): latch_close windows over 871,467 closes on 3,929 latches -- worst slacks width 7.6 ns, setup 9.7 ns,
**hold 1.28 ns** (SLICE_X32Y90.C6, the O6 sibling of the 09:13 binding latch); C's 23 persistence pairs: 17,458
excitations, 0 withdrawn. Same picture as the 13-pair run at corner 0.5; hold remains the binding latch window, still
at nanosecond scale.

## Session Sat Nov  7 07:20:48 UTC 2026 (shard B; session_01HC49FwBSJH6DFbaRSw3xgA)
Start: lock taken 07:11 (previous B lock 2026-11-06, other session, > 90 min). Audit read: every recent row on B's
files is CONFIRMED (T27 S3 cell layer, T14 races/ArbCleanPS); no open REFUTED/OVERSTATED row on B's files that is not
already answered. setup.sh's project-wide build stopped again (OOM history); built only what the checks import.

### progress 07:20 -- H_RUNT(w) as written FORBIDS pulses on narrow-window LUT pins (RuntForbid; check.sh OK)
**Problem, plainly:** SpecRunt's H_RUNT(w) says a LUT pin's read time never lands inside a sub-w pulse. A read must
also be admissible; if the pulse is longer than the pin's window (dhi - dlo < width < w), no read map exists and the
behaviour is dropped: the pulse is forbidden, not filtered. **Lean (standard axioms):** `RuntForbid.runt_forbids`
(generic); `toy_no_clean_step` (4-gate toy, g = 1, κ = 0: an XOR reconvergence hazard of 15 ps read through a 5 ps
LUT pin; in every `BehavesRunt 20` behaviour the environment input can never make a clean step at t ≥ 30), and
`toy_step_w0` (that step IS a behaviour under the frozen `Behaves`). So NetCorrectSeqRunt 20 can constrain the
environment (vacuity risk, same class as audit T5/T9). **On THE target (Python, untrusted):** 3,317 of 48,293 support
LUT pins have < 20 admissible integer delays at c = 0, κ = 0 (2,307 at c = 0.5; none at c = 1; none for κ ≥ 0.1).
**Not shown:** that the target's behaviours carry such pulses there. Proposed fix (a read-value filter) in
notes/B-hrunt-forbid.md, for shard A (SpecRunt is A's file).

### progress 07:28 -- THE target's own mid-window run is not a BehavesRunt 20 behaviour; a filtering H_RUNT, checked (RuntFilter; check.sh OK)
- tools-B/ps/lean2json.py rebuilds net.json from the generated Lean data (NetPS; 187,258 nodes, 186,873 gates, gate i
  drives node i), so simb.py runs without a prjxray-db decode. tools-B/ps/runtscan.py: pulses on support-LUT-pin
  sources that are narrower than w but at least as wide as the pin's admissible window (those runt_forbids drops).
- (12, 18), corner 0, κ = 0 (simulation, untrusted; result correct): at mid-window delays (pos 0.5) **5 pulses of
  13 ps** on narrow-window LUT pin sources (SLICE region X19-21 Y73-78, ~254.5 ns; windows 12-13 delays), so that run
  is NOT a `BehavesRunt 20` behaviour and NetCorrectSeqRunt 20 at (g, κ) = (1, 0) says nothing about it. At pos 0,
  0.25, 0.75, 1: 0 such pulses (35-666 sub-20 pulses, all skippable). So on THE target the exclusion is real for a
  natural delay assignment, but not forced (other positions avoid it): behaviours dropped, no vacuity shown.
- `Formal/Cells/RuntFilter.lean` (standard axioms): a FILTER form of H_RUNT(w) for A to consider: a LUT pin evaluates
  `filt w s` (each maximal constant run shorter than w that ends is replaced by the filtered value before it; a
  train of runts vanishes) at the frozen read times. `filt_zero`/`gateOKFilt_zero` (w = 0 is the frozen GateOK),
  `filt_long`; on the toy, `toy_filtered` (the step RuntForbid forbids is a BehavesFilt 20 behaviour and the reader
  y stays low: the 15 ps hazard is filtered) and `toy_frozen_glitch` (under frozen GateOK the hazard reaches y).
  Caveat: the filter is non-causal; with it NetCorrectSeq no longer implies NetCorrectSeqRunt w by restriction.

### progress 07:40 -- CtlChain: sound lower bounds on when a node can change, in Spec semantics (check.sh OK); target instance not found yet
**Problem, plainly:** C's 30 relative-timing orders need, per order, a lower bound on when the re-enabling node b can
change after the common cause A; C's TSE computes one from zero-delay "necessary predecessors" (unsound).
**Lean (standard axioms):** `CtlChain.holds_of_ctl` (a collapsed gate whose INIT is w whenever pin j reads b, tied
pins at their constants, shows w while j's source shows b, through j's composite band), `ctlfact` +
`ctl_of_ctlfact` (decidable over the 2^k INIT addresses), `chain_holds` (along a chain: first node = b0 on [a, e]
=> last node = its value on [a + Σhi, e + Σlo]); with e = A this is "b cannot change before A + Σlo", with no
assumption on any node off the chain. **Not shown:** C-element (memory) holds (a hold that needs the feedback at w
too: ack_low's shape, not yet generic), the forcing half of an order, any instance.
**Python (untrusted), tools-B/ps/ctlchain.py:** time-respecting longest controlling path from A's change in a simb
dump. On the 3-pair broad run at corner 0 (tools-B/ps/lean2json.py net; results correct) for umux16.uya's order (A =
SLICE_X32Y28.A6 falling at 853,417 ps, b = SLICE_X32Y45.A6 next at 891,100): **no controlling chain from A reaches b**
(128 nodes bounded); walking back from b, its holds run through SLICE_X36Y47.A5 <- SLICE_X37Y48.C6 <- SLICE_X42Y97.B6 <-
... (the X42-43 Y87-97 logic), not to A. Either A is not b's cause in this run (C's trace A is from the untimed
machine), or the hold needs multi-pin control. Open.
Also: tools-B/target/simb.py's --datachange help said the default "handshake" mode is allowed by Spec.Env; it is NOT
(data move while the acks are still high; Env's broad rule forbids it; FOR-RESEARCH's early-release livelock).
Corrected the help text (default kept for old scripts). Today's 3-pair default-mode run gave [2, 6, 21] for
[(12,18), (1071,462), (6,4)]: that is the known early-release failure, outside Env; with --datachange broad: correct.

### progress 07:44 -- CtlChain extended: controlling SETS and multi-root hold certificates (check.sh OK); instance attempt negative
**Lean (standard axioms):** `CtlChain.hold_set` (a gate held by a controlling set of pins, each pin with its own
source window: an OR held low needs all its low inputs held) and `cert_holds` (a list of steps, each deriving one
node's hold window from roots or EARLIER steps, holds whenever the roots do). This is the sound form of C's TSE
"necessary predecessors" lower bound with several causes; roots are premises (order-level facts).
**Python (untrusted, negative):** tools-B/ps/ctlcert.py (controlling-set certificate on a simb dump; roots = the cause
plus every node static in [tau, b's change]). For umux16.uya's order on the 3-pair corner-0 run: b = SLICE_X32Y45.A6
is NOT certified from A = SLICE_X32Y28.A6 (853,417 ps): walking back, b's change at 891,100 comes through two long
AND/OR delay lines (X42-43 Y87-97, X36-37 Y87-98 enabled by SLICE_X35Y79.D6) whose head (SLICE_X36Y95.D6) was already
in flight before A changed; re-anchoring at SLICE_X36Y95.C6 (853,299) or SLICE_X35Y79.D6 (843,253) still certifies
only 16 / 750 nodes, not b: other concurrent activity is in flight at every candidate cause. **So in a timed run the
common cause of an order is not one event; a sound LO needs the order-level state (which nodes are in flight) from
C's abstract machine, which this tool cannot see.** Handed to C as the shape: roots = C's order-level holds,
steps = hold_set, cert_holds composes.

### progress 07:45 -- hold_mem (C-element hold, generic); the arbiter server path is not certifiable from q alone either (Python, negative)
`CtlChain.hold_mem` (standard axioms, check.sh OK): AckLow.ack_low generalised to any held value w and any
controlling set: once at w on its feedback window, a C-element stays w while the set's sources hold. With hold_set
and cert_holds this completes the hold toolkit (plain, set, memory, composition).
Python (ctlcert.py, memory holds on): ucontrol_merge10.uarb1, cause q = SLICE_X38Y51.B6 changing at 312,962 ps (3-pair
corner-0 run), targets its three moving state-LUT inputs (next changes ~47-49 ns later): none certified (18-71 nodes):
the loop body between the decision and the server's response has other activity in flight, as for the uya order.
So neither the RT orders nor the server-path obligation reduce to a single timed cause; the roots of a certificate
must come from the abstract machine's state (C).

### progress 07:48 -- CORRECTION: the "not certified" results of 07:4x were a tool bug; certificates work (Python, untrusted)
ctlcert.py processed nodes changing at the same ps (zero-delay hops) in a fixed 4-pass order, so long hop chains were
left uncertified. With a fixpoint loop (corner 0, κ = 0, 3-pair broad run; dmin sums, corner-independent lower ends):
| cause -> target | certified LO (ps) | actual (mid-window run) | premises besides the cause |
|---|---|---|---|
| b = SLICE_X32Y45.A6 rising (302,683) -> its ack source SLICE_X37Y43.B6 | 867 | 1,036 | 2 static |
| uya order: SLICE_X32Y28.A6 (853,417) -> SLICE_X32Y45.A6 | 4,633 | 37,683 | 3 static |
| merge10.uarb1 q (312,962) -> state input SLICE_X40Y49.A6 | 4,991 | 46,487 | 38 static |
The 07:30-07:44 statements "no chain reaches b", "B not certified", "server path not certifiable" are WITHDRAWN (tool
bug, not the circuit). The uya LO (4,633) is below C's unsound TSE figure (5,682).
**The binding race row, re-derived:** b's ack is read at b's pin 4 (pin chain FAST_MIN sum 206 ps), so after b rises the
ack cannot be read changed before 867 + 206 = 1,073 ps, against b's own feedback loop (7 arcs, FAST_MAX sum 441 ps):
κ* = (1073 - 441)/(1073 + 441) = **0.417** at the fast corner, which reproduces RaceTablePS's binding row (0.415, from
simulated ack paths) and sits below C's counterexample candidate (fails at 0.44, k48 adversary slows exactly this
loop). Certificate (LUT level): ack LUT SLICE_X37Y43.B (an OR, held low by pins 0 and 4) <- SLICE_X36Y45.A (C-element,
memory hold, pin 3) <- SLICE_X36Y46.D <- .C <- .B <- b; premises: b low until it rises, SLICE_X36Y45.A low on its
feedback window, SLICE_X37Y43.A6 low (static). Next: this certificate in Lean on THE target's own gates.

### progress 07:59 -- RaceCertPS CHECKED: the binding race's acknowledge cannot return early, every behaviour of THE circuit
`Formal/Cells/RaceCertPS.lean` (standard axioms, check.sh OK; rows GENERATED by tools-B/ps/gen_cert_ps.py from
ctlcert.py's tree, `rows_ok` by kernel decide: view chains, wiring, controlling-set INIT facts `kfact`, ties).
**Plainly:** `target_ack_holds`: in every behaviour of THE circuit (any g > 0, 0 ≤ κ ≤ 1), at its corner c: if
b = ulink_n_falseResult_85 stage 0 (SLICE_X32Y45.A6, node 120808) is low on [a, e], the reset is low from ar, the OR's
other input SLICE_X37Y43.A6 (node 140520) is low on [a, E], and the C-element SLICE_X36Y45.A6 is low on its feedback
window before the hold starts, then b's acknowledge source SLICE_X37Y43.B6 stays low up to
e + k1.lo 4 + k2.lo 4 + k3.lo 3 + k4.lo 3 + k5.lo 4 (five routed LUT steps' summed lower window ends; and up to
E + k5.lo 0). Generic pieces: `KRow`/`kfact`/`krowOK`/`krow_set`/`krow_mem` (any certificate row of THE target).
**What it buys:** the acknowledge delay of B's binding RaceTablePS row was a simulated path; it is now a lower bound in
every behaviour, under four local value premises. With b's pin-4 chain and its feedback loop (Python, the theorem's own
integer bounds lo = ⌈(1-κ)lerp(min)/g⌉, hi = ⌊(1+κ)lerp(max)·g⌋): the switch obligation (ack read unchanged for b's
loop upper delay) holds for κ ≤ 0.423 at c = 0, 0.433 / 0.439 / 0.442 / 0.445 at c = 0.25 / 0.5 / 0.75 / 1 (g = 1),
and for g < 1.58 at κ = 0. C's adversary (slow loop, all else fast) fails at κ = 0.44: the sufficient and the failing
sides are 0.017 apart on this node. **Not shown:** the four premises (order-level), that inequality in Lean (next),
the other 184 race rows.

### progress 08:02 -- race_margin CHECKED: the binding race row's margin is a theorem up to κ = 0.41 (g = 1), every corner
`RaceCertPS.race_margin` (standard axioms, check.sh OK): for g = 1, all κ ∈ [0, 41/100], all c ∈ [0, 1]:
b's feedback loop upper delay (kb.hi 0) ≤ k1.lo 4 + k2.lo 4 + k3.lo 3 + k4.lo 3 + k5.lo 4 + kb.lo 4, with the arcs
read from the netlist (`a1`..`ab0` by kernel decide; `kb_view` ties b's chains). Proof: ceil/floor bounds
(`sum_lo_ge`, `sum_hi_le`, `toNat_ge/le`) to the real inequality (1-κ)(1073 + 1725c) ≥ (1+κ)(441 + 641c).
**Plainly, with target_ack_holds:** in every behaviour of THE circuit with g = 1 and κ ≤ 0.41, once
ulink_n_falseResult_85 stage 0 rises (and the four local premises hold), its acknowledge is read unchanged for at
least the node's own feedback loop delay: B's binding race obligation (the row C's κ = 0.48 counterexample breaks)
is met. It is the first race row whose acknowledge delay is proved rather than simulated. Real-valued limit 0.417
(c = 0); C's adversary fails at 0.44. **Not shown:** the cfb_switch assembly (mechanical), the four premises, the
other 184 rows (ctlcert.py + gen_cert_ps.py produce rows for any node; the Lean pattern is generic).

### progress 08:06 -- target_b_switch(_041) CHECKED: the binding node rises cleanly in every behaviour for κ ≤ 0.41 (g = 1), given local premises
`RaceCertPS.target_b_switch` (standard axioms, check.sh OK): ack_holds_at (refactored to one corner) + b's force fact
(kbF: reset low, x high, ack low => 1 whatever the feedback) + confirm fact (kbC: reset low, x high, feedback high
=> 1 whatever the ack), both kernel-checked on b's INIT 0x2200332222003322, assembled with SpecFbChain.cfb_switch.
**Plainly:** in every behaviour of THE circuit, at its corner, if ulink_n_falseResult_85 stage 0 (SLICE_X32Y45.A6)
is low until s, its x input (node 136002) reads high from s until e', the reset is low, and the acknowledge
certificate's premises hold (SLICE_X37Y43.A6 low, SLICE_X36Y45.A6 low on its feedback window, the cause window long
enough before s), and the margin holds, then the node is HIGH on all of [s, e']: it rises and stays, no runt, no
fall-back. `target_b_switch_041`: at g = 1 and κ ≤ 0.41 the margin is `race_margin`, so only the local premises
remain. This is exactly the behaviour C's κ = 0.48 counterexample violates (b rises, the ack returns before b's
slowed loop, b falls and oscillates). **Not shown:** the local premises (order-level; for C's network argument), b's
fall direction, the other 184 race rows (same generator + Lean pattern).

### progress 08:09 -- CertPS: a generic hold-certificate checker on THE target (check.sh OK)
`Formal/Cells/CertPS.lean` (standard axioms): certificates = lists of `CRow` (a KRow plus, per controlling pin, a
label: the cause, static premise k, or an EARLIER row k); `win` computes each row's hold window from the premise
windows and the routed pin bands (start = max of source starts + hi, end = min of source ends + lo); `certOK`
(Boolean: krowOK per row + labels: source node and controlled value match, earlier-row indices); `cert_sound`:
in a behaviour at a corner, with the cause's value on [a, e], each static node's on [a, E k], and each memory row's
own value on its feedback window before its hold, every row's node holds its value on its window. Next: generate
certificates for the RaceTablePS rows (ctlcert.py -> gen) and check them with certOK by kernel decide.

### progress 08:13 -- certificates for 181 of the 185 RaceTablePS rows generated; kernel checks running
tools-B/ps/gen_certs_ps.py (untrusted generator): for each RaceTablePS row (out/target_ps_races.json), the episode
path's LUT steps become CRows (cause = the storage node's own flip; controlling set = path pin + fewest static
premises; memory only if needed), from simb dumps at corner 0 (3-pair broad run; then (2^30, 3·2^29), (7,3), (3,7)
for rows that do not flip there). 158 + 23 = 181 certificates; 4 rows have none from these dumps
(SLICE_X4Y54.A, X4Y51.A, X16Y25.B, X16Y18.D). Lean: Formal/Cells/CertRowsPS(2)/Bxx.lean, `certsNN_ok` by kernel
decide over `CertPS.certOK` (~6 GB, ~1 min per file); check.sh running (104 + 8 files). Not committed until it passes.

### progress 08:16 -- CertMarginPS: certificate window ends as path sums, and the margin from arc-sum facts (check.sh OK)
`Formal/Cells/CertMarginPS.lean` (standard axioms): `psum` (summed lower bands along a certificate's causal path),
`win_end_ge` (with one non-static pin per row (`singlePath`) and static premises lasting to e + PS, each row's
window ends no earlier than e + psum), `lo_sum_ge` / `hi_sum_le` (integer window ends vs the corner-linear real
sums, g = 1), `margin_of_sums` (283·ΣFAST_MAX(loop) ≤ 117·ΣFAST_MIN(path) and the SLOW analogue give
Σ hi(loop) ≤ Σ lo(path) for every κ ≤ 83/200 and every corner: RaceTablePS's facts, now for the integer bounds the
certificates use). Next: per row, tie psum + the node's ack-pin band to RaceTablePS's path, and the switch assembly.

### progress 08:33 -- CertRaceAll.race_holds CHECKED: a race obligation from any chain certificate, every behaviour
`Formal/Cells/CertRaceAll.lean` (standard axioms): `chainShape`, `psum_chain`, `pathArcs`, and `race_holds`:
for g = 1, κ ≤ 83/200, a certificate with certOK / singlePath / chainShape and the two RaceTablePS-style integer facts
(283·ΣFAST_MAX(node feedback pin) ≤ 117·ΣFAST_MIN(path pins ++ node ack pin), and SLOW), in a behaviour at a corner,
with the certificate's premises: the acknowledge source keeps its old value at every u from the last row's window
start with u + lo(ack pin) ≤ e + hi(feedback pin), i.e. every read of the node's acknowledge pin within its feedback
loop's upper delay after the flip sees the old value (the cfb_switch obligation). Next: the per-row instances
(node pins, ack/feedback pin indices, facts by kernel decide) for the 181 certificates.

### progress 08:46 -- CertSwitchAll: a checked race row makes its node switch cleanly (compiles; check.sh after the batch check)
`Formal/Cells/CertSwitchAll.lean` (compiles with -DautoImplicit=false, no sorry; check.sh run deferred: two OOM
kills today when a second Lean process ran beside the 6 GB certificate checks): `SwRow` (race row + the node's
force row F (old ack value among its controlling pins, feedback free) and confirm row C (feedback = new value, ack
free)), `swOK`, `switch_row` (cfb_switch + race_row: the node is at its new value on all of [sT, e'] given the
certificate premises, the other force/confirm pins' values over the reads, and the timing conditions), and
`target_switches_of` (all rows of a checked list, one corner, every behaviour, g = 1, κ ≤ 83/200). The generator now
emits F/C rows for all 181 certificates (found for every one at the flip) into RaceAllPS(2)/Bxx (`swNN_ok` by kernel
decide; `swNN_rr` rfl ties them to the race rows) and the batch theorems `target_races`, `target_switches`.
Kernel checks: CertRowsPS batch 1 at file 66/104 (5 OOM-killed files to rerun alone); batch 2 OK; RaceAll files next.

### progress 10:28 -- CHECKED: 158 of the 185 race rows are theorems about every behaviour of THE circuit (target_races, target_switches)
Lean (standard axioms; lake build per module + check.sh audit of the top modules, 3,284 declarations):
`Formal.Cells.RaceAllPS.target_races` / `target_switches` (135 rows) and `RaceAllPS2.target_races` /
`target_switches` (23 rows), instances of `CertRaceAll.target_races_of` / `CertSwitchAll.target_switches_of` over
generated, kernel-checked rows (`certsNN_ok`, `racesNN_ok`, `swNN_ok`).
**Plainly:** for every behaviour of THE circuit with g = 1 and κ ≤ 83/200 = 0.415 (one corner for all rows), for each
of 158 storage nodes (RaceTablePS rows): (races) once the node has flipped, every read of its acknowledge pin within
the node's feedback-loop upper delay sees the old acknowledge value; (switches) the node, once forced, reaches its new
value and keeps it on the whole window, with no runt. Each conditional on the row's local value premises (the node's
old value before the flip, 0-31 static side inputs held, memory rows' states, the force/confirm side inputs; listed
in out/target_ps_certs1/2.json), which are order-level facts for C's network argument. This replaces "the simulated
acknowledgement path" of RaceTablePS by a proof for 158 rows; it is the S3 race layer in every-behaviour form.
**Not covered:** 4 rows (power-up episodes, no post-reset certificate), 23 rows whose single certificate spans 19-40
netlist chunks (killed for memory in one kernel decide; all have κ thresholds ≥ 0.94, the table minimum is 0.415);
the premises themselves; non-vacuity (no Lean witness behaviour meeting all premises yet).

### progress 10:30 -- arbiter server path: hold certificates from the state's change to A0 (Python, untrusted)
ctlcert.py on the 3-pair corner-0 run, cause = the arbiter's state q changing, target = its A0 input (ArbViewPS role
a0), κ = 0, dmin sums (sound-shape lower bounds, given the listed premises): ucontrol_merge10.uarb1 (SLICE_X38Y51.B)
≥ 1,833 ps (7 LUT steps), SLICE_X14Y18.A ≥ 1,469 (5), SLICE_X14Y19.A ≥ 1,818 (7), SLICE_X18Y24.A ≥ 2,106-2,197 (7),
SLICE_X39Y21.C ≥ 1,530 (4); SLICE_X39Y24.A and SLICE_X16Y31.A: A0's next change is not certified from q (A0 there
moves for another reason in this run); SLICE_X16Y25.B, SLICE_X16Y18.D: q does not flip after reset in this run.
**Meaning for H_ARB(T):** ArbTSpec.spec_double_ack needs A0 to act while q is still unsettled; with these certificates
A0 cannot move before q's first change + ~1.47 ns (fast corner, κ = 0), so for T up to about that minus the read
windows the server-path obligation holds (given the premises), while the non-vacuity floor is the state LUT's own
upper delay (~664 ps slow). The Lean assembly (certificate + ArbOK + GrantExcl + AckLow) is the next step.

### progress 10:38 -- CHECKED: five arbiters settle before their server answers, under H_ARB(T), every behaviour (ArbServer, ArbServerPS)
**Problem, plainly:** ArbTSpec.spec_double_ack shows H_ARB(T) alone allows the server's A0 to act while the arbiter
state q is still moving (both clients acknowledged). The missing obligation: q has settled before A0 can change.
**Lean (standard axioms; lake build + check.sh audit):** `ArbServer.q_settles` (generic: a chain certificate from q
to the copy gate driving the state LUT's A0 pin node (`arbCertOK`) + ArbOK T: with q unchanged on [a, e], the
certificate premises, the other state inputs constant on [t1, t2], t2 ≤ e + psum: q constant on [t1 + T, t2]);
`target_arbs_settle_of` (list form, one corner); `ArbServerPS.target_arbs_settle` for ucontrol_merge10.uarb1
(SLICE_X38Y51.B, arbs[0]) and SLICE_X14Y18.A, X14Y19.A, X18Y24.A, X39Y21.C (arbs[5..8]); certificates `CertArbPS`
(5 certificates, 5-8 rows: q -> R0 (the state LUT's O5) -> ... -> A0 source -> A0 pin node; 2-5 static premises
each; out/target_ps_arbcerts.json). **Reading:** if q first moves at e + 1 ≥ t1, the A0 pin node cannot change
before e + psum (≥ ~1.47-2.2 ns at the fast corner, κ = 0, Python), so for T below that the state has settled before
the server's answer reaches it: the server-path obligation of the one-acknowledge argument, as a theorem modulo the
local premises. **Not shown:** the assembly with GrantExcl/AckLow into "one acknowledge per transaction"; the premises;
arbiters arbs[1..4] (no post-reset chain certificate in the runs used: A0 there changes for another reason, or q never
flips after reset).

### progress 10:49 -- reading A and C today: the frontier is now bracketed on both axes by B's sufficient rows
- A/C Lean-refuted THE statement at g = 1, κ = 11/25 = 0.44 (w = 0 and w = 20) and at g = 8/5, κ = 0. B's checked
  race certificates give the binding row's switch obligation for κ ≤ 0.41 (Lean, race_margin) / 0.417 (real-valued)
  and, at κ = 0, for g < 1.58 (Python): the sufficient side of B's cell layer sits 0.02-0.03 below the refutations on
  both axes. (Sufficient for the race rows only; the network premises are still open, so this is not a lower bound
  on THE theorem's frontier.)
- C's κ = 0.40 runt ring (w = 0) is at arbiter 0 with its A0 route (pin 3, from SLICE_X38Y53.B6) slowed and needs
  T ≥ 7.2 ns. ArbServerPS.target_arbs_settle covers arbiter 0 for T below its server-path sum (≈ 1.83 ns at κ = 0,
  ~1.1 ns at κ = 0.4, fast corner): there the state settles before A0 moves. So for the headline T the gap
  [server path, 7.2 ns) is where H_ARB(T) neither prevents nor admits that ring by B's argument; C's run shows it is
  admitted from 7.2 ns. The headline T should therefore stay below the server-path delay, which also keeps it above
  the state LUT's own delay (664 ps slow) only for κ small enough: (1-κ)·1469 (the shortest of the five server
  paths, fast corner) vs (1+κ)·664 -> κ ≤ ~0.38 for both conditions to hold with g = 1. Python estimate, not Lean.

### progress 12:21 -- the 23 large certificates, checked in pieces (BigCertPS; building)
`CertSplit` (Lean): `certOK_of_split` (certOK from krowOK by row ranges + labels), `raceOK_of_split` (raceOK from
its cheap parts + per-range path arc sums), `all_range'_append`, `sum_block`, `sFmin_pathArcs`.
tools-B/ps/gen_bigcerts_ps.py: per certificate a data file, row-range files (krowOK + the range's path FAST_MIN /
SLOW_MIN sums, each range ≤ MAXC netlist chunks) and a combining file (certOK, raceOK, swOK); BigCertPS.lean:
`target_switches` over all 23. First pass (MAXC = 12): 14 certificates complete; 9 had a range killed for memory
(three decides per file over 12 chunks) and are being rebuilt with MAXC = 5 (260 modules).

### progress 14:00 -- CHECKED: the 23 large certificates (BigCertPS.target_switches): 181 of 185 race rows now theorems
`Formal.Cells.BigCertPS.target_switches` (standard axioms; 391 modules built one at a time with lake, check.sh
audit 3,531 declarations): the 23 rows whose certificates span 19-40 netlist chunks, each checked in row ranges
(≤ 5 chunks, ≤ 20-30 rows per file; certOK_of_split / raceOK_of_split reassemble them). With RaceAllPS (135) and
RaceAllPS2 (23): **181 of the 185 RaceTablePS rows** are clean-switch theorems in every behaviour of THE circuit
(g = 1, κ ≤ 0.415, under each row's local premises). The 4 left are power-up episodes (reset high; κ 0.85-0.985).
Memory notes for full builds (shard A, check.sh --committed): every Cert/Race/BigCert module checks alone within
~6 GB; lake's parallel build will need check.sh's OOM retry (it rebuilds killed modules one at a time).

### progress 14:01 -- RaceAllTarget.target_switches_181: all 181 rows in one statement, one corner (check.sh OK)
`Formal.Cells.RaceAllTarget.target_switches_181` = target_switches_of over RaceAllPS.sws ++ RaceAllPS2.sws ++
BigCertPS.sws. This is the statement S4 can consume (notes/B-for-C-S4.md).

### progress 14:05 -- session summary (shard B, 2026-11-07)
**Lean, standard axioms, all pushed (check.sh audits OK):**
- H_PRIM / H_RUNT fidelity: `RuntForbid` (SpecRunt's H_RUNT(w) FORBIDS, not filters, a sub-w pulse wider than a LUT
  pin's window; toy where it forbids the environment's own step), `RuntFilter` (a filtering form, total, w = 0 =
  frozen). On THE target (simulation): the plain mid-window corner-0 runs have 5-12 such 13-14 ps pulses, so they are
  not BehavesRunt 20 behaviours at κ = 0 (notes/B-hrunt-forbid.md; for A, owner of SpecRunt).
- Hold certificates (sound "necessary predecessor" lower bounds in Spec semantics): `CtlChain`, `CertPS`,
  `CertMarginPS`, `CertRaceAll`, `CertSwitchAll`, `CertSplit`; generators gen_cert_ps / gen_certs_ps /
  gen_bigcerts_ps (untrusted; every row re-checked by kernel decide).
- `RaceCertPS.target_b_switch_041`: the binding race node switches cleanly for κ ≤ 0.41 (g = 1).
- `RaceAllTarget.target_switches_181`: 181 of the 185 RaceTablePS storage nodes switch cleanly in every behaviour of
  THE circuit (g = 1, κ ≤ 0.415, one corner), under local value premises (out/target_ps_certs1/2.json).
- `ArbServerPS.target_arbs_settle`: 5 of 9 arbiters' states settle (H_ARB(T)) before the server's answer reaches
  the state LUT, for T below the server path's summed lower bands.
**Simulation / untrusted:** certificate LO bounds (binding row κ* 0.417 real-valued, g < 1.58 at κ = 0); server path
≥ 1.47-2.2 ns (κ = 0, fast corner); simb's default data mode is outside Env (help text corrected).
**STATUS list:** no hypothesis of THE theorem is removed today (no n ≥ 1 theorem yet); what changed is that the
timing half of the storage nodes' environment premises (S3 races, 181 nodes) and the arbiters' server-path
obligation (5 of 9) are now theorems, leaving order-level VALUE premises for S4 (notes/B-for-C-S4.md).
**Open for B:** the 4 power-up race rows; the 4 other arbiters; the one-acknowledge assembly (needs a careful reading
of the state LUT's encoding: with A0 = 1 it outputs 1 whatever r1/r2/fb, so "A0 freezes q" is not the right shape);
latch hold windows by certificates (need full-width runs where the data bits move); non-vacuity witnesses.

### progress 14:06 -- correction: the state LUT DOES freeze q while A0 is high (decoded INIT)
The summary's "with A0 = 1 it outputs 1 whatever r1/r2/fb" used the RTL INIT 0xFFF0FFB2ACACACAC with the ROUTED pin
order; the decoded gate (SLICE_X38Y51.BLUT.O6, INIT 0xffffaab2e4e4e4e4, roles r1 = pin 2, r2 = 1, fb = 0, rst = 4,
A0 = 3, pin 5 tied 1) gives, with rst low: A0 = 0: q = C(r1, ~r2) (set on r1·~r2, reset on ~r1·r2); A0 = 1: q = fb
(frozen), as bd_arb.v says. So the one-acknowledge assembly has the expected shape: certificate (A0 cannot rise
before the server path) + ArbOK (q settles within T) + freeze (A0 high holds q) + GrantExcl + AckLow.

### progress 14:13 -- CHECKED: arbiter 0 does not acknowledge the losing client (ArbOneAckPS.target_arb0_one_ack)
**Problem, plainly:** ArbTSpec.spec_double_ack: H_ARB(T) alone lets both clients be acknowledged. For
ucontrol_merge10.uarb1 (arbs[0], the arbiter of C's κ = 0.40 ring) in the transaction where its state q falls (client
2 wins): is the losing side's acknowledge A1 (SLICE_X39Y51.D6 = C(g1, A0)) held low throughout, in every behaviour?
**Lean (standard axioms, check.sh OK):** `target_arb0_one_ack`: in every behaviour of THE circuit with H_ARB(T)
(`ArbOK T arbs x`, any sane p), at its corner: with the server-path certificate's premises (q high on [a, e]; its
static side inputs; memory rows), the state's other inputs constant on [t1, t2] (t2 ≤ e + psum), q low at t1 + T,
the reset low, A1 low on its feedback window before s0, and the overlap condition
t1 + T + hi(g1's q pin) + hi(A1's g1 pin) ≤ e + psum(A0 source) + lo(A1's A0 pin) + 1 (T small enough that the
grant settles before A0 can reach A1), A1 is LOW on all of [s0, t2 + lo + lo]. Assembly: certificate c000 (A0's
source held low) + kA1 (A1 held by A0 low, reset, feedback) + q_settles (q constant at the winner's value) + kGr1 (g1
held low by q) + kG1 (A1 held by g1 low). **Not shown:** the premises; the opposite transaction and the other 4
arbiters with certificates (same pattern, rows by generator); that A2 (the winner) completes (liveness).

### progress 14:19 -- CHECKED: one-acknowledge for 5 arbiters (ArbOneAck.one_ack(_of), ArbOneAckAllPS.target_one_ack)
`ArbOneAck.one_ack` (generic form of ArbOneAckPS: certificate + q_settles + the losing acknowledge's two holds +
the losing grant's hold; `oneAckOK` checks the wiring), `one_ack_of` (list form, one corner),
`ArbOneAckAllPS.target_one_ack` (rows GENERATED by tools-B/ps/gen_oneack_ps.py from ArbAckPS.arows and CertArbPS;
`rows_ok` by kernel decide) for arbs[0], arbs[5..8], each in its certificate's transaction direction: in every
behaviour of THE circuit with H_ARB(T), under the premises (as in 14:13's entry), the losing client's acknowledge
stays low through the transaction. Standard axioms, check.sh OK. **Not shown:** the opposite direction of each
(needs a certificate from a flip of the other polarity), arbs[1..4], the premises.

### progress 14:29 -- CHECKED: one-acknowledge in the other direction (4 arbiters); arbiters 1 and 3 settle + one-ack
**Problem, plainly:** `ArbOneAckAllPS` showed the losing client is not acknowledged for 5 arbiters, each in one
transaction direction only (q leaving one value). The other direction needs a certificate from a q flip of the other
polarity; arbs[1..4] had no server-path certificate at all.
**Lean (standard axioms; lake build + check.sh audit OK):**
- `CertArbPS2` (4 certificates, q flips of the opposite polarity in d3: arbs[0], [5], [7], [8]; cause values are the
  negations of `CertArbPS`'s) and `ArbOneAckAllPS2.target_one_ack` (4 rows). With `ArbOneAckAllPS`, arbs[0], [5], [7], [8]
  now have the one-acknowledge statement for both directions of q; arbs[6] for one (d3 has no flip of the other polarity).
- `CertArbPS3` (2 certificates), `ArbServerPS3.target_arbs_settle` (arbs[1] = SLICE_X39Y24.A, arbs[3] = SLICE_X16Y31.A
  settle before their server answers, the `ArbServerPS` statement) and `ArbOneAckAllPS3.target_one_ack` (both, one
  direction: q leaving true).
Same reading and premises as `ArbServerPS` / `ArbOneAckAllPS` (local value premises, one corner, H_ARB(T)).
**Why arbs[1], [3] were missing (generator bug, fixed):** simb.py dumps omit the nodes that are False for the whole
run; ctlcert.py read such a node as "unknown" and dropped every controlling set using it (here arbiter 2's R0, a pin of
arbiter 3's state LUT). Now read as False (gen_certs_ps.py already did). ctlcert bounds after the fix (fast corner,
κ = 0, Python): arbs[1] 1945 ps, arbs[3] 719 ps. Earlier ctlcert NEGATIVES (no certificate) may be affected by the same
bug and should be re-run; the positives are unaffected in soundness (every certificate is checked in Lean).
**Not shown:** arbs[2], arbs[4] (q never flips after reset in any of the 15 dumps here, so no transaction to certify
from); the other direction for arbs[1], [3], [6]; the premises. Also observed (Python, d3): arbiter 1's A0 change at
431.9 ns comes from arbiter 3's q flip through a ~7 ns chain, not from arbiter 1's own q.

**CORRECTION (to progress 10:30):** "SLICE_X16Y31.A: A0's next change is not certified from q (A0 there moves for
another reason)" was the ctlcert absent-node bug: in d3 arbiter 3's A0 change does come from its own q (Python trace),
and it is now certified. For SLICE_X39Y24.A the "another reason" reading stands (its A0 change follows arbiter 3's q),
but a hold certificate from its own q exists all the same (ArbServerPS3).

### progress 14:32 -- CHECKED: arbs[6] one-acknowledge in the other direction (ArbOneAckAllPS4)
`CertArbPS4` (1 certificate: arbs[6] = SLICE_X14Y19.A, q leaving true at 1,507,123 ps in the simb dump
dd_0x40000000_0x60000000; 7 LUT steps; ctlcert bound 1818 ps, fast corner, κ = 0, Python) and
`ArbOneAckAllPS4.target_one_ack`. lake build + check.sh OK (standard axioms). arbs[0], [5], [6], [7], [8] now have the
one-acknowledge statement for both directions of q; arbs[1], [3] for q leaving true only (every dump here flips them
once, true -> false); arbs[2], [4] none. Same premises/reading as ArbOneAckAllPS.

### progress 14:33 -- what the remaining uncovered rows are (Python, untrusted)
The 4 RaceTablePS rows without a certificate (SLICE_X4Y54.A, SLICE_X4Y51.A, SLICE_X16Y25.B, SLICE_X16Y18.D) are
exactly the storage nodes that never flip after reset (t > 400 ns) in any of the 15 simb.py dumps here (d0, d3, dp,
12 dd_* input pairs); the last two are the states q of arbs[2] and arbs[4], the two arbiters without a server-path
certificate. So every storage node and arbiter that moves after reset in these runs now has its checked certificate;
what is left is nodes these workloads never move. A certificate for them needs a flip to take premise values from
(or a search for sensitizing values, which gives premises nobody has seen hold), or a network-level argument (C) that
they do not move after reset, which would make their race obligations vacuous. Not attempted here.

### progress 14:46 -- CHECKED: latch hold windows from certificates (LatchHoldCert; first 8 latches, LatchHoldPS)
**Problem, plainly:** `LatchViewPS.target_ps_latch_close` (4,185 latches) assumes each latch's data source keeps the
captured value until `τ + hi e` (the HOLD half of its data window) and that the enable was open before τ. In a
bundled-data pipeline the next data is released only in response to the close itself, so the hold is a race between
the close and the controller/acknowledge path back to the data: the same shape as B's storage-node race rows.
**Lean (standard axioms; lake build + check.sh OK):** `LatchHoldCert`:
- `margin_succ`: per-row integer facts `kA·(ΣFAST_MAX(enable arcs) + 1) ≤ kB·ΣFAST_MIN(path arcs)` (and SLOW) give
  `hi e + 1 ≤ Σ lo(path)` at every corner, for every κ ≥ 0 with `(1+κ)·kB ≤ kA·(1-κ)` (each row its own κ range).
- `latch_hold` / `latch_hold_row`: a chain certificate whose cause is the latch's enable source (old value = "open")
  and whose last row is its data source gives the data value on `[window start, τ + hi e]`, τ = e + 1.
- `latch_row` (`target_latch_close` per row at a fixed collapsed relation) and `target_latch_holds_of`: for a checked
  list, ONE corner for certificates and latches together (one `view_collapse`), each latch holds `v` on `[A, E' + lo e]`
  with the hold half and the open window discharged; left: the certificate's local premises, the enable closed on
  `[τ, E']`, the setup half (data before the certificate's window start), the latch's own inequalities.
- Instance `LatchHoldPS.target_latch_holds` (certificates `CertLatchPS`): 8 latches so far, from closes in d3
  (κ ranges 0.346-0.68, median 0.584; the 8 use 0-2 static premises, ctlcert count). Generator tools-B/ps/gen_latchhold_ps.py (two
  passes: the arc sums are evaluated in Lean by `#eval`, then each row's kA/kB is the smaller of the two ratios).
**Python (untrusted):** ctlcert over the 396 latch closes in d3 followed by a data change: running (3 workers); of the
first 93, the chain-shaped ones certify; the non-certified ones are latches whose next data change is not caused by
their close in that run (premise-free reading: an independent cause).
**Not shown:** latches whose data never moves in d3 (3,360 of 4,185 do not move: narrow data in that run); the
premises; whether the minimum κ range (0.346 so far) is a real limit or a short path in this one run.

### progress 16:15 -- CHECKED: latch hold windows for 112 latches (LatchHoldPS, CertLatchPS)
`LatchHoldPS.target_latch_holds` now covers 112 latches (the chain-certified closes among the first ~200 of the
396 d3 latch closes with a later data change); certificates `CertLatchPS` (42 files), rows split by certificate
file (`LatchHoldPS/Bxx`: one kernel check per block; all 112 in one check was killed for memory). lake build +
check.sh OK (standard axioms, 2636 declarations). Row κ ranges ((1+κ)·kB ≤ kA·(1-κ)): min 0.346
(SLICE_X32Y92.A O5), median 0.666. Premises per row: out/target_ps_latchholds1.json. Same reading as 14:46: hold
and open windows discharged, the certificate's local premises and the setup half remain.
**Running (Python):** the rest of the d3 scan; a full-width run (pair 0x49e9c618,0x35bf992e, corner 0, mid-window,
broad data rule, result 2 correct) moves the data of 1,639 latches (d3: 825), incl. the binding hold latch
SLICE_X32Y90.C6 (6 data flips); its 361 new latch closes are being scanned.

### progress 20:03 -- CHECKED: latch hold windows for 214 more latches (LatchHoldPS2; 326 in all)
The d3 scan finished: of the 396 latch closes followed by a data change, 326 have a chain-shaped certificate, 43 a
certificate that is not a single chain (not used by LatchHoldCert), 27 none (the next data change has another cause
in that run). `LatchHoldPS2.target_latch_holds` (certificates `CertLatchPS2`, 61 files; rows split per file) covers
the 214 not in LatchHoldPS. lake build + check.sh OK (standard axioms, 2852 declarations). Row κ ranges: min 0.199
(SLICE_X20Y96.D O5), median 0.617. Together, LatchHoldPS + LatchHoldPS2 give the hold and open windows of 326 of the
4,185 latches as theorems (each in its own κ range, local premises and the setup half remaining). Premises:
out/target_ps_latchholds2.json. Python, untrusted: which certificate path makes 0.199 binding is not yet examined
(a short controller path to that latch's data, or a slow enable pin arc).

### progress 22:27 -- CHECKED: latch hold windows for 344 more latches from a full-width run (670 in all)
**Run (simulation, untrusted):** simb.py, pair 0x49e9c618,0x35bf992e (row 14 of gcd_ps_vec1000.hex), corner 0,
mid-window, broad data rule, result 2 (correct); dump dfw.json. It moves the data of 1,639 latches (d3: 825); 361
latch closes followed by a data change are on latches not in the d3 scan; ctlcert (κ = 0, fast corner) gives a
chain certificate for 344 of them, none uncertified.
**Lean (standard axioms; lake build + check.sh OK, 3192 declarations):** `LatchHoldPS3.target_latch_holds`
(certificates `CertLatchPS3`, 96 files), same statement as LatchHoldPS. Row κ ranges: min **0.291 at SLICE_X32Y90.C
O6**, the latch with the smallest simulated hold slack (1.28 ns, 11:54 entry); median 0.654. With LatchHoldPS (112)
and LatchHoldPS2 (214): **670 of the 4,185 latches** have their hold and open windows as theorems (each in its own κ
range; local premises and the setup half remain). Premises: out/target_ps_latchholds{1,2,3}.json.
**Build note:** two 15-18-chunk certificate files with 24-31 certificates were OOM-killed (after a container
restart); gen_certs_ps.py MAXC2=K:N:P caps chunks and certificates per file from file K on.
**Reading:** for g = 1 the binding latch's hold obligation is now proved for κ ≤ 0.291 (from this certificate; the
sums use the fast/slow MIN of the path and MAX of the enable pin). That sits below the race rows' 0.415 and A/C's
0.44 refutation: if 0.291 is tight it, not the races, would bound the headline κ for latches whose data moves like
this. Not examined yet: whether a longer certificate (a different path through the controller) raises it.

### progress 00:12 -- CHECKED: latch hold at the data PIN -- binding latch now κ ≤ 0.440; all 670 ≥ 0.376
**Problem, plainly:** the 0.291 for SLICE_X32Y90.C O6 came from `SpecLatch.latch_close`'s data premise: it asks the
data SOURCE to hold until `τ + hi e`, ignoring that the latch only uses a data read while its enable read still
sees "open" (output times `s < τ + hi e`) and that such a read looks at the source at `s - (read delay) ≤ s - lo d`.
**Lean (standard axioms; lake build + check.sh OK, 4148 declarations):** `LatchHoldPin`: `latch_close_pin`
(`latch_close` with the data premise `t + lo d < τ + hi e`; same proof, which only ever uses that), `margin_le`,
`latch_hold_pin`, `latchHoldPinOK` (facts on path arcs ++ data-pin arcs vs enable-pin arcs, no +1),
`target_latch_holds_pin_of`; instances `LatchHoldPinPS`, `LatchHoldPinPS2`, `LatchHoldPinPS3` (same 670 certificates,
CertLatchPS/2/3, unchanged). Per-row κ ranges: min 0.474 / 0.376 / 0.407, medians 0.726 / 0.673 / 0.711.
**Binding latch:** SLICE_X32Y90.C O6 κ ≤ 0.440 (was 0.291), O5 ≤ 0.421 (was ~0.3). The lowest of the 670 is now
SLICE_X20Y96.D O5, 0.376. So the 14:5x reading ("latch hold might cap the headline κ at 0.29") is WITHDRAWN: it was an
artefact of the latch theorem's data premise. The latch hold rows now sit at or above the race rows' 0.415 except
for a few latches between 0.376 and 0.415 (not yet examined; same caveat: a different certificate path may raise them).

## Session Sun Nov  8 07:10:47 UTC 2026 (shard B; session_01HC49FvLPHt8jW9mMxvCTG5)
Start: lock taken 07:11 (previous B lock 00:12, other session, > 90 min). Audit read (audit head bb78f0a8): every row
on B's files is CONFIRMED (T27 S3 cell layer; T36 race_margin; T38 race rows 158/181, one-ack, latch holds 670 at the
data pin, κ figures recomputed by the auditor). No open REFUTED/OVERSTATED row on B's files. setup.sh: Mathlib cache
unreachable, building the imported part from source (running).

### progress 07:15 -- plan: the latch-hold race has never been attacked by an adversary
A's and C's single-pin adversary sweeps (hazsweep.py --control; 412 control storage nodes, κ = 0.40 / 0.48) skip all
4,185 latch-like storage LUTs. B's latch-hold certificates (670 latches, LatchHoldPinPS*) give sufficient bounds as
low as κ ≤ 0.376, below the refuted 0.44. So a latch whose hold breaks between 0.376 and 0.44 would lower THE
statement's refutation frontier. New tool `tools-B/ps/latchsweep.py` (untrusted): per latch, its enable-pin arc and
the copy-chain hops into it at the top of the window, every other arc at the bottom (corner 0, κ = P/100 exact,
H_RUNT(20) on LUT pins, C's simadv.py). Sanity: at κ = 0.80 the enable adversary on SLICE_X32Y90.C5 gives a quiet
deadlock (no out0; 567 ns), so the adversary does bite at large κ; at 0.43 the three lowest-bound latches tried
(SLICE_X32Y90.C5/C6, SLICE_X20Y96.D5) are correct. Running: all 4,185 latches at κ = 0.43 on the full-width pair
(0x49e9c618, 0x35bf992e), the 670 certified first (~8 runs/min, so the full list takes ~9 h).

### progress 08:21 -- latch-hold adversary at κ = 0.43: the 670 certified latches all correct (simulation, untrusted)
`latchsweep.py`, κ = 43/100, w = 20, full-width pair (0x49e9c618, 0x35bf992e): the first 675 runs (the 670 latches
with hold certificates, then 5 more) all return gcd = 2. The 15 latches whose certified bound is below 0.445
(`tools-B/ps/out/latchhold_kappa_670.txt`, recomputed from the Lean rows' kA/kB: (kA-kB)/(kA+kB); lowest
SLICE_X20Y96.D5 0.376) were also run on the 3-pair broad run (12,18), (1071,462), (6,4) whose closes they were
certified from: 15/15 correct (`tools-B/ps/out/latchsweep_k43_d3_low15.txt`). **Reading:** no single enable-pin
adversary breaks a latch hold below the 0.44 refutation on these pairs; the 0.376-0.44 certified bounds look like
certificate slack (the certified path sum is not tight against a real data change that alters the latched value), not
a race. Not shown: multi-pin adversaries, other pairs, other corners. The other 3,510 latches: running.

### progress 08:22 -- why the low certified latch bounds are slack, not races (simulation, untrusted)
- Bisection, binding latch SLICE_X32Y90.C5 (certified κ ≤ 0.421), enable-pin adversary, full-width pair: correct at
  κ = 0.43, 0.50, 0.60; quiet deadlock (no out0) at 0.70 (and 0.80). So this latch's own failure point under its
  adversary is in (0.60, 0.70], far above the 0.44 refutation.
- Lowest certificate, SLICE_X20Y96.D5 (O5 = d·e | fb·~e, data pin 0 from SLICE_X18Y95.C5, enable pin 1 from
  SLICE_X20Y96.A6; certified κ ≤ 0.376): on the 3-pair run at κ = 0.43 with its enable slow, the enable opens for
  ~11 ns per pair (1016.6-1027.6 ns), the data source moves at 1016.4 ns (before the open) and next at 1245.7 ns,
  218 ns after the close. The certificate (cause = enable source closing, 3 LUT steps to the data source, a
  C-element, plus one static premise SLICE_X14Y88.C6 = false) only bounds how early the data source COULD move
  after the close; in the runs its other input keeps it for ~200 ns. So the 0.376 is the certificate's slack: a
  longer controlling path (through the static premise's own cause) would raise it, at the cost of a premise
  further away. Not attempted: regenerating certificates with longer chains for the 15 rows below 0.445.

### progress 09:35 -- latch-hold adversary at κ = 0.43: every latch whose data moves is correct (simulation, untrusted)
Full-width pair (0x49e9c618, 0x35bf992e), κ = 43/100, w = 20, corner 0: a baseline run (all arcs fast, correct)
was dumped and the latches whose enable AND data sources both move after reset were selected (a latch whose data
never moves cannot lose a hold race in that run). With the 670 certified latches run first, 1,441 latches in all
were run with their enable-pin adversary: **1,441 / 1,441 correct** (`tools-B/ps/out/latchsweep_k43_fw.txt`).
**Reading:** on this pair no single latch's hold race breaks below the 0.44 control race; with C's bundling
adversary (setup side, first wrong value in (0.68, 0.8]) neither half of the latch window is the binding failure.
So the refutation frontier at g = 1 stays at the control race (0.44), and B's 0.376-0.44 certified latch bounds are
certificate slack (independent causes keep the data, 08:22 entry). Not shown: other pairs (running next: the
3-pair run's moving latches not covered here), multi-pin adversaries, the slow corner.

### progress 09:42 -- 3-pair run: the 103 further latches whose data moves are correct too
Baseline dump of the 3-pair broad run ((12,18), (1071,462), (6,4); κ = 0.43, all fast, correct): 103 latches move
both enable and data there and were not in the full-width sweep; enable-pin adversary at κ = 0.43, w = 20: 103/103
correct (`tools-B/ps/out/latchsweep_k43_d3.txt`). So 1,544 latches (every latch moving on either workload) have been
attacked at 0.43 without a failure. Running: the same 1,441 at the slow corner (c = 1; latchsweep.py --corner 1).

### progress 12:52 -- slow corner too: 1,441 / 1,441 latches correct at κ = 0.43 (simulation, untrusted)
Same 1,441 latches and adversary as 09:35, at the slow corner (c = 1: enable-pin arcs at (1+κ)·SLOW_MAX, all else
(1-κ)·SLOW_MIN; latchsweep.py --corner 1 --tmax 9 µs; a first attempt with the 3 µs cap reported spurious "no out0":
the slow-corner run needs ~4.8 µs). All correct (`tools-B/ps/out/latchsweep_k43_fw_c1.txt`).
**Summary of today's latch-hold attack:** 1,544 latches (every latch whose enable and data both move on the full-width
pair or the 3-pair run), single enable-pin adversary at κ = 0.43, H_RUNT(20): no failure at either corner. The
binding latch fails only in (0.60, 0.70]. So, on these workloads and this adversary class, latch holds do not move
the g = 1 refutation frontier below the control race at 0.44; the certified latch bounds below 0.415 (4 latches,
0.376-0.414) are certificate slack. What is NOT shown: a latch-hold failure is impossible below 0.44 (no theorem;
multi-pin adversaries, other pairs untested). The STATUS list is unchanged by this (no hypothesis discharged): the
day's result is negative evidence for research and for the frontier, not a shrink.

### progress 14:40 -- w = 0 (no runt filter): 1,441 / 1,441 latches correct at κ = 0.43, fast corner (simulation)
Same sweep as 09:35 without H_RUNT (plain transport reads, the pessimistic w = 0 statement): all correct
(`tools-B/ps/out/latchsweep_k43_fw_w0.txt`). So the latch-hold adversary finds no failure at κ = 0.43 under w = 0
or w = 20, at either corner. (The first w = 0 launch died with its parent shell after 458 runs; it resumed from
the result file, so no run was repeated or skipped.)

### progress 14:4x -- combined adversaries do not lower the binding race's threshold (simulation, untrusted)
Pair (1071, 462), w = 20, corner 0, every listed arc at the top of its window and all else at the bottom:
A = SLICE_X32Y45.A6's 7-arc feedback route (the Lean-refuted race); B = ucontrol_merge10.uarb1.ua2's 5-arc pin-0
route (A's second race, 0.46); L = the binding hold latch SLICE_X32Y90.C5's 6-arc enable route. A, A+B, A+L, A+B+L:
all correct at κ = 0.42 and 0.43; A and A+B+L both deadlock at 0.44. So these races do not interact: each fails at its
own threshold. Running: A's adversary at κ = 0.43 on the first 60 vectors of gcd_ps_vec1000.hex (is the 0.44 threshold
pair-dependent?).

### progress 14:5x -- binding race's adversary at κ = 0.43 on 60 more pairs: all correct (simulation)
A's adversary (SLICE_X32Y45.A6 feedback route slow, all else fast, w = 20, corner 0) on the first 60 vectors of
target/gcd_ps_vec1000.hex (incl. (2^31-1, 2^31-2), (2^31-1, 2^31-1), powers of two): 60/60 correct
(`tools-B/ps/out/race_A_k43_vec60.txt`). No pair found that moves this race's threshold below 0.44.

### progress 15:2x -- CANDIDATE COUNTEREXAMPLE at κ = 0.40 (w = 20), BELOW the Lean-refuted 0.44 (simulation, two independent checkers)
Control sweep (`tools-B/ps/ctlsweep.py`: C's hazsweep with κ = P/100) at κ = 0.43, w = 20, corner 0, on the
FULL-WIDTH pair (0x49e9c618, 0x35bf992e) instead of (1071, 462): node **SLICE_X16Y21.A6** (6-input C-element
LUT, INIT 0x00fa00a000fa00a0, pin 3 = reset SLICE_X2Y29.DQ, pin 4 = its own feedback) with its pin-0 route (6 arcs, from
SLICE_X17Y23.B6) at the top of the window and everything else at the bottom: **quiet deadlock, no out0**.
Bracket on this pair: correct at κ = 0.30, 0.35; deadlock at 0.40, 0.42, 0.43 (0.10 ran out of simulated time, not a
verdict). On (1071, 462) the same adversary is correct at 0.43, which is why A's and C's sweeps (that pair only)
did not see it: **the failure is pair-dependent**.
Exact run at κ = 10/25 (simadv.py --classes, KDEN 25; dump `tools-B/target/out/k40w20_x16y21_dump.json.xz`, classes
`k40w20_x16y21_classes.json`):
- A's `gatecheck_runt.py` (exact mode, w = 20): 186,871 gates, 258,156 checks, **0 mismatches, 0 arcs outside Adm,
  0 lag violations** (a GateOKRunt 20 behaviour at g = 1, κ = 0.40, corner 0);
- C's `envcheck.py` (R 400 ns, su 1000, Δo 3 ns): **Env + SeqEnv OK; ArbOK for every T ≥ 131 ps; out0 0 of 1;
  quiescent from 484,403 ps**.
So, if the simulator and both checkers are right, NetCorrectSeqRunt 20 (and hence the plain statement) is FALSE at
g = 1, κ = 0.40, for T ≥ 131: the g = 1 margin is below 0.40, not 0.44. NOT yet: a Lean witness (C's/A's generators
CexR44 / gen_runt_c.py should apply with this classes file and pair), the exact threshold in (0.35, 0.40], the
mechanism (the deadlock is ~84 ns after reset release), other pairs.

### progress 15:4x -- κ = 0.40 candidate: bracket, mechanism class, Lean witness building (Formal/Cells/CexX16)
- Bracket on the full-width pair (same adversary): correct at 0.30, 0.35; **no out0 by 4 µs at 0.36, 0.37, 0.38,
  0.39** (14-17 M events: a livelock, not a quiet end; at 0.36 the run to 1.2 µs is a GateOKRunt 20 prefix (3
  mismatches, all at the cut time; 0 arcs outside Adm), Env + SeqEnv OK, ArbOK T ≥ 139, with 6-20 ps pulses
  circulating around SLICE_X8-9Y14 and SLICE_X16Y21.A6 itself oscillating from 487.7 ns); quiet deadlock at 0.40-0.43.
  So the finite (Lean-able) witness is at 0.40; below it, down to 0.36, the run never answers but never goes quiet
  either (a Lean refutation there would need C's eventually-periodic route, and the run is not obviously periodic).
- Lean: `Formal/Cells/CexX16/` = C's CexR44 witness files (KBase, RBase, Wit, Refute: A's gateWR check as copied by
  C) with κ 11/25 -> 10/25 (35·FAST_MAX, 15·FAST_MIN), this run's boundary codes (req [401000, 460480), acks
  [422393, 469241), [422665, 469428), start ack [460479, 483896), pend ack [404000, 463480); same shapes as C's run),
  the full-width pair and T ≥ 131; data generated by gen_runt_c.py from the κ = 10/25 dump. KBase and RBase build;
  the 75 gate-check chunks are building one or two at a time (the setup's whole-project build was stopped to free
  memory; it only rebuilds B's big certificate modules, not needed today). Not committed until Refute checks.

### progress 16:30 -- control sweep at κ = 0.43 on the full-width pair done: 2 of 1,316 fail (simulation)
`tools-B/ps/out/ctlsweep_k43_fw.txt` (412 control storage nodes x live pins, single-pin adversary, w = 20, corner 0):
1. SLICE_X16Y21.A6 pin 0: the quiet deadlock of 15:2x (κ = 0.40 candidate; Lean witness building);
2. SLICE_X38Y51.B6 pin 3 (arbiter 0's state LUT): no out0 by 3 µs, not quiet: the livelock A saw at κ = 0.48 on
   (1071, 462), where the state toggles with its inputs fixed, which H_ARB(T) excludes (not a behaviour; not checked
   again here).
The known 0.44 race (SLICE_X32Y45.A6) does not fail at 0.43, as expected. So the new race is the only single-pin
failure below 0.44 on this pair.

### progress 16:38 -- the κ = 0.40 race fails on 16 of 60 vector pairs (simulation)
SLICE_X16Y21.A6 pin-0 adversary on the first 60 vectors of target/gcd_ps_vec1000.hex, w = 20, corner 0:
**κ = 0.35: 60/60 correct; κ = 0.40: 16/60 no out0** (incl. (0x40000000, 0x60000000), (2^31-128, 2^29-64), (19767456,
2016807462), several gcd = 1 pairs); (1071, 462) and the other small pairs pass. So the race is not a quirk of one
pair: it needs some property of wide operands (to be characterised), which is why the sweeps on (1071, 462) missed it.
Files: `tools-B/ps/out/race_x16_k{35,40}_vec60.txt`.

### progress 16:5x -- PROVED IN LEAN: THE headline statement is false at g = 1, κ = 10/25 = 0.40 (Formal/Cells/CexX16; check.sh OK)
`Formal.Cells.CexX16.not_netCorrectSeqRunt20 : ∀ T su Δo, 132 ≤ T → Δo ≤ 3000 → ¬ NetCorrectSeqRunt 20
DecodedPS.net DecodedPS.boundary DecodedPS.arbs ⟨1, 10/25⟩ T 400000 su Δo` (axioms propext, Classical.choice,
Quot.sound; `./check.sh Formal/Cells/CexX16/{Refute,Wit,RBase,KBase}.lean`: 1,266 declarations, [check] OK; no
sorry / native_decide; the 75 gate chunks built one or two at a time).
**Plainly:** with no guard, within-die scatter 0.40 at the fast corner, any arbiter bound T ≥ 132 ps, reset 400 ns,
any setup margin and out0/end-ack delay ≤ 3 ns, and LUT pins filtering every pulse narrower than 20 ps, there is an
admissible behaviour of THE target that accepts (0x49e9c618, 0x35bf992e) and never answers. The witness: the
C-element SLICE_X16Y21.A6's pin-0 route from SLICE_X17Y23.B6 (6 arcs) at ⌊35·FAST_MAX/25⌋, every other arc at
⌈15·FAST_MIN/25⌉ (LUT pins ≥ 20 ps); quiet from 484 ns. By A's `SpecMono.seq_anti_p` this should carry to every
g ≥ 1, κ ≥ 0.40 (not restated here), and C's `Net/Stretch` route should give every reset ≥ 400 ns (not done: the
Lean here is for R = 400 ns only). The plain statement (w = 0) follows via `SpecRunt.seqRunt_of_seq` (as in C's AllR;
not restated here).
**Frontier now (g = 1, fast corner):** refuted at κ ≥ 0.40 (this file), previously 0.44 (CexR44). Simulation: the same
adversary is correct at 0.35 on all 60 test pairs and livelocks (no quiet end, no out0) at 0.36-0.39 on the full-width
pair. B's sufficient race bounds (0.415 for RaceTablePS's rows) did NOT cover this node's race on this workload: the
race rows come from simulated runs of narrower pairs. So the g = 1 margin of THE statement is below 0.40, and the
lower end is not known (no positive theorem). **For research:** a race at SLICE_X16Y21.A6 (C-element with reset,
INIT 0x00fa00a000fa00a0) that only full-width operands exercise; its feedback-vs-pin-0 margin is ~0.35-0.40.

### progress 17:0x -- κ = 0.40 refutation extended: every g ≥ 1, κ ≥ 0.40, w ≤ 20, and the plain statement (CexX16.Frontier; check.sh OK)
`Formal/Cells/CexX16/Frontier.lean` (standard axioms, check.sh OK, 1,296 declarations): `not_seqRunt20_above40`,
`not_seqRunt_le20_above40` (every runt width w ≤ 20), `not_seq_above40` (the plain NetCorrectSeq, via
`seqRunt_of_seq`): for every g ≥ 1, κ ≥ 10/25, T ≥ 132, Δo ≤ 3 ns, any su, reset 400 ns, THE statement is false.
A's monotonicity lemmas are copied verbatim from Target/FrontierRunt (importing it would rebuild its two 75-chunk
witnesses; that OOM-killed a first attempt). **Not shown:** resets other than 400 ns (C's Stretch route), κ < 0.40.
**STATUS (for A, who owns STATUS.md):** the g = 1 refutation point moves from 11/25 to 10/25 (B's
CexX16.Frontier); the binding race is now SLICE_X16Y21.A6 pin 0 on full-width pairs, not SLICE_X32Y45.A6.

### progress 17:1x -- κ = 0.40 refutation for every reset length R ≥ 400 ns (CexX16.AllR; check.sh OK)
`Formal/Cells/CexX16/AllR.lean` (shard C's CexR44/AllR with this run's codes; standard axioms; check.sh OK, 1,487
declarations): `not_netCorrectSeqRunt20_R : ∀ D T su Δo, 132 ≤ T → Δo ≤ 3000 → ¬ NetCorrectSeqRunt 20 net boundary
arbs ⟨1, 10/25⟩ T (400000 + D) su Δo` and `not_netCorrectSeq_R` (plain). So the board's long reset is covered too.
Frontier.lean now also has `not_seqRunt_le20_above40_R` and `not_seq_above40_R`: every g ≥ 1, κ ≥ 10/25, w ≤ 20 (or plain),
every reset 400 ns + D, T ≥ 132, Δo ≤ 3 ns (check.sh OK, 1,497 declarations).

### progress 17:2x -- below 0.40: an exactly periodic livelock at κ = 0.36 (simulation; a liveness counterexample candidate)
- The 16 pairs that fail at 0.40 also fail at 0.38 (same 16 of 60) and, at 0.36, all 16 run to the 3 µs cap with
  9-12 M events and no out0 (livelock, no quiet end). At 0.35 all 60 pairs are correct.
- Full-width pair, κ = 9/25 = 0.36 exactly, w = 20, same 6-arc adversary, dump to 1.2 µs
  (`tools-B/target/out/k36w20_x16y21_dump_1200ns.json.xz`): **from 491 ns every node's flips are exactly periodic with
  period 79 ps** (140 nodes active, around SLICE_X8-9Y14 and SLICE_X16Y21.A6; checked to 1.19 µs; Python). Checks on
  the prefix: A's gatecheck_runt (exact, w = 20): 0 arcs outside Adm, 0 lag violations, 3 mismatches all at the cut
  time (expected for a non-quiescent cut); C's envcheck: Env + SeqEnv OK, ArbOK T ≥ 139, out0 never rises.
- **Reading:** if the periodic tail extends for ever (it is a deterministic transport run, so a repeating state does
  repeat), THE statement is also false at κ = 0.36 (liveness: the pair is never answered). A Lean proof needs C's
  `Net/Periodic` (`eq_of_periodic`, with a period multiple ≥ the largest arc delay, e.g. 13·79 = 1027 ps) combined
  with the H_RUNT(20) read maps (A's gateWR) on the periodic code: not written. Simulation, untrusted: the g = 1 margin
  of THE statement on this race is in (0.35, 0.36].

### progress 17:3x -- the κ = 0.40 race is merge4's arbiter acknowledge C-element; FOR-RESEARCH B1
SLICE_X16Y21.A6 = `ucontrol_merge4.uarb1.ua2`, reading the fork `ucontrol_merge4_f` (SLICE_X17Y23.B6) on pin 0
(routed JSON, NEXTPNR_BEL): the same "ua2 reads the fork" pattern as A's 0.46 race at merge10. Written up as
FOR-RESEARCH B1 (Lean result, pair dependence, the periodic livelock below 0.40, the suggested fix).

### progress 18:24 -- control sweep at κ = 0.37 (full-width pair): only the merge4 ua2 race fails (livelock)
`tools-B/ps/out/ctlsweep_k37_fw.txt`: 1,315 / 1,316 single-pin runs correct; the one failure is SLICE_X16Y21.A6 pin 0
(no out0 by 3 µs, 10.9 M events: the periodic livelock of 17:2x). The arbiter-0 state livelock (0.43) is gone at 0.37.
So on this pair, below 0.40, the merge4 ua2 race is the only single-pin failure and it gives no quiet (finite) end:
a Lean refutation below 0.40 needs the periodic route.

### progress 18:3x -- what a Lean refutation below 0.40 needs (handoff note for C / A)
- w = 20, κ = 9/25, full-width pair: exactly periodic from 491 ns, period 79 ps, 140 active nodes (17:2x). A Lean
  witness needs (i) codes as C's `sigQ` (prefix + one period), (ii) a GateOKRunt check over a finite window that
  extends to all t: C's `eq_of_periodic` does this for transport gate equations, but under H_RUNT the LUT-pin read
  map `jr` skips pulses < 20 ps, and in the periodic tail the narrow-pulse chains are infinite, so A's `gateWR`
  (finite chain lists) has to be redone for periodic chains (a chain list that is itself `sigQ`-periodic), (iii)
  Env / SeqEnv / ArbOK (no boundary or arbiter-state node is in the periodic set? not yet checked) and out0 never rising.
- w = 0, κ = 9/25: NOT periodic by 1.19 µs (445 active nodes, 66 M events: unfiltered runts keep spreading), so the
  plain statement's κ = 0.36 refutation does not have the simple periodic witness; but the w = 20 one refutes the plain
  statement too (seqRunt_of_seq), so (ii) is the only route needed.
Not attempted here today.

### progress 19:12 -- control sweep at κ = 0.38 on (0x40000000, 0x60000000): again only the merge4 ua2 race (livelock)
`tools-B/ps/out/ctlsweep_k38_p40000000.txt`: 1,315 / 1,316 correct; SLICE_X16Y21.A6 pin 0 runs to 3 µs without out0
(8 M events). No other single-pin race fails at 0.38 on this second wide pair, and none ends quietly below 0.40.

### progress 19:2x -- notes/B-arb-up.md: the Lean facts an arbiter-aware Up rule (C's open UpOKA, R1) can use
For C's S4 data-layer guard failures at the arbiter-0 grant: uncontended requests switch the state LUT within its
feedback window without H_ARB (`ArbClean.q_clean_set/reset`, target instances ArbViewPS*); contended ones only
settle by (last input change) + T, value unknown (Spec ArbOK), so the certificate must branch; the server-path
separation (`spec_double_ack`, `one_ack`) and T ≥ the state-LUT delay (audit T5) must come with any such edge.
A note only; no new Lean.

### progress 19:3x -- consistency check: the κ = 0.40 node IS a RaceTablePS row, but the failing race is a different pin
SLICE_X16Y21.A6 (node 37463) is row 73 of `RaceTablePS.raceTable`; `table_race_free` (κ = 83/200) says its FEEDBACK
loop (pin 4) is no slower than its simulated acknowledge path. The refutation slows its pin-0 route (the input from
the fork ucontrol_merge4_f), which is not that race: no B row covers a storage node's non-feedback input arriving late
relative to the rest of the handshake (an isochronic-fork / relative-timing race, C4's category; it is not among C4's
36 sites either, which came from narrow pairs). So no B theorem is contradicted, but the earlier reading "B's race
rows are safe to κ ≤ 0.415, so the frontier is in [0.415, 0.44)" was wrong in substance: the rows cover one race per
node (feedback vs acknowledge), and the margin of THE statement is below 0.40 because of a race the rows do not model.
Correction to the STATUS reading (A's file): B's 0.415 is a bound for the feedback races only, not a lower end of the
frontier.

### progress 19:3x -- merge10's ua2 race does not drop on wide pairs (simulation)
A's second race (merge10.uarb1.ua2 pin-0 route, `tools-A/target/out/k48w20_ua2_classes.json`; fails from 0.46 on
(1071, 462)) on the two wide pairs (0x49e9c618, 0x35bf992e) and (0x40000000, 0x60000000) at κ = 0.36, 0.40, 0.43,
w = 20: all correct. So the pair dependence is specific to merge4's arbiter, which the wide pairs exercise and the
narrow ones do not (consistent with the 0.43 sweeps, where merge10 ua2 did not fail on either wide pair).

## Session Mon Nov  9 07:10:38 UTC 2026 (shard B; session_01HC49FxhoCpLyX7S4DnzarL)
Start: lock taken 07:10 (previous B lock 2026-11-08 19:21, other session, > 90 min). Audit read (head dd23acde): every
row on B's files CONFIRMED, including T47 (B's κ = 0.40 refutation, own build + own simulation check); no open
REFUTED/OVERSTATED row on B's files. setup.sh running (fresh container).
**Today's item (B), claimed now so C and A do not duplicate it.** A has claimed the κ = 9/25 periodic refutation, and the
owner wants the extra capacity on S4/S6, so B works on C's S4 data-layer item 3 of 2026-11-08 15:21, **"tracing the
truncated latch holds" (R2/R3)**, which is a cell question: per truncated hold, is the latch close ordered before its
D's next change by a separation C's AO certificate can use, by one of B's latch-hold certificates (LatchHoldPinPS, 670
latches), or by neither (a race candidate)? Deliverables: the latch-by-latch classification (tools-B, untrusted), and
in Lean (Formal/Cells/) whatever generic lemma turns a hold certificate into the hold phase of C's `ChainOK` claim
chain. C's own tools (formal/tools/tocc) are read and run from a scratch copy only.

### progress 08:1x -- R2/R3 (truncated latch holds) traced: proof-rule and claim-builder gaps, no race found (untrusted Python)
Subagent, C's tocc pipeline re-run from a scratch copy (net.json/bnd.json from tools/cview/lean2json.py), pair (12,18),
g = 1, κ = 0, one midpoint run per corner. Outputs and tools: `formal/tools-B/r23/` (README.txt, table_c*.tsv,
trunc4_c*.txt, roots/guards_c*.txt, adv_summary.txt, datal_t.py = datal.py with truncations switchable).
- **Reproduced C exactly:** 82 / 46 of 264 guards fail (c = 0 / c = 1), as JOURNAL-C 11-08 15:21.
- **The truncations are the whole remaining failure:** suppressing the U->H (latch hold) and H->U' (re-open) unions
  makes all 264 guards pass at both corners (U->H alone: 30 / 30 left). Other truncation kinds are harmless.
- In the run, D almost never changes near a close: of 131 U->H truncations at c = 0 only 16 have a later D change,
  the nearest 8.6 ns after the close read (c = 1: 6 of 88, nearest 22.2 ns).
- Three classes (roots, c = 0 / c = 1):
  * **A (50+65+1 / 20): D's claim ends at an event causally BEFORE the close** (often the latch's own opening, large
    offset b). `ChainOK` can only join by a lower bound Sep(close -> claim end), which cannot exist here; the right
    join is an UPPER bound, close ≤ claim-end event + u with c2.a + u ≤ c1.b. Example SLICE_X34Y92.C5 (en
    X34Y92.A6, D X37Y79.D6): claim end = open A6(0)@321,592 + 50,498 ps; close A6(1)@331,299; slack 40 ns in the run.
    Its Up(open -> close) is blocked by a concurrent cause (SLICE_X11Y25.B6(2)), the same blocker as C's R1, which C's
    relative Up clause (JOURNAL-C 2026-11-09 08:10) addresses. Alone, X34Y92.C5's hold fixes 36 guards at c = 0.
  * **B (5 / 41): claim end and close causally unordered**, no common-ancestor bound (e.g. SLICE_X34Y65.A5, c = 1,
    run margin 36.7 ns, 12 guards). Not addressed.
  * **C (16 / 17): H->U' re-open setup, finite shortfall -162 to -2,099 ps**, 14 of them the registers enabled by
    SLICE_X22Y87.A6. Artefact: their D inputs are constant 0 in this run (high operand bits of (12,18)) but the claim is
    anchored at a recent control event instead of a constant (hInit / value) claim.
- Every guard-breaking hold latch is among B's 670 latch-hold certificates (κ bounds 0.73-0.87), but those are a
  different argument (physical enable->D chain, Spec level), not the AO Sep/Up the builder uses.
- Adversarial runs (enable route max / D min and the reverse, the 6 critical sites, both corners): gcd = 6, 0
  data-driven control changes, no latch changed while its enable read closed. Weak tests (real gaps 9-80 ns).
Not done: other pairs; a suppressed union is not a proof.

### progress 08:1x -- Formal/Cells/UnionUp.lean CLAIMED: claim chains joined by an UPPER bound (class A's missing rule)
Core Lean, no Mathlib; private olean build of its closure OK; `#print axioms`: propext, Classical.choice, Quot.sound
(chainOK_up_of_chainOK: none); no sorry/native_decide.
**Plainly:** two consecutive claims on one node with one value (c1 ends at event e1 + c1.b, c2 starts at e2 + c2.a)
join into one claim if e2 happens at most u after e1 (an `Up e1 e2 = some u` entry that is sound) and
0 ≤ c2.a, c2.a + u ≤ c1.b. `union_holds_up`; `ChainUpOK`/`chain_holds_up` (each link by C's Sep join or this Up join);
`chainOK_up_of_chainOK` (strict generalisation of `ChainOK`); `UpSoundT` and `upSoundT_of_up_sound` (C's
`AO.up_sound`, under its own hypotheses, gives the soundness the join needs, at the same horizon).
**Not shown:** the wiring into C's `timedU_follows`/`timedA_follows` (they take `ChainOK`; switching to `ChainUpOK`
needs UpSoundT at the induction horizon, which `up_sound` provides from the same hypotheses) -- C's file, proposed
here; classes B and C; any instance.

### progress 08:2x -- UnionUp: third join form through a common ancestor (`JoinAnc`, `union_holds_anc`) for class B
c1's end event at least s after an ancestor e0 (a `Sep` entry), c2's start at most u after e0 (an `Up` entry),
0 ≤ c2.a, c2.a + u ≤ c1.b + s: the claims join. `ChainUpOK` links now accept Sep, Up or JoinAnc. Same checks
(private build of the closure, standard axioms). Whether C's tables reach such an e0 for class B is being measured.

### progress 08:2x -- UnionUp made wireable into C's induction step (1 ≤ c2.a, upper bounds one tick behind)
In `AO.timedA_follows`' step, `chain_holds` is applied at t + 1 with `SepSound` at t + 1, while `up_sound` is only
available at horizon t (it is what proves `sepSound_step`). So the Up and JoinAnc joins now require 1 ≤ c2.a and
`chain_holds_up` takes `SepSound` at T and `UpSoundT` at T' with t ≤ T, t ≤ T' + 1. The hold claim c2 starts at
close + (enable pin delay) ≥ 1, so the condition is met by the latch phases it is for. Same checks (standard axioms).

### progress 08:2x -- UnionUp.timedA_follows_up CLAIMED: C's main AO theorem with the new chain joins
`Formal.Cells.UnionUp.timedA_follows_up`: C's `AO.timedA_follows` (safety: ideals, every exact change certified,
every data claim holds, separations sound) with data-claim chains in `ChainUpOK` form (Sep, Up or common-ancestor
joins). The proof is C's, copied, except the chain step: `chain_holds_up` with SepSound at t + 1 and UpSoundT at t
(`upSoundT_of_up_sound` from the induction hypotheses at t). Its hGC is weaker than C's, so it implies C's theorem.
Private build of the closure OK; `#print axioms`: propext, Classical.choice, Quot.sound. check.sh not yet run (setup
still building Mathlib). **For C:** a generator may now emit Up / JoinAnc joins for latch holds (class A/B of R2/R3);
liveness (`timedA_live`) with ChainUpOK not done (same one-line change expected).

### progress 08:2x -- UnionUp: liveness too (gate_firesA_up, timedA_live_up)
C's `gate_firesA` and `timedA_live` (proofs copied) with `ChainUpOK` chains, through `timedA_follows_up`. Private
build OK; standard axioms; no sorry/native_decide. So the whole AO chain (safety + liveness) accepts Up and
common-ancestor joins in latch claim chains.

### progress 08:5x -- class C (re-open setup, register enabled by SLICE_X22Y87.A6) on a full-width pair: correct (simulation)
Class C's shortfall was on (12,18), where these D inputs never change. On the full-width pair (0x49e9c618, 0x35bf992e),
where they do, the setup adversary (`latchsweep.py --pin d`: the latch's data-pin route at the top of its window, all
else at the bottom, corner 0, H_RUNT(20)) on all 32 latches of that register: 32/32 correct at κ = 0, 0.10, 0.20,
0.30 (`tools-B/ps/out/setup_x22y87_fw.txt`). Caveat found on the way: at κ ≤ 0.20 this pair's answer comes after the
sweep's default 3 µs cap (3.51 µs at κ = 0), so a first run reported spurious "no output"; rerun with a 9 µs cap.
(Yesterday's 0.43 sweeps finished under 3 µs: faster arcs.) Reading: class C is a claim-anchoring artefact on this
evidence too; the builder needs value-level / older-anchor claims for these D inputs. Not a proof.

### progress 09:0x -- Formal/Cells/UnionUpDec.lean CLAIMED: Boolean checker for ChainUpOK
`chainUpB sl ul c cs` over C's tables (`AO.sepL`, `AO.upL`), `joinB_sound`, `chainUpB_sound : chainUpB … = true →
ChainUpOK (sepL sl) (upL ul) c cs`; a toy (data claim ends at the open + 50, hold starts at the close + 3, close ≤ open
+ 20) discharged by `decide`. Private build OK; `#print axioms chainUpB_sound`: propext, Classical.choice, Quot.sound.
So a generator emitting Up / ancestor joins can have them kernel-checked like C's other tables.

### progress 10:2x -- check.sh OK on Formal/Cells/UnionUp.lean and UnionUpDec.lean (398 declarations, standard axioms)
setup.sh finished Mathlib (from source) and moved on to the whole-project build; stopped it (as A did yesterday: it
OOMs on B's large chunk modules and today's work does not need them). C's AO modules built with lake, then
`./check.sh Formal/Cells/UnionUp.lean Formal/Cells/UnionUpDec.lean`: textual scan OK, axiom audit 398 declarations,
[check] OK. (09:0x-10:1x: idle waiting on the subagent's re-measurement, which is still running.)

### progress 10:2x -- re-measurement: C's relative Up clause does the work; B's new joins join NOTHING on these pairs (untrusted Python)
Subagent, same scratch pipeline; files `formal/tools-B/r23/followup/` (README.txt follow-up section, gsum*.txt,
ao_uprel.py = C's ao.py + the relative clause, datal_t.py with UPJOIN/JOINANC switches). C's committed Python did not
yet compute C's 08:10 relative clause (Lean only), so it was added in the copy: one level, 8 latest common ancestors
as bases (a subset of what the Lean admits); Up also for events concurrent with e0, min over applicable disjuncts.
Failing guards (one midpoint run per corner, NPASS = 1; base = C's code, reproduced exactly):
| pair | base c0 / c1 | + relative clause | + Up join + JoinAnc |
|---|---|---|---|
| (12,18), 264 guards | 82 / 46 | **44 / 32** | 44 / 32 (0 links joined) |
| (17,5), 406 guards | 184 / 151 | -- | **158 / 128** (0 links joined; 0 start-side failures left) |
- **Plainly: today's UnionUp joins (Up, JoinAnc) are sound but did not fire once on these two pairs.** The large-offset
  class A cases are fixed by C's relative clause through Sep form iv (e.g. SLICE_X34Y92.C5: Up(open -> close) =
  45,569 ps within its 50,158 budget, 36 guards). The class A cases left have small offsets (1.4-6.3 ns) against Up
  bounds of 19-63 ns: Up exists but is 14-60 ns too large, and the D claim does end well before the close in the run
  too. Class B links have no common ancestor that works. So UnionUp is a generalisation with no measured use yet;
  the earlier reading "class A needs an Up join" was wrong once the relative clause is in.
- (12,18) residue: 42/44 (c0) and 30/32 (c1) trace to ONE root, latch SLICE_X25Y76.B5's re-open (H -> U'): its U' D
  claim starts at SLICE_X22Y87.A6(0) (374,823 ps) but the H phase ends at the re-open SLICE_X24Y77.A6(2) (381,661):
  shortfall -4,259 / -9,260 ps, while its D (SLICE_X22Y81.B5) last changed ~116 ns before the re-open: an anchoring
  artefact of the builder (the D claim should start at D's own last change). The other 2 per corner: U->H at
  SLICE_X36Y63.B6 / X36Y68.B6 (D = SLICE_X39Y53.B6, arbiter-0 area), finite margins -8.6 to -30 ns; this morning's
  hold adversary on them (enable route slow, all else fast, both corners) gave the right gcd and no hold violation.
- (17,5) residue: mostly U'->T class A (re-latch start), not root-traced.
**For C:** commit the relative clause into tools/tocc's Up computation (copy: tools-B/r23/followup/ao_uprel.py);
anchor U' D claims at D's last change (fixes 42/44 at (12,18)).

### progress 10:3x -- note for C (no Lean): the 57 gates that read one source on two live pins (TimedBridge's open item)
`GateFact` needs distinct pin sources. For these gates the pin NODES (`g.ins i`, distinct site-pin wires on the
decoded net, A1..A6) are distinct even when their collapsed sources coincide, so the gate can be kept un-collapsed by
one hop: pins = g.ins, arcs i = [its own pin arc] (CGateOK straight from GateOK), and each such pin node added to the
timed net as a k = 1 gate with the collapsed chain from the source (CGateOK of the copy chain). Then every pin list is
nodup. Not written; a design suggestion only.

### progress 11:0x -- (12,18) data layer down to 18/18 failing guards, one root (concurrent-branch Up bound); no race found (untrusted Python)
Subagent, on top of the relative clause; files `formal/tools-B/r23/followup2/` (README.txt, datal_t.py with REANCH /
LGTOPOFF switches, traces, h_rag_c*.log). Changes to the claim builder (copy only):
- `LGTOPOFF` (a builder bug): the guard-optimal end choice was also applied to a latch's own phase windows when the
  latch is the guard's data node, which broke its U->H union. With it off, SLICE_X36Y63.B6 / X36Y68.B6 join by the
  plain Sep join: the real D end (SLICE_X38Y51.A6(0), through the arbiter-0 state) is causally AFTER the close, Sep
  2,649 / 2,244 ps. No arbiter fact needed.
- `REANCH`: at a re-open, request the D claim from the start of D's own stable value (split into comb segments
  joined by Sep). Removes the SLICE_X25Y76.B5 root, but NOT yet sound as a cut: failing comb-segment links rise 3 -> 13
  (c0, worst -18.9 ns) / 2 -> 11 (c1), loop-cover CovTime failures c1 22 -> 48 (c0 2,751 -> 512); the guards depending
  on any failing obligation are unchanged in number (78 / 120). Missing in Lean terms: a value-level hand-over join
  at a mux whose select switches while both covered inputs agree (a GateProof with the select X across the switch);
  the builder does not produce it.
Failing guards: (12,18) c0 44 -> 20 (REANCH) -> **18**; c1 32 -> 20 -> **18**. (17,5): 158 -> 156, 128 -> 126.
- (12,18) residue, both corners: 18 guards on SLICE_X38Y78.A6 from one root, SLICE_X37Y71.B5 H->U' (-7,876 ps, c0).
  Its D (SLICE_X34Y77.D5) has two covers, bank latch SLICE_X30Y75.C5 and latch SLICE_X36Y69.B6 (whose D is the
  arbiter-0 OR SLICE_X39Y53.B6). The X36Y69 branch is concurrent with SLICE_X30Y76.A6(2); the best common-ancestor
  bound with the relative clause lets it come ~10.5 ns after that event, while in the run it comes 1.2 ns before. This is
  C's R1 pattern ("Y2", the arbiter-0 grant in the branch's past): it needs a tighter Up rule or an arbiter-aware fact.
  8 adversarial runs (setup race, concurrent branches skewed, both corners): gcd 6, 0 data-driven control changes; the
  branch gap stays ≥ 3.9 ns (c0) / 9.8 ns (c1).
- (17,5) roots: c0 class A with D-claim ends anchored at SLICE_X34Y76.A6(0) + 61-70 ns (SLICE_X34Y76.B6 T->U 126
  guards, X36Y71.C6 18, X35Y76.B5 12; Up-vs-missing not computed); c1 H->U' anchored at SLICE_X30Y76.A6(2), -12 to -13 ns
  (the same register-bank re-open / concurrent-branch class).
**Reading:** no hazard found in any of today's ~30 adversarial runs; what blocks a passing (12,18) certificate is
(i) the concurrent-branch upper bound (C's R1/Y2) and (ii) a mux hand-over claim form. Neither is a B cell question;
handed to C. STATUS list unchanged today (no hypothesis discharged); today's Lean (UnionUp, UnionUpDec) generalises
C's chain joins but has no measured use yet.

### progress 11:1x -- CORRECTION: today's B guard counts used C's unsound form-(iv) separations (d ≤ 0)
C (JOURNAL-C 10:38) found that the tocc pipeline accepted form-(iv) separations with d ≤ 0 while `SepOKA` (iv) needs
d ≥ 1. B's copies reproduced that pipeline, so every B count today (82/46 base, 44/32 with the relative clause, 18/18
with REANCH + LGTOPOFF; (17,5) 158/128, 156/126) is optimistic; C's sound base is 82 / 64 at (12,18). The qualitative
findings (which roots, the LGTOPOFF builder bug, no hazard in the adversarial runs) are not counts, but each root
needs re-checking with d ≥ 1. C asks B for the re-open latch-chain step (register-bank latches SLICE_X30-31,Y75-77:
"new D valid before the re-open is read" short by 1.35 / 1.45 ns at c0): B takes it, next entry.

### progress 11:3x -- register-bank re-open (C's handoff): no hazard; the blocker is claim anchoring; a NEGATIVE-offset fix is NOT sound (untrusted Python + reading the Lean)
Subagent, with C's d ≥ 1 fix applied to the copy (SEPIV1; C's r1b/lchk.py re-check NOT run). Files:
`formal/tools-B/r23/followup3/`.
- The 32 bank latches enabled by SLICE_X30Y76.A6 (C's "re-open" blocker): 30/32 latch the SAME value at every opening
  (both corners); the 2 that change have their new D long before the open. Between the open read and the D claim's
  start, D is stable: nothing in the D cones (257 comb gates, 110 leaves) changes in ±15 ns except bank latch C5 itself;
  a ternary (Kleene) check with the changing latches, or all 32 bank latches, set to X and the enable X keeps every
  unchanged latch's D definite and equal to Q. Adversarial run (enable path fast, all else slow, both corners): gcd 6,
  no data-driven control change, no bank Q change while closed, no D glitch.
- **Why the Lean step fails:** inside the D cone, SLICE_X28Y67.A6 reads two covers whose start events are the loads of two
  different registers (SLICE_X24Y77.A6(0) @273,748, SLICE_X28Y65.A6(0) @272,926), causally unordered; a claim has ONE
  anchor and `CovTime` needs a lower Sep from each cover's start to it, so the builder anchors at the bank's own opening,
  and the offsets then grow along the carry chain to ~2.3 ns > the enable's lo (~0.22 ns).
- Counts with the sound Sep: best config 48 / 48 failing guards, all rooted at that bank re-open step. The subagent's
  "ANEG" run (claim offsets a < 0) reaches 0 / 0, **but that is not a Lean-valid certificate**: C's `GateProof` and
  `claim_stepR` require 0 ≤ c.a, and the induction is causal (a claim anchored at a future event cannot be proved at
  time t). So 0/0 is NOT a result; 48/48 is the sound count of the best builder configuration so far.

### progress 11:3x -- Formal/Cells/CovUp.lean, CovUpMain.lean CLAIMED: pin covers timed by an UPPER bound from the claim's anchor
The sound replacement for negative offsets. `CovUp.CovTimeU`: a covered pin's start side may be justified by
`Up(c.A → w.A) = u` with 1 ≤ hi + w.a and hi + w.a + u ≤ c.a (the cover starts no later than the claim's anchor + u),
besides C's Sep form; so a claim can be anchored at a COMMON ANCESTOR of two causally unordered covers (here: of the two
register loads), with a ≥ 0. `win_transferU`, `claim_stepU` (C's claim step, proof copied, with UpSoundT one tick
behind), `GateProofU` (+ `gateProofU_of_gateProof`). `CovUpMain.timedA_follows_cu`, `gate_firesA_cu`,
`timedA_live_cu`: C's AO safety and liveness with GateProofU claims and ChainUpOK chains; they imply C's theorems.
`./check.sh` on UnionUp, UnionUpDec, CovUp, CovUpMain: 409 declarations, standard axioms, [check] OK.
**Plainly:** if a generator anchors such claims at a common ancestor and the Up bounds are tight enough, the bank
re-open step needs no negative offset. Whether C's Up tables are tight enough there: being measured. Not shown: the
Boolean checker for CovTimeU, any instance.

### progress 11:4x -- Formal/Cells/CovUpDec.lean CLAIMED: Boolean checker for CovTimeU
`covTimeUB` (C's covTimeB start test, or the Up start test) and `covTimeU_of_B` (sound); toy by `decide`. check.sh
on all five of today's files together (UnionUp, UnionUpDec, CovUp, CovUpMain, CovUpDec): 482 declarations, standard
axioms, [check] OK (run alone, file mode fails only because CovUp's olean is not in its private dir).

### progress 12:1x -- CovTimeU in the builder: C's register-bank re-open step PASSES soundly; 18/18 guards left, one R1 root (untrusted Python)
Subagent, copy of C's builder with `COVUP` (a claim with causally unordered covers is anchored at one of the latest
common ancestors e0 of the covers' start events; each cover's start by Sep or by `CovTimeU`'s Up form; c.a ≥ 0; sound
Sep (form iv d ≥ 1); no negative offsets). Files `formal/tools-B/r23/followup4/`. Failing guards of 264 at (12,18):
| config (all: relative Up clause, Up/ancestor chain joins, LGTOPOFF fix, sound Sep) | c0 | c1 |
|---|---|---|
| without COVUP | 60 | 48 |
| + COVUP | **42** | **30** |
| + COVUP + REANCH | **18** | **18** |
- **The bank re-open (C's handoff): all 32 bank latches' H->U' links pass at both openings**, smallest margin +6,868 ps
  (c0) / +18,404 ps (c1); their D claims are anchored at common ancestors of the two operand-register loads, each cover
  timed by an upper bound from that ancestor -- the case `CovUp.CovTimeU` was written for, and its first measured use.
- COVUP alone leaves one root (SLICE_X25Y76.B5 H->U', -9.8 / -24.0 ns), removed by REANCH; COVUP + REANCH leaves one
  root, SLICE_X37Y71.B5 H->U' (18 guards on SLICE_X38Y78.A6; -8.6 / -20.0 ns): C's R1 concurrent-branch case (the
  re-open of D-cover latch SLICE_X36Y69.B6, with the arbiter-0 grant in its past, unordered with X37Y71.B5's re-open);
  Up bounds from the common ancestor are 9-20 ns looser than the real gap; CovTimeU does not close it.
- **Not a passing certificate:** REANCH raises failing comb-segment links 3/2 -> 13/11 (worst -13.3 / -32.8 ns), and in every
  configuration 78 (c0) / 120 (c1) guards depend on a failing claim obligation (loop-cover CovTime, comb segments), as in
  C's base. The Sep/Up entries were NOT re-checked with C's lchk.py (different implementation, no table emitter).
  (17,5): 156 / 126, unchanged.
**For C:** CovTimeU (Formal/Cells/CovUp, CovUpMain with the AO theorems, CovUpDec) is the Lean form the builder needs for
claims over causally unordered register loads; the open items are R1 (concurrent-branch Up tightness), the comb-segment
joins under REANCH, and the pre-existing loop-cover CovTime failures.
