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
| Phase 3 support | **in progress: bridges to C's capstone, gate-level network closure** | ResetContract, ResetGcd*, Rig*, RigLaps, RigSrcWitness, ResetCapstone*, ResetWitness2, LutFbBridge(2,2Env), ContractBridge, IpowCells(T), AssumeGuarantee*, EdgeTimes*, FiniteRuns*, ZeroDelay*, RingPhys*, ArbNoWithdraw, ArbSettled, ArbMultiToken, ArbAMerge, SelfAuditB6-B8 | NETWORK THEOREMS (gcd_hw_safe_net/net2/net3, fin_net/fin_net3/fin_net3', and the chain forms gcd_hw_safe_chains/fin_chains) do NOT bind pin drivers or the cell set to the netlist (SelfAuditB9; audit P12b CONFIRMED and broader): a pinless cell's contract is the bare claim that its node is clean, so none of them enforces that a link's environment comes from a gate model, and the chain forms are per-link existentials whose end contracts equal Env1 in content. 'Gate-modelled' counts in earlier entries describe the INTENDED elaboration only. FIX (2026-10-31): FiniteNetBound.FGcdNetOKB binds every tied pin's driver to the cell the netlist names (63/175 links bound on both sides); gcd_hw_safe_fin_netB has a JOINT WITNESS on a gate-timed run in which the tied cells drive each other (BWitNet.gcd_hw_fin_netB_witness; unit LUT delays, one run). C's H_CELLS for all 192 non-link operators remains a hypothesis in every one of them (H_OTHER). Departure bounds assumed except on link chains (EdgeTimes). Infinite-run theorems exclude terminating runs (SelfAuditB8); finite form gcd_hw_safe_fin_links has a joint witness on C's real a=12,b=18 run, with each link's Env1 still assumed (finite network closure: Bfin2). Reset->capstone: H_MAP proved (generator byte-identical), H_CELLS_AFTER open. Rig every-result blocked (H_PEND_FAST). H_PIN (arbiter rise-side race) unchecked by any project rule |

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
