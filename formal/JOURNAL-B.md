# Shard B journal (cells: C-element, latch/link, arbiter)

## Verdicts (shard B)

All files below check with `formal/check.sh` (lake build of `Formal/`) and
standalone with `cd formal/lean && LEAN_PATH=.lake/build/lib/lean lean
Formal/Cells/<F>.lean` (core Lean, no Mathlib). Notes: `formal/notes/B-*.md`.

| track | verdict | evidence | effort to finish | buys |
|---|---|---|---|---|
| 5 C-element | **works** | CElemFn (8 INITs = spec; Kleene closed forms), CElemTiming (bounded delay: enabling input >= LUT+feedback delay, tight; four-phase spec with new fork condition), CTree (tree and flat C-element have equal reachable-state sets, all shapes, atomic-cell model, under four-phase with ack wait — not trace equality) | ~1-2 d: port to Core's real-time channels (probe 5d running), inertial/involution regimes, bd_c3/c4 timing | INITs machine-checked; the exact timing condition per cell; the ack wait shown necessary |
| 6 latch/link | **works** | Latch (mux latch, setup/hold, DACK rule H sufficient), LinkHandshake (four-phase refinement, token conservation, half-token bound, deadlock freedom for any N in an atomic-gate model with isochronic forks; unequal fork delays only N<=3; bundling inequality SUFFICIENT, necessity shown on one trace only — audit row 20), Bundling (delay lines; capture condition derived; rules I and F each miss a term) | ~2-3 d: compose C-element + latch into a link stage, W-bit lift, pipe | a derived spec for tighten.py rules H/I/F; reference spec for track 10 |
| 7 arbiter | **works** (all four probes) | binary: ArbBinary (runt trace, exclusion under named timing, tie to previous winner, runt from same-sense moves); Kleene: ArbKleene + TernarySound/TernaryPhases (exclusion for all 3-valued inputs, X only as (X,X), scenarios lifted to every binary trace under GMW delays, exactness witnesses); analog: ArbAnalog (Buridan/Marino impossibility with continuity proved by Gronwall; repelling equilibrium; bad-timing window between two exponentials) and ArbResolve (e^(-t/tau) law, probability and MTBF bounds, no fixed read time safe); handover: ArbHandover, ArbHeldTimed(2), ArbCorners (16 ps overlap is exact only in the simulator's corner-MIXED arc model, 0 at any consistent corner; held INIT meets the merge precondition in all interleavings of a ZERO-WIRE-DELAY model (isochronic A0 fork); RT1/RT2 both directions, numeric instances redone at consistent corners in ArbCorners), ArbA0Fork (rule J exact) | rates equal (0.5 d), explicit F (non-vacuity, 1 d), corner-consistent numbers (Bc running), DDE loop | exclusion tiers made exact: structural only for settled q; handover is relative timing; metastable tier provably only probabilistic, rate needs tau_r and T0 measured |

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
  site-pin delays (up to ~0.5 ns, not in nextpnr's SDF) and using a flat
  124 ps LUT arc (68-161 ps the wrong way). Proposed rule J' in
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
  --freq 100): at a consistent corner NO C-element violates H_SELORD and no
  latch bit violates the corrected rule I (feedback arc + site pins) or rule
  H with site pins, with or without the guardband; only the box reading
  fails (5-10 C-elements per seed, worst -585 ps). Thinnest: the rig's own
  2-cell ring urig.uenv1 (feedback on pin 1): +4 ps at the fast corner on
  seed 4, +24 guarded. Rule H with site pins drops to +40 ps guarded on its
  worst bit. Shipped rules all pass the same routes.
- Held arbiter: g1/g2 and A1/A2 exclusion across a handover are relative
  timing (RT1/RT2), contrary to the header's "structural WITH THE HOLD".
- Arbiter runt direction (7a): the runt comes from SAME-sense request moves
  within one loop delay (both rising from idle with a gap in (0, L), or a
  request pulse shorter than L, or A0 falling against a request edge);
  opposite-sense moves give q exactly one clean edge. bd_arb.v's header says
  the reverse. Exact simultaneity is the only deterministic tie. Ties go to
  the previous winner; alternation needs H_Q_BEFORE_REREQ.
- Bare-cell filtered overlap (8%): an isolated handover overlaps <= 72/94 ps
  for any request skew, below the filter; the observed events are not the
  digital handover overlap.

## Audit response (claude/audit REPORT.md, read 2026-10-27)

Rows concerning shard B, and what was done:
- Row 10 (REFUTED): "rule J uses a flat 124 ps arc (68-161 ps the wrong
  way)", "O6 rise 45-56, fall 100-124". Agreed: prjxray's two groups are
  FAST and SLOW corners (makesdf.py:63). Withdrawn. ArbCorners (Bc) proves
  every old instance is the corner mix and recomputes: rule J's flat 2x124 is
  exact (client 2) or 26 ps conservative (client 1); its real gap is the
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

North star (PROGRAM.md, owner, 2026-10-27; I read it late, at ~05:30):
digital only. The analog probes (ArbAnalog, ArbAnalog2, ArbResolve) are
outside it: kept as checked files, no further work. The arbiter is treated
as a digital race (ArbBinary, ArbInvolution, TernaryOnBits). Phase 1 task
for B: port Cells from Prelim to Core and delete Prelim. Phase 2: the whole
library against a handshake spec, and formal/out/cell_constraints.json.

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
