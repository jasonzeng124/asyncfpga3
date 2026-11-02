# Shard C journal (composition, ring, timing checker, netlist import, other tools)

## Verdicts (shard C) -- as the Lean says on 2026-10-29 (rewritten from probe aud2's draft)

- **Track 9 (rings): works.** Interleaving model (H_SI), bd_link_ctl ring: dead for N<=2;
  one token live iff N>=3 (`ring_three`); k tokens need N>=2k+1 (`k_tokens`); fair window
  N(N-1)/2 (`RingFair`). `RingGen` restates the headlines over the generated bd_c2n netlist
  (a flipped INIT breaks them). Timed: every stage toggles in every window of N*H (8o).
  9d: bdc's reset leaves every ring EMPTY (all ring cells clear on rst, from the INITs;
  `bdc_closed_ring_empty`), so the token enters through the loop entry: for bdc's shape
  (bd_mux -> N links -> bd_steer) a kernel-checked reachable set (real LUTs, zero reset, one
  start token, env hypotheses H_START_ONCE/H_CTL_ENV/H_EXIT_ENV) has exactly one token and no
  deadlock for N = 3..5 and deadlocks for N = 1, 2 (`RingResetCert`). Timed: `timed_ring_three`
  (inertial per-stage bounds; iff N >= 3), also for bounded pure FIFO delay (`pure_noOvertake`
  closes 8d's goal 2); rise-to-rise >= N dmin (>= 6 dmin at N=3), tight; no runt on any stage of
  a persistent ring (`ring_no_runt`). Not covered: exact cycle time, loop N > 5, other cells on
  the cycle, a gate-level environment.
- **Track 8 (composition, gcd_hw): safety proved, liveness reduced, rig first result only.**
  Token level: bdc's gcd_hw graph returns Nat.gcd a b for a, b < 2^31 on every schedule,
  live and bounded without fairness (8i/8k); ipow likewise for all i32; collatz conditional
  on C termination (8v). Circuit level, concrete 465-channel network from bdc's own graph and
  link placement: `gcd_hw_circuit_safe3` -- every out0 latch is gcd a b under H_CELLS (Ops
  gate models), H_BUNDLE (on zero-delay traces) and H_START_ONCE; one explicit run satisfies
  all three and latches 6 = gcd 12 18 (8t; audit CONFIRMED). ipow: `ipow_circuit_safe3` (8y).
  Generic (8y2): `KCap.kernel_circuit_safe` proved once for any kernel given as data [KD] plus
  46 decidable/C-reference obligations [KP]; gcd_hw and ipow are instances (same statements),
  xorshift is new at token level (every seed, every 32-bit rounds) and circuit level
  (`xorshift_circuit_safe`), collatz at circuit level conditional on C termination
  (unconditional 1 <= n < 256). Negative controls (mutated MLIR constant, walk row) fail the
  build. Witnesses that latch a value (wit): xorshift (seed 2463534242, rounds 4 -> 2008045182),
  collatz (n=7 -> 16), expected values from gcc on kernels/*.c; `gcd_rig_all_witness`: one rig
  run (12/18) re-offering start during out0's return-to-zero, latching 6 twice. Unit delays,
  one input each; the rig witness needs a start high at reset (an all-low start cannot rise
  under RigEnv).
  Rig (re-offers start): EVERY result (8s3): `gcd_rig_all` -- under H_CELLS (without
  Src.iz), H_BUNDLE, the rig's env gates `RigEnv` (uenv1/uenv0 = C(a,not b), from the INIT)
  and a, b < 2^31, every value out0 offers or latches, in every invocation, is gcd a b.
  Invocations overlap (out0's return-to-zero, a lagging sink branch) harmlessly; the needed
  env condition H_START_GATE is derived from gcd_rig.v's env cells, not assumed. Witness: a
  two-latch rig run (wit). Not: liveness, CMPD/compare logic.
  Liveness: 8z's open obligation H_NO_DEADLOCK' is FALSE as stated (`nd_counterexample`, 8z2:
  a run meeting the other six hypotheses where start's LUT never releases its request, so
  out0 never closes). Repaired: `gcd_hw_live_final2` -- first out0 within an explicit bound,
  value gcd -- under the same cell/env hypotheses plus H_START_REL (start's request falls
  within H of its ack; shown necessary) and the weaker H_NO_DEADLOCK'' (OPEN; 320 random
  bounded-delay runs: no deadlock). 8z3: every gcd_hw gate is persistent under H_CELLS,
  H_BUNDLE, H_START_ONCE (`gcd_hw_persistent_all`) EXCEPT the 22 mux input-ack C-elements,
  whose falling excitation can be withdrawn (`mux_full_pers_false`, local; reachable in
  simulation, never deadlocking), so the confluence route needs repair. 8z4: generic timed->interleaving serialization theorem
  (`serial`, `trace_nodead`; rank hypothesis necessary: `arb_not_reach`) and `mux_out_not_mux`
  (no mux output feeds a mux, so a rank exists); its other premise (`hex`) not instantiated for
  gcd_hw. Exhaustive interleaving search (Python): no deadlock in ~2.7 M states, incomplete. The
  walk route needs a combined well-founded measure (data arrival + return-to-zero waits). Joint witness for every hypothesis of both
  theorems: one run (12/18, H=1) closing out0 at tick 473 with 6. Do not cite 8u's
  `gcd_hw_live` (likely vacuous) or 8z's `gcd_hw_live_final` as a liveness result.
  Physical refinement (8x): under per-arc BoundedDelay semantics (glitches allowed) a node
  quiet from t already holds its zero-delay value (`run_settles`), so a tcheck PASS row fixes
  the sampled VALUE: per channel, `held_dag`/`held_cert` give Ops `Held` on the observed
  channel (under H_TXWIN; witness and necessity example proved). `gcd_hw_circuit_safe_phys`
  drops H_BUNDLE for per-channel certificates, but needs H_ZD_AGREE (physical trace agrees with
  an Ops trace) and H_DERIVED (376 of 465 channels have no tcheck row). 8x2: cells relaxed
  to require data only while the output is busy (`OpsBusy.CellB`; old Cell implies it; capstone
  re-proved on it), so the observed run is the Ops trace and H_ZD_AGREE is gone
  (`gcd_hw_circuit_safe_phys2`); fork/join/steer/link/src propagate bundling, so only 31 root
  channels need certificates (`gcd_hw_circuit_safe_phys3`, at the cost of H_SEND); exactly 2
  roots lack a tcheck row (chan 463 acc251 bus, chan 415 umux21 select). 8x3:
  `gcd_hw_circuit_safe_phys4` -- every out0 latch is gcd from H_CELLS_B (relaxed gate models on
  the observed run), H_START_ONCE and tcheck certificates on 26 root channels only (all have an
  A row); protocol and Held on all 465 channels derived by one joint induction over time
  (`OpsBusy2.net_joint`), so H_SEND/H_RECV are gone; `amergeB_held` makes 5 arbiter stages
  structural. Witness: 8t's run (roots `exempt`). Open: deriving H_CELLS_B's data fields from
  the netlist (H_FN, H_LAUNCH), H_TXWIN. 8x4: `fieldOf_row` for every cell kind (handshake
  half + protocol + Held + a tcheck Row => the data field); `gcd_hw_circuit_safe_phys5` needs
  per-operator handshake halves, per sampled output a Row or (ghost) the field, H_START_ONCE,
  26 root certificates; `phys5_gen` discharges H_FN by decide against Formal.Gen on 176 of 221
  sampled channels (H_FN assumed on 45: bjoin, compute join, extui steer, out0). CAVEAT: on
  gcd_hw the only witness takes every channel as ghost, so the Row form is witnessed only on a
  toy; a routed witness is the job of probe cap. The generated-cell derivation of the gate fields is not yet composed into H_CELLS
  (O4): done with named gaps -- `gcd_hw_circuit_safe_gen` / `gcd_rig_all_gen` replace H_CELLS by
  H_GEN (each of the 367 operator instances obeys its yosys-generated netlist, LUT outputs move
  to their function of the previous tick's inputs) plus three timing conditions shown REAL by
  kernel-checked counterexamples: H_CHAIN_SETTLED (side-tapped delay chains, incl. bd_link's
  uack, can emit a runt: `fastfall_hazard`), H_LEAF_PERSIST (two-level C-trees, fork N=5,6),
  H_WIRE_DI (cells whose req/ack are literally one net need a >= 1-tick route). Data paths,
  selects, grants, H_R0_ISO stay copied hypotheses; a flipped INIT bit breaks the proof. Joint
  witness for H_GEN only quiet. No tcheck row checks H_CHAIN_SETTLED yet. O4b: generic over kernels
  (`CellBind.K.kernel_circuit_safe_gen`; gcd_hw, ipow, collatz, xorshift instances); found O4
  missed the 3-input compute join (O4's H_GEN is provably unsatisfiable on ipow and collatz:
  `ipow_O4_vacuous`), now covered; H_LEAF_PERSIST and H_REQ_PERSIST PROVED by a joint induction
  with the protocol (`PersistK.kernel_circuit_safe_genP`). Quiet witnesses only (no ipow run). Pipelines: FIFO + live given per-link obligations, under H_SI and an isochronic
  fork (8a); gate level for every n (9c); Muller feedback condition from delay bounds, exact,
  n<=3 (MullerTimed). Hypotheses: notes/C-gcd_hw-hypotheses.md §0.
- **Track 10 (verified timing checker): works; delay data is the limit.** Interval STA
  sound (audit CONFIRMED); per-node exact only over the choice of cell functions (an upper
  bound for fixed LUT functions, CheckerFixedFn). Shared-prefix credit sound under
  H_CLEAN_EDGE (10l). Rules E/A/J each have a proved counterexample on constructed netlists;
  rule A under E's band is sound exactly for data paths <= 403 ps (SLACK = 0). nextpnr's SDF
  carries slow-max only (no lower bounds). tcheck on gcd_hw (4 routes) and collatz/xorshift/
  ipow (12 routes): every disagreement with the project rules is project-PASS/tcheck-FAIL,
  none at a fixed prjxray point; rule A and tcheck both time GND/VCC tie-offs as data (false
  path). OUTMUX (10m): the audit read C-10g; C-10h already had the hop. tcheck's prjxray arcs
  equal the auditor's independent xrc.py on all 86,037 common arcs (gcd_hw s4) and 17,800
  (collatz s2) within 11 ps (hull of xMUX/xMUXL aside: <= 34 ps high, safe side). One leftover
  OUTMUX bug in the J shared-path split fixed: all 72 J clients now match xrc within 15 ps;
  BQ#1 merge6#1 passes, s4 merge12.uarb2#2 fails only under the band (-116/-204). Tie-off
  (GND/VCC) starts dropped from rule A as a false path (H_FALSE_CONST): gcd_hw verdicts
  unchanged; kernel rule-A rows with tie-off starts flip FAIL->PASS. No row anywhere fails at a
  consistent corner without the band. ipow's DSP48E1 arcs still fall back to the SDF band.
  Rule K (10l2): the 16-24 failing rows per seed were a front-end bug (the control C-element's
  maximum-node arc pinned to req_in, ignoring the wait for z_ack to fall; plus a latch-output
  shortcut), not a race: with the fixed rule all 42 rows pass on 4 seeds in all 6 corner
  models (worst +979 ps with per-pin arcs). Rule K actually checks B's X3 hold half
  (bd_mux.bundled_s_hold), not X4. `RuleK.mux_joins_ruleK`/`ruleK_exact` tie the fork form to
  the real join INITs; H_ROUND_TRIP not derived from the netlist.
  Chain settling (10o, O4's H_CHAIN_SETTLED): exact iff condition proved for AND/OR delay
  chains under per-arc bounded delay (`ChainSettle.settled_iff`, converse `runt_of_gap`). On
  16 routes (gcd_hw 4 seeds, collatz/xorshift/ipow 4 each): the 744 new bd_link uack rows pass
  in all six corner models (worst +12 ps); 9 FASTFALL lines fail under the band only (worst
  -589 ps, gcd s4 ucontrol_merge12); rule F passes all 9 (it is evaluated at the SDF point only)
  and never checks the uack lines, so it does not cover the condition. C-10k's Fd rows miss a
  LUT pin-delay term (2 rows Fd +26/+21 vs exact -5/-10). Chainck's interval code is untrusted
  Python mirroring the Lean lemmas. RT_FB with the OUTMUX hop (10f2; same routes, byte-identical
  FASM): the audit row is right -- on gcd_hw seed 4 the rig's uenv1 C-element fails RT_FB by
  -16 ps in the per-element fast model (was +4); the kernel alone still has 0 failures in every
  one-corner model on all 4 seeds (worst fast +70). With every element at one common corner end
  uenv1 passes by >= +167 ps (Python), so the failure comes from taking one shared hop at max on
  feedback and min on response. 64-stage Muller: slowE 1-8 of 64 stages fail per seed (mean
  3.9, was 7.2). Kernel-checked violating run: gcd4_fast_exact.
- **Goal 3 tool (vk): works.** `formal/tools/verify/verify.sh <kernel> [--route DIR]`: MLIR
  import + drift; committed hand proof re-checked against a fresh import; bounded search of
  every schedule against the compiled C (prints the counterexample schedule or the infinite
  loop); generated per-vector Lean theorems for any kernel (complete runs end with the C value;
  no hand proof needed, listed vectors only); circuit-network regeneration check; tcheck on
  routes with failing rows and arcs printed. PASS on gcd, ipow, collatz; xorshift proved on its
  vectors; negative controls (swapped operands, changed constant, wrong C, bad timing) FAIL
  with counterexamples; an equivalent mutant reports NOT PROVED (hand proofs are syntactic).
  How-to: notes/C-vk-verify.md. ipow routed on 4 seeds: banded rows fail mostly via DSP
  fallback arcs (known front-end gap).
- **Gen: done.** All 36 cells/rtl modules generated from the project's yosys and tied to
  B's transcriptions (163 theorems); a flipped INIT breaks the build. bd_mem's BRAM opaque.
- **Track 11 (netlist import): works for LUTs.** yosys import: binary next-state equal to
  independent specs (Kleene: same INIT and pin order as B only). Bitstream: physical INIT +
  pip-walked pin map of routed bd_c2/bd_link/bd_arbiter (4 seeds) computes the logical cells;
  mutated INIT/pips caught. The placer's pin permutation is real and moves delay by up to
  ~0.5 ns. Whole design (11f, rebuilt): the routed gcd_hw (kernel +
  rig, 9623 cells; FF/CARRY4/MUXF7/F8/route-through/constant LUTs decoded) read back from its
  .bit; Lean proves for route d that all 10629 physical instances compute their renamed yosys
  cells (`gcd_hw_d_netlist`) and that all 5645 library-cell LUTs have the INIT of the
  Formal.Gen cell (`gcd_hw_d_cells_init`); seeds 2, 3, 4 pass the Python mirror only. Mutated
  INIT/pip/FF init/clock inversion caught. Trusted, not proved: FASM site decoding, yosys
  flattening, the FF/CARRY4 Gen models; rho not proved injective; functions only, no timing.
- **Track 12 (other tools): bound-finders and corner sweepers, not provers (~1 day per
  tool).** 12d redid 12a/b/c at one consistent corner and under the corner model: the 16 ps
  handover race, the 56-60 ps server latency, 12a's 152 ps aperture and k >= 10 were corner-mix
  artefacts (gone at every consistent corner). Surviving forms, corner-dependent (TChecker):
  A0-rise fork breaks iff wa >= 2 O6lo + c_lo (94 ps FAST / 204 ps SLOW; old 116 was a FAST_MAX
  point); q->ugrant route mutex iff wq_g < 42 / 100 ps; A0-fall fork k >= 3 lut + 2 route.
  C-element bounds unaffected. New: a kappa-dependent held-ack server condition (fitted on
  every tool row, not proved). Not re-established: 12c's pure-delay "holds" rows (zones do not
  finish at rise = fall). UPPAAL/Workcraft/PRISM still 403; IMITATOR binary fetched but not
  run (unvetted download).

## Session Tue Oct 27 02:58:16 UTC 2026

### progress 02:58
Took LOCK-C (was epoch/none). A's setup.sh exists; running it (Lean 4.35.0 +
Mathlib from source). Next: Formal/Net/Prelim.lean and probes for tracks 8-12.

### progress 03:02
Lean 4.35.0 up (A's setup.sh; Mathlib still building from source). Toolchain
cache restore (cloud/toolchain-cache.sh fetch, key d7ce266cff0c8e1e) running;
needed zstd from apt first. Net/Prelim committed (Nat-ps traces, as shard B).
11 probes launched: 8a Handshake (protocol-level assume-guarantee FIFO),
8b Kahn (token semantics, determinacy, gcd = C gcd), 8c Muller (gate-level
LUT C-element chain; SI exhaustive check fallback), 9a Ring (why 3 stages,
proved or refuted), 9b RingCheck (verified min-cycle checker vs emit.py),
10a Timing checker (interval STA sound + exactness), 10b rules E/A/J
(semantics, counterexamples), 11a yosys JSON -> Lean, 11b FASM -> Lean
(physical INIT after pin permutation), 12a SAT/SMT, 12b Workcraft/UPPAAL.
Probes compile with core Lean via slot.sh; only the lead builds.

### progress 03:12
9a done and committed (Ring.lean, 110 decls, axiom audit clean; imports B's
Cells.CElemFn). Surprise: tb_ring.v's occupancy sweep never varies the token
count (every 0<K<N reset carries one token), so a 2-token ring was never
tested on the bench; N=4 with two tokens is dead. Launched 8d (SI
interleaving -> timed traces bridge, to discharge H_SI for Ring/Muller).

### progress 03:20
10a and 8a committed after my own per-file compile + axiom audit (I fixed one
doc comment in CheckerToy that tripped check.sh's textual scan: the word
native_decide in a /-- -/ comment). Finding from 8a: the bundling window must
end at ack-fall (latch closes), not ack-rise; internal links need only
control-event separations. Killed Mathlib's `cache get` (9031 x 403, 18 min);
Mathlib now builds from source. Launched 8e (checker accepts => pipeline FIFO).

### progress 03:35
Committed 10b (Rules), 11a (Import), 11b (Fasm) after per-file compile +
axiom audit (B's CElemFn/CElemTiming/Latch/ArbKleene also audited clean as
deps). Lead fixes: trimmed 11a's yosys JSON to the top module (write_json
dumped ~420 blackbox primitives, 10 MB/cell; drift check still passes); doc
comments mentioning sorry/native_decide reworded (check.sh's textual scan
excludes only '--' lines). Environment: probes apt-installed libtcl8.6 and
libboost 1.83 libs, pip simplejson/textx/intervaltree (nextpnr/prjxray need
them; not committed; setup gap for cloud/setup-toolchain.sh's cache path).
.bit files are not byte-reproducible (4 header bytes differ across
xc7frames2bit runs): CLAUDE.md's cmp on bitstreams gives false differences;
compare FASM or frames.
PROGRAM.md gained a 48-h plan (owner). Shard C: Phase 1 = import every cell into
Formal/Gen/ (launched 11d); Phase 2 = compiled verified checker on real routes
(10d running; needs a lake exe target in A's lakefile); Phase 3 = composition
through Dynamatic ops + gcd from bdc's netlist (8b/8e). Launched 10c (prjxray
vs SDF on the 128-ring data), 10d (checker on routed FASM), 11c (routed link +
arbiter import). Risk: B is deleting Cells/Prelim; Import/Fasm/Ring import it
and will need porting to Core.

### progress 03:45
9b RingCheck committed (checker proved exact for the per-simple-cycle rule;
per-kernel >=3 proofs for 9 fixtures, kept in Wip/C9b/certs since gcd takes
883 s; agrees with emit.py on all 36 graphs). 10c committed (Python): the
128-ring silicon comparisons all predate nextpnr-xilinx-lut-perm-sink.patch;
against the current SDF measured/predicted is 1.067 (was 1.361), prjxray
0.989; ~9% short-ring excess unexplained; recommends re-measuring the rings on
the current binary. Owner notified. Launched 8f (Dynamatic op composition,
Phase 3).

### progress 03:59
Committed 8b (Kahn, 966 decls), 8d (Bridge, 216), 8e (EndToEnd, 225); 8c
(Muller) audit running (~6 GB). INCIDENT: shard A's commit bb9f5e2 ("WIP
snapshot") overwrote/deleted files A does not own -- C notes (C-8b, C-8d,
C-8e, C-9b, C-10c, C-11c, C-11d, C-12b), C Wip files, and B's notes
B-gls-compare.md and B-lib-end-mem-mlink.md. I restored every C file from my
working tree (verified byte-equal at HEAD); B's two notes are B's to restore.
Shard A: please add only paths you own. Launched 8g (Muller timed feedback
race from delay bounds) and 8h (per-link margins, rise/fall delays,
per-event delays, open-width numbers).

### progress 04:01
8c Muller committed (two doc comments reworded for check.sh's scan). 12b done
(files landed via WIP snapshots): Workcraft/UPPAAL/TChecker/PRISM downloads
all 403; Storm + own front end on the real INITs. Results: C-element spec
holds iff env min response >= feedback max (exact; LUT spread irrelevant --
B's bound adds LUT spread because its channel allows overtaking: possibly
slack, for B to settle); shipped bd_arbiter needs server latency >= ~60 ps and
A0->ustate rising skew < 116 ps, conditions the header presents as
structural; pure delay breaks mutex via runts. Evidence for fixed integer
delays, not proofs. Memory: the sandbox cgroup kills processes at ~5 GB (also
killed Lean twice). Launched 12c (TChecker by git clone, dense-time zones).

### progress 04:09
11c committed (routed link+arbiter bits == yosys import, 4 seeds). My own
error: during the incident restore I did rm -rf Wip/C* then copied a backup,
which deleted Wip/C11c files created after the backup; 11c regenerated them.
Mathlib abandoned in this sandbox: setup.sh's retry loop re-ran lake update
-> cache get (9031 x 403) repeatedly; killed it. Shard C's files are all core
Lean, so I verify per file (compile + collectAxioms audit) instead of
check.sh's full lake build (which needs Mathlib for A's Core). Launched 10e
(compiled tcheck exe on real routes, row-by-row vs rules A/E/F/H/I/J).

### progress 04:22
10d committed (bucketed checker, 3000 arcs in 7.9 s kernel decide; routed
ce_pair and a 64-stage Muller pipeline). Finding: RT_FB (C-element feedback
before neighbour response) fails on 12/64 stages under prjxray slowE intervals
(worst -138 ps), feedback placed on B1/C1; SDF says +419 ps. One seed;
Elmore unvalidated; passes only under near-perfect on-die correlation.
Owner notified. Launched 10f (seeds, a shipped kernel route, pin constraints).

### progress 04:30
8h committed (per-link end_to_end2; rise/fall pins; per-event pins under
H_PULSE; Prelim's BoundedDelay admits echoes no pulse condition excludes --
three probes (8d, 8e, 8h) now agree it is the wrong channel for these proofs;
NoOvertake/EPin are the usable ones; flagged for shard A's Core). Launched 8i
(gcd graph imported from bdc, not hand-drawn).

### progress 04:55
API session limit hit (resets 04:50 UTC): probes 8f, 8g, 8i, 10e, 10f, 11d,
12c stopped mid-work; their work so far is saved in the tree (Wip/notes
snapshotted; unchecked Formal/ files left untracked). 12a still running its
own background jobs. Will resume each probe after the reset.

### progress 05:16
Resumed the 7 probes after the reset. Committed 11d (Gen), 8f (Ops), 8g
(MullerTimed) after compiling every dependency myself (new helper builds
Formal.* deps by mtime) and an axiom audit (Gen 590, Net 1409 decls clean).
Note for A: check.sh FILE mode (.lake/checkfile) fails on files whose
Formal.* imports are not also passed (reported by 8f/8g). Launched 8j
(control_merge, witness, liveness) and 11e (port shard C off Cells.Prelim).

### progress 05:18
10e committed: tcheck (compiled, proved core) on 4 gcd_hw routes agrees with
rule I 75/75 and rule H 157-158/158; 2 H rows pass tighten but fail under the
project's own guard band once prjxray site-pin delays replace the SDF's flat
pin charge (thin margins, not predicted failures). Incident: 10e ran
slot.sh lake build in formal/lean by mistake (slot.sh cds there) and compiled
Mathlib for ~17 min before killing it; only .lake/packages build dirs touched.
Launched 10g (rules A/E/F/J + 8e races + RT_FB rows in tcheck).

### progress 05:57
8j committed: negative result -- the hand-drawn gcd graph used by 8b/8f
deadlocks for every a != 0 (no storage on the data loop); gcd_circuit is
non-vacuous only at a=0. This is why theorems need a liveness/witness check.
10g committed: tcheck covers A/E/F/J/H/I + two unchecked races on 4 gcd_hw
routes; every disagreement is project-rule PASS vs tcheck FAIL under prjxray
site pins + the project's own band (thin margins); J's pip estimate
over-credits by ~95 ps avg. RT_FB thin fail on the env C-element (2 seeds).

### progress 06:09
Committed 12a (z3 BMC/k-induction/Spacer), 11e (port toward Core: 22 modules
Prelim-free; audit 5216 decls), 8i (gcd_hw graph from bdc computes the C
function on every schedule; audit 832). Process fix: my push helper had been
doing 'git add -u' on claimed dirs, so in-progress edits to already-claimed
files (11e's) entered WIP snapshots before review; all of them were then
rebuilt and audited clean, and the helper now adds only notes/Wip/tools.
Launched 8k (gcdC = Nat.gcd on [0,2^31), termination, combined corollary).

### progress 06:18
8k committed: gcd_hw's bdc graph computes Nat.gcd on [0,2^31) and is live at
token level (audit 1109). Launched 8l: capstone refinement (link + N-way mux
op cells, Ops refinement on the imported graph with bdc's link placement,
circuit liveness) and shard C's hypothesis list for the gcd_hw theorem.

### progress 06:22
12c committed (TChecker by git clone; dense-time exact thresholds). New
candidate failure in the shipped held bd_arbiter: mutex depends on the
q->grant-LUT route vs its ustate copy (H_GRANT_FORK; inertial wq_g < 56 ps,
transport fails once wq_g > wq_s). No B file states it (grep). For shard B:
please check against Arb*. Launched 10i to measure wq_g/wq_s on the 4 gcd_hw
routes and link_arb, before raising it with the owner.

### progress 06:34
10f committed: the C-element feedback race is real on bare Muller rings on all
8 seeds (slowE 4-12 of 64 fail, worst -116..-231 ps; feedback on pins 1-3,
no pin constraint exists anywhere in the flow), but NOT reached on shipped
gcd_hw on 4 seeds in any one-corner model (worst slowE +234 ps; response
paths are 2-5 LUTs). Only the test rig's bare 2-cell ring is thin (+4 ps).
This answers my earlier notification: a risk for bare rings, not for gcd_hw.

### progress 06:45
10h committed: tcheck's Python path-picking replaced by a proved potential
certificate (pot_sound, cycles allowed); front-end gaps closed; agreement A
199/200, E 465/472, F 113/116, H 630/632, I 300/300, J 71/72; every residual
disagreement fails only with the project's own band on prjxray corners and
passes unguarded. Launched 9c (Muller chain for all n by a local invariant).

### progress 06:50
10i committed: H_GRANT_FORK is live on 32/40 routed bd_arbiter instances
(runt up to ~1.2 ns on a grant wire at SLOW_MAX; pin assignment); evidence
that the handshake survives (runt ends >= 342 ps before A0 can rise), not
proved. Owner notified, with the 10f follow-up (gcd_hw C-elements safe).

### progress 07:14
8l committed (audit 1773). Not yet an unconditional circuit-level gcd
theorem: open O1 (circuit follows the token run's control_merge labels), O2
(total stream solution), O4 (Ops gates = generated cells + C2), O5 (circuit
liveness), O7 (concrete network). Launched 8m (O7+O2+O1 -> gcd_hw_circuit_safe)
and 8n (O4 + bounded-delay liveness).

### progress 07:22
9c committed: the gate-level bd_link chain is hazard-free / four-phase / in
order for every n (iso, rt and timed under FbBound) via a two-position
adjacency invariant + kernel-checked windows + gluing lemma.

### progress 07:24
10j committed: the grant-fork runt never breaks the handshake on the 36
routed gcd_hw arbiters at 4 corners (proved; per-instance kernel verdicts;
H_CAUSAL_PATH, H_FF_DRAINED). Owner notified. Clean rebuild of every claimed
shard-C file into a fresh olean dir running (stale-olean check).

### progress 07:35
8n committed: Ops gates = generated cells under H_FB_FIRST (B's C2), and
bounded-delay liveness for an n-link pipeline of generated LUTs (exact at
unit delay). Launched 8o (per-token period, linear ring bound, op-cell ring)
and 10k (unchecked capstone timing hypotheses as tcheck rows on gcd_hw).

### progress 08:00
8o committed: linear ring liveness bound N*H; pipeline period (2n+3)H for
n<=3 by certificates. gcd_hw liveness blocker named: the 8 arbitrated
control_merges need a no-contention proof (no bounded arbitration time on
this fabric) -- to follow 8m's O1.

### progress 08:12
10k committed (capstone timing hypotheses as tcheck rows; all pass at
sdf/fast/slow; band-only failures listed; status merged into
C-gcd_hw-hypotheses.md). 8m committed: gcd_hw_circuit_safe (audit 2649).
Launched 10l (shared-prefix credit, max-node, X4/M3/C7 rows) and 8q (O1).
Clean rebuild: 139 modules ok, 0 other lines.
Clean rebuild finished: every claimed shard-C module tracked at its start
(136, plus Core/Cells deps: 139 modules) compiled from scratch into a fresh
olean dir with no error, so no result depends on a stale olean copied by a
probe. (Files claimed since then were each compiled on commit.)

### progress 08:27
8q committed: H_CM_FORCED -> H_CUT; gcd_hw_protocol needs no forcing
assumption; no free arbiter contention under H_CUT. Launched 8r (discharge
H_CUT via the single control-spine token).

### progress 08:58
8r committed: gcd_hw_circuit_safe'' needs only H_CELLS, H_BUNDLE,
H_START_ONCE, H_WALK. Finding: a free-running start source violates H_CUT
(argued with a=12, b=18), so the env must offer start once per result.
Launched 8s (prove H_WALK; model the rig's env ring for H_START_ONCE).

## Session Tue Oct 27 10:58:27 UTC 2026

### progress 11:04
Took LOCK-C (previous lock 2h stale; that session died after 8r, with 8s and
10l running). Lean 4.35.0 from setup.sh; Mathlib's from-source build killed
again (shard C is core-only; `lake build Formal.<Mod>` builds only the
module's Formal deps). FPGA toolchain restored from the cache branch and
cells/verify/toolchain.sh passes (9 patch fingerprints ok; nextpnr sha256
9c732bc6303458df). Recovered 10l: its two Lean modules existed only as
tcheck's synced copies; restored verbatim to Formal/Timing/{MaxNode,
SharedPrefix}.lean (sync.sh --check: same), compiled, audit clean (142
decls). 10l's results (summary10l.txt) show rule K (B's X4 ctl_req fork)
failing 16-24 of 42 rows per seed even unguarded, by up to -5.9 ns: not yet
diagnosed, so no verdict; probe 10l2 is on it. 8s's work was lost (nothing
saved); relaunched.
Audit (claude/audit REPORT.md) rows on shard C, all still unanswered:
win_exact exact only over all cell functions (C.md #1); corr_bd_violation's
per-event "justification" needs a wire to glitch (#2); Ring header bound
N(N-1)/2 vs proved N(N-1) (#3); ring_three over a hand ctl, INIT only via a
bridge (#9); Rules "<= 402 ps" leaves 403 (C2); Import "equal to B's Kleene
specs" is same-INIT only (C2); tcheck front end omits the slice OUTMUX hop
(tcheck.md; J numbers change sign on some rows); "+490 ps" is a mean;
RtFbGcd omits the driver LUT->xMUX hop (P4); gcd_hw_conditional has no gcd
content (P4). Also, by my own grep: 12a/12b/12c modelled LUT arcs as
"rise 56 / fall 124", the corner misreading PROGRAM.md flags for shard B, so
their arbiter/C-element thresholds may be artefacts. Until the probes below
report, read the track-10 "per-node exact" and the track-12 thresholds in the
verdicts above with these caveats.
Launched 11 probes: aud (audit fixups in Lean/docs), 10m (OUTMUX + xMUX hop,
rerun all rows), 12d (12a/b/c and 10i at one consistent corner), 8s (prove
H_WALK), 8t (joint non-vacuity witness for gcd_hw_circuit_safe''), 8u
(circuit liveness O5), 8v (second kernel, token level), 10n (tcheck on
collatz/xorshift/ipow + how-to), 11f (whole-design bitstream import:
FF/CARRY4/MUXF7/F8), 8w (tcheck verdicts => capstone H_BUNDLE, O6), 10l2
(diagnose rule K, finish 10l).

### progress 11:46
Committed after my own build + check.sh audit:
- aud (2798 decls): audit rows answered in Lean. RingFair proves the
  N(N-1)/2 fair window; RingGen restates ring_three/k_tokens over the
  generated bd_c2n netlist (a flipped INIT now breaks the headline, Wip
  mutant); CheckerFixedFn: `win` is exact only when the witness may choose
  the cell functions (XOR counterexample), docs corrected; Rules: the rule-A
  band threshold is exactly tl <= 403 (iff; the journal's 402 was off by one),
  SLACK=0 stated; CheckerToy/Capstone docstrings corrected (corr needs a
  glitching wire; gcd_hw_conditional has no gcd content -- the gcd theorem is
  gcd_hw_circuit_safe''). Table: notes/C-aud-audit.md.
- 8w (506 decls): O6 mechanised as data (1212 Ops obligations, 4500 of 4572
  tcheck rows matched; H_MUXN_SEL(umux21) has no rule-E row although the
  hypothesis list says it does; C7, M3 and the cm stage-1 bus acc251 have no
  rule) and in Lean for the PHYSICAL channel (held_of_tx/held_of_cert under
  TxCover). Finding: the capstone's H_BUNDLE lives on zero-delay traces, so
  tcheck cannot discharge it directly; a physical -> zero-delay refinement is
  missing (launched 8x for it).
- 8v (817 decls): ipow's bdc graph computes b^e mod 2^32 on every schedule for
  all i32 inputs and is live without fairness; collatz conditional on C
  termination (unconditional for 1 <= n < 256). Importer generic; drift check
  covers 3 kernels; negative control caught. Token level only.
Launched 8x (physical refinement for the capstone) and 8y (ipow circuit-level
safety, generic capstone generator). Installed libtcl8.6 + boost libs (the
toolchain cache restore lacks them; yosys failed without libtcl).

### progress 12:44
Committed after my own build + check.sh audit (all core Lean, axioms
propext/Classical.choice/Quot.sound only):
- 8u (3591 decls): circuit liveness reduced, not proved. The 9 arbiter
  stages are never contested, so an uncontested-only settle bound suffices
  (gcd_hw_arb_settle; stall_* shows the uncontested bound alone is useless);
  generic ranking theorem rank_live (no fairness); gcd_hw_live holds under two
  OPEN network obligations, H_NO_DEADLOCK and H_FIRING_BOUND (8z on them).
- 8s (3497 decls): H_WALK proved for all a, b < 2^31. gcd_hw_circuit_safe3:
  every out0 latch is Nat.gcd a b under H_CELLS, H_BUNDLE, H_START_ONCE.
- 8s2 (3590 decls): the rig violates H_START_ONCE (re-offers start after
  every result). gcd_rig_first: under the rig's env gate model (H_ENV) the
  FIRST out0 result is gcd a b; reset level settled without a new hypothesis.
  Negative (proved): re-arming fails at every re-offer (invocations overlap at
  the out0/env handshake), so "every result" is open (8s3 on it).
- 8t (3740 decls): joint non-vacuity. One explicit run (a=12, b=18) satisfies
  H_CELLS, H_BUNDLE, H_START_ONCE, H_WALK together and latches 6 on out0.
  One input, one unit-delay schedule, zero-delay buses.
- 8y (3734 decls): ipow at circuit level, ipow_circuit_safe3 (same hypotheses;
  H_WALK proved), from bdc's own ipow graph; generator formal/tools/capnet
  reproduces the gcd files byte for byte.
Launched 8s3 (every rig result) and 8y2 (capstone parametric in a Kernel
structure; one-argument kernels; xorshift's steer case).
Still running: 10m, 12d, 10n, 11f, 10l2, 8x, 8z.

### progress 12:54
10n committed (tools/notes only): tcheck runs on collatz/xorshift/ipow (12
routes); no disagreement is a fixed-point prjxray failure; finding: the
project's rule A (tighten.cell_boundary) and tcheck's rules2.py time GND/VCC
tie-off routes as data -- a false path that sets the rule-A peak on every
route (0.9-4.2 ns too high) and is the whole cause of the only project-rule
violation seen (ipow s3 umuli1, -59 ps guarded). Safe-side error but it
over-sizes delay lines; for FOR-RESEARCH (shard A). tcheck fix queued until
10m releases the front end. How-to for a new kernel:
notes/C-howto-new-kernel.md.

### progress 13:01
8z committed (3948 decls). gcd_hw_live_final: for a, b < 2^31 the first out0
token closes within (1168(8 Lrun+23)+1)(H+1) ticks carrying gcd a b, under
H_CELLS, H_BUNDLE, H_START_ONCE, H_BOUNDED_DELAY' (all gates but start's LUT),
H_START_ENV, H_ARB_UNCONTESTED_BOUNDED and H_NO_DEADLOCK' (the one open
network obligation; 56 random-delay simulations never deadlocked -- evidence
only). Proved: every channel offers <= 4L+11 tokens (kernel-checked
15-round certificate), firing bound, H_WALK_ENDS. CORRECTION to 8u (committed
705257c): its gcd_hw_live is likely VACUOUS -- H_BOUNDED_DELAY on start's
source LUT plus H_START_ONCE forces start's ack never to fall
(start_never_closes, mechanised; the step to "out0 never closes" is argued),
and its H_FIRING_BOUND counted unconstrained traces, so it could not hold.
Use gcd_hw_live_final, not gcd_hw_live. No Lean witness yet that 8z's
hypothesis set is jointly satisfiable. Launching 8z2 (H_NO_DEADLOCK' +
witness).

## Session Thu Oct 29 07:22:22 UTC 2026

### progress 07:22
Took LOCK-C (previous lock 2026-10-27T13:01, stale). Previous session's running probes (10m, 12d, 10n-fix, 11f, 10l2, 8x, 8z2, 8s3, 8y2) never landed; checking for leftovers.

### progress 07:27
Lean 4.35.0 via setup.sh; its Mathlib from-source build stopped (shard C's
195-module closure imports no Mathlib; checked by walking imports). Targeted
`lake build` of every tracked Net/Timing/Gen module running. FPGA toolchain
restore (cloud/setup-toolchain.sh) running. Audit re-read: rows 24-27, 38, 39,
53, 60 answered last session (C-aud-audit.md, 8t joint witness = row 70
CONFIRMED); still open for C: OUTMUX hop in tcheck (rows 13, 49, 50),
RtFbGcd xMUX hop (row 54), hypotheses N12 wording (row 55). Lost last
session (never committed): 11f's tools/Lean (only its note survives), 10m,
12d, 10l2, 8x, 8z2, 8s3, 8y2.
Launched 12 probes: 10m (OUTMUX + tie-off false path in tcheck, rerun all
rows, compare with the auditor's xrc.py), 10f2 (RT_FB with the xMUX hop),
12d (12a/b/c/10i at one consistent corner), 8x (physical -> zero-delay
refinement so tcheck discharges H_BUNDLE), 8z2 (H_NO_DEADLOCK' + joint
witness for gcd_hw_live_final), 8s3 (every rig result), 8y2 (kernel-generic
capstone + a third kernel), 11f (rebuild whole-design bitstream import), 10l2
(rule K failures), 9d (ring: H_ONE_TOKEN from reset, timed lift), vk (one
verify.sh entry point with counterexample traces), aud2 (audit wording,
hypothesis list refresh).

### progress 07:38
aud2 committed (docs only): audit wording fixes in 9 shard-C notes, the
hypothesis list's §0 rebuilt against the Lean (47 names grepped), and the
verdict block above rewritten to say no more than the Lean. FPGA toolchain
restored from the cache branch; cells/verify/toolchain.sh ok, nextpnr sha256
9c732bc6303458df, yosys 0.62 runs. Lean module build at 114/163.

### progress 08:06
9d committed after my own check.sh (4 files, 885 decls, axioms standard only):
RingReset/RingResetCert/RingTimed/RingTimedPure; see the track-9 verdict.
Note for shard A: tools-A/snap.sh stages all of formal/lean/Wip except _snap[BC], so it
can commit shard C's Wip/C*/ files (in flux while probes run) and make a later C push
conflict. Suggest excluding '^formal/lean/Wip/(C|_snapC)'. C's snap-c.sh stages only
Wip/C* and Wip/_snapC.

### progress 09:22
12d committed (notes and tools only, no Lean claimed): see the track-12 verdict. Its
closed forms are tool fits on every row (0.1-0.2 ps), not theorems; z3 k-induction for the
FAST aperture stopped bounded at depth 50 under load.

### progress 09:23
8s3 committed after my own check.sh (3 files, 3718 decls, standard axioms): gcd_rig_all,
every rig result is gcd a b; see the track-8 verdict. Non-vacuity only via the quiet run.

### progress 09:28
8y2 committed after my own check.sh (19 files, 4795 decls, standard axioms), capnet/check.sh
OK (gcd, ipow byte-identical), dfimport/check.sh ok incl. xorshift. Launched O4 (bind the Ops
models to the generated cells: H_CELLS from LUT/wire hypotheses) and wit (witness runs for
gcd_rig_all with >= 2 invocations, xorshift, collatz). 12d, 8s3 committed above.

### progress 09:49
8z2 committed after my own check.sh (17 files, 4328 decls, standard axioms): see the
liveness lines of the track-8 verdict. Launched 8z3 (prove H_NO_DEADLOCK'').

### progress 09:54
8x committed after my own check.sh (4 files + witness chain, 4088 decls, standard axioms).
Launched 8x2 (relaxed Ops data fields so H_ZD_AGREE becomes trivial; classify the 376
underived channels).

### progress 10:15
10f2 committed after my own check.sh (15 RtFb files, 481 decls, standard axioms): see track 10.

### progress 10:33
10m committed (tools, results, notes; no Lean claimed; tcheck binary rebuilt, its 12 checker
theorems' axioms standard, 0 CERTBAD). Same 16 routes byte-identical. r10l rows regenerated
with the newer rule K (103 flips): that is 10l2's to interpret. 11f, O4, wit, 8z3 under my
checks.

### progress 10:36
Committed after my own check.sh: wit (8 files, 4697 decls), O4 (6 files, 4911), 8z3 (7
files, 4034); axioms standard. Launched 8z4. 11f's check running.

### progress 10:36
11f committed after my own check.sh (Basic + GcdD/All + FasmGcd; standard axioms): see
track 11. Routes re-made today byte-identical to the fixtures (nextpnr 9c732bc6303458df).

### progress 10:38
10l2 committed after my own check.sh (RuleK.lean, 528 decls). Launched 10o (H_CHAIN_SETTLED as
a timing row on real routes vs rule F) and 11g (whole-design Lean for seeds 2-4, second
kernel). RingCheck docstring now names H_ONLY_LINKS_STORE (audit C2 3c).

### progress 10:41
vk committed (tool + note, no Formal files; selftest --quick OK in my run).

### progress 11:10
8x2 committed after my own check.sh (6 files). vk committed. Launched vk2 (automatic
all-inputs token proofs), O4b (generated-cell binding for every kernel; prove
H_LEAF/REQ_PERSIST), 8x3 (drop H_SEND/H_RECV by a time-bounded protocol induction).

### progress 11:20
O4b committed after my own check.sh (7 files).

### progress 11:29
8x3 committed after my own check.sh (6 files, 4447 decls). Launched 8x4 (data fields derived
inside the capstone) and witgen (active run under H_GEN).

### progress 11:30
10o committed after my own check.sh (ChainSettle*, 197 decls); tool results committed, the
74 MB regenerable obligation files ignored.

### progress 11:31
8z4 committed after my own check.sh (2 files, 3069 decls); H_NO_DEADLOCK'' remains OPEN.
10o committed. Launched 10o2 (ChainSettle -> O4 bridge, Lean checker for chainck).

### progress 12:10
8x4 committed after my own check.sh (5 files, 5061 decls). Launched cap (phys5 instantiated
on route d's imported netlist and certified tcheck rows).

## Session Sat Oct 31 07:21 UTC 2026

### progress 07:21
Took LOCK-C (previous 2026-10-29T12:59, stale; no C session on 10-30). Probe "cap" (launched
12:10 on 10-29) never landed. setup.sh's whole-project `lake build` (Mathlib from source: cache
unreachable) stopped by me; shard C's modules are built by target (they import no Mathlib).
Audit read (passes 12-13). Open rows on C files, in order of weight:
- row 18 (P12a): `TxWin.count : ∀ k` forces infinitely many offers, so on every terminating run
  BCert = exempt and phys4/phys5_cls/_gen are vacuous on real gcd runs. CONFIRMED by me from
  the definition. Fixing now (index by the transactions that occur).
- row 19 (P12a e): "H_FN decided on 176/221" overstated -- fnOK returns true for `.wire` (43
  forks) and `.shift` (37 steerD) without consulting Formal.Gen; only 96 (87 latches + 9 data
  muxes, W=3 instances, bit pair pair[0].u assumed) are checked against generated cells, and
  H_FN is reduced to H_ZD_BITS + H_WIDTH (assumed). Accepted: the correct sentence is "96 of
  221 sampled channels are checked against Formal.Gen (W=3 only); 80 pass a constant-true
  check; H_FN rests on H_ZD_BITS + H_WIDTH".
- row 20 (P12a): "9 FASTFALL lines" miscount. Accepted: 11 distinct lines (19 line x model
  failures: 1 sdfband + 9 fastG + 9 slowG); by tcheck's own verdict (fastG AND slowG) those 11
  lines FAIL, rule F passes them. The C-10o note's table was already right.
- row 13 (P13): bdc_closed_ring_empty scope -- docstring now says closed bd_c2n rings from
  all-zero only; "every bdc ring" rests on emit.py emitting no `_set` cell (grep, not Lean).
- row 45: Ring.lean header already says N(N-1) / tight N(N-1)/2 in RingFair (fixed earlier).

### progress 07:36
TxWin repaired (row 18): `idle`/`count`/`win` now need a k-th offer (`HasOff`), last window
unbounded; `off_in_win`, `sampled_eq_zd`, `idle_until(T)` adapted, statements of every downstream
theorem unchanged; periodic witnesses wX/wXQ adapted. New `CapstoneRefineFinWit.fin_witness`:
a channel offered exactly twice, idle forever after tick 32, carries a tcheck DAG `BCert` (not
`exempt`) and gets Held + zero-delay samples. Building the 14 dependent modules.
Found three finished probes from 10-29 that never landed (only Wip/_snapC copies): 8z5
(H_NO_DEADLOCK'' narrowed to `NoBlock`; `spine_local`, `gcd_hw_no_rtz_loops`), vk2 (generated
all-inputs token proofs, incl. isprime) and 11g (bitstream import on gcd_hw seeds 2-4 and
xorshift seeds 1-4, rho a bijection). Re-claiming them after my own build/check:
- vk2: `tools/autoproof/ref/gcd_binary.c` was never committed (gen_claimed.sh failed). I
  reconstructed it from the test-point lines AutoGcd.lean quotes; with it gen_claimed.sh
  regenerates all ten Auto* files BYTE-IDENTICAL to the snapshot (AutoLib is hand-written).
- 11g: drift check needs prjxray-db; FPGA toolchain restore (cache branch) running.

### progress 07:50
Committed after my own `./check.sh` on 21 files (6801 declarations, axioms standard, OK):
- TxWin repair (audit row 18) + `CapstoneRefineFinWit.fin_witness` (finite channel, DAG BCert)
  + `CapstoneRefineOut0Wit.out0_dag_witness`: on C-8t's REAL gcd_hw run `chW`, out0 (offered
  once) carries a `BCert.dag` whose obligation netlist is hand-made (5 nodes, fixed delays, 3
  bus bits; NOT the routed netlist); from it alone out0 is Held and every in-transaction sample
  is 6 = gcd 12 18. The phys4/phys5 witnesses themselves still use exempt/ghost on every root.
- 8z5 claimed (CapstoneLiveNd5{Spine,Loop,}; Wip/C8z5/Neg.lean negative controls pass):
  H_NO_DEADLOCK'' <-> NoBlock; spine_local; gcd_hw_no_rtz_loops. H_NO_DEADLOCK'' stays OPEN.
- vk2 claimed (Auto*: generated all-inputs token-level theorems for gcd, ipow, collatz,
  xorshift, isprime and the equivalent gcd mutant; AutoLib hand-written once), with the
  reconstructed `tools/autoproof/ref/gcd_binary.c` (regeneration byte-identical).
- RingReset docstring scope (audit P13 row 13).
11g: fasm2lean3 `check.sh --no-lean` passes on all four gcd_hw seeds (bits = FASM, check3 0
fail on 10629-10633 instances each, no drift, negative controls caught); Lean build of
Gcd2-4 and Xorshift1-4 running (one module at a time).
Started H_COMPUTE_FN (open hypothesis: the yosys LUT/CARRY4 netlist of each bdc_fused unit
equals its MLIR op): survey of gcd_hw's 20 fused units from the synth JSON -- per output bit,
uori0/1 and ucmpi2/3 depend on <= 2 input bits; the adders/compares/selects/shifts on up to
64. Writing Formal/Net/Compute/Basic.lean (cell semantics on shard A's CARRY4/MUXF models,
support soundness, cut-point soundness, exhaustive local checks).

### progress 08:27
H_COMPUTE_FN started and partly discharged (notes/C-hcf-compute.md). Committed after my own
`./check.sh` (16 files, 1812 declarations, axioms standard, OK): Formal/Net/Compute/{Basic,Word,
Adder,EqZero,GcdBitwise,GcdAdd,GcdEqZero} + generated Formal/Gen/Compute/GcdD/* (extractor
tools/compute/extract.py, drift check tools/compute/gen.sh --check). Proved for EVERY input, on
the committed yosys synthesis of gcd_hw: uori0/uori1 = e0|e1, ucmpi2/ucmpi3 (1-bit compares),
ucmpi0/1/8/10 = (e0 == 0), uaddi0 = e0+e1 mod 2^32 (ripple adder with the CARRY4 carry-outs as
cut points). 9 of 20 units. Generic machinery: support/cut-point/cone soundness, exhaustive local
checks by kernel decide. Assumed: shard A's LUT/MUXF/CARRY4 Boolean models; NOT timing, glitches,
the link to the capstone's Join.dat. One kernel decide over all 32 adder bits needed 13 GB and
was OOM-killed under check.sh; split into one theorem per bit (1.3 GB, 211 s).

### progress 08:50
Committed after my own `./check.sh` (12 files, 1977 declarations, OK): the five arithmetic
shifts ushrsi0..4 compute `$signed(a) >>> 1` for every `a` when their `e1` port carries 1 (the
only value it carries in gcd_hw: a constant-1 token; the Ops join has `.lit 1`). The units are
general 32-bit barrel shifters; new `Fold.lean` propagates the fixed shift amount through LUT
cofactors and MUXF selects (`fold_sound`), so each output bit's folded support is <= 2 input bits.
NOT shown: other shift amounts. 14 of 20 units done. Signed compare (uori2/3/4, uselect0) proved
in my runs (`Slt.lean`: lexicographic CARRY4 chain, structural via `run_cell`); checking next.

### progress 09:10
More H_COMPUTE_FN, proved in my runs (check pending): signed compare (`Slt.lean`: lexicographic
CARRY4 chain; the chain is checked STRUCTURALLY through a new generic `run_cell`: a cell's
equation over the final net values in a duplicate-free, locally topological netlist) for uori2/3/4
(`((e2&e3)!=0) | slt(e0,e1)`) and uselect0 (`slt ? e0 : e1`); `Ripple.lean` (general ripple chains:
operands from any leaves, complements, carry-in) for uselect1 = `d = e0-e1; d > -1 ? d : 0-d` (the
abs-difference unit where the gcd_rig GLS located the board failure: its synthesized FUNCTION is
right for every input; the failure was a timing event, not addressed); ushli0 = `e0 << k` for every
`e0` and every k < 32 (32 fixed-k certificates through the constant folder, ~1 h of kernel time).
The four routed gcd_hw seeds have byte-identical yosys synthesis JSON (md5 e81e3f53...), so the unit
theorems hold for all four routes' logical netlist; 11f/11g carry it to the placed instances.
Kernel memory: one decide over 4096 assignments took 7.8 GB; split by assignment ranges
(`localOK_of_ranges`, 0.9 GB).

### progress 09:22
Answer to B (JOURNAL-B, "FOR SHARD A (lead) / C: apply both patches in one commit" -- the
Prelim deletion, B.patch + AC.patch, 14 of whose files are C's): C will not apply it, because a
single commit across A's, B's and C's files breaks the ownership rule for whichever shard makes
it. C CONSENTS to shard A (lead, owner of the project files) applying the C-file part of AC.patch
together with B.patch in one commit, provided check.sh stays green; C will re-verify its modules
the next session after it lands.

FOR SHARD A (out/gcd_hw_hypotheses.md, row H_COMPUTE_FN; text to use ONLY once this journal reports ushli0 and GcdJoin claimed):
"H_COMPUTE_FN | the yosys fused-unit netlists compute bdc's expressions | **A for the function**
(C-hcf: all 20 gcd_hw units proved for every input on the committed synthesis, identical on all
4 routed seeds; `GcdJoin.j2..j162`: each of the capstone's 20 join functions `jg e js` equals its
unit's function on bdc's port wiring; ranges: 32-bit tokens for uselect0, shift < 32 for ushli0,
shift = 1 for the ushrsi units as gcd_hw feeds them) | still assumed: H_MAP (which unit is which
join), the constant ports' values, primitive Boolean models | timing is H_COMPUTE_DELAY (rule A)".

### progress 09:35 (heading corrected from 09:50: commit 502da4fe is 09:35 UTC)
Committed after my own `./check.sh` (26 files, 2563 declarations, standard axioms, OK): H_COMPUTE_FN
for uori2/3/4 (signed compare + or), uselect0 (signed-compare mux), uselect1 (abs difference);
infrastructure Struct/Slt/Ripple and the reworked Word/Adder/Shift (re-checked with GcdAdd,
GcdBitwise, GcdEqZero, GcdShrsi0-4). 19 of gcd_hw's 20 units are now claimed (ushli0 for k < 32,
GcdJoin and the xorshift units are under check, not claimed).

### progress 09:41
Under my own `./check.sh` now (NOT claimed until a commit says so): ushli0 (Gen Ushli0, GcdShli0K0-3,
GcdShli0) + GcdJoin; xorshift (Gen Xs/*, Sgt, BitFn, XsUnits, XsFn, XsXor). Negative controls
(`Wip/Chcf/Neg.lean`: one-bit INIT mutations in uori0 and uaddi0 must make the certificate false)
are building. The 11g full check (tools/fasm2lean3/check.sh, every seed of gcd + xorshift) has
passed steps 0-2 (toolchain 9c732bc6303458df, 4 seeds, check3 0 fail, drift up to date, rhoinj
uncovered 0); its Lean step is still running.

### progress 09:42 -- xorshift H_COMPUTE_FN claimed
Committed after my own `./check.sh` (Gen/Compute/Xs/{Uaddi0,Ucmpi0,Ucmpi1,Uxori1,Uxori2}, Sgt,
BitFn, XsUnits, XsFn, XsXor: 10 files, 2115 declarations, standard axioms only, OK;
`KERNEL=xorshift tools/compute/gen.sh --check`: all 5 up to date). Proved for every input, on the
xorshift soak top's yosys synthesis (identical on its 4 seeds): uaddi0 = `e0 + 1`, ucmpi0 = signed
`e0 > e1`, ucmpi1 = signed `e0 < e1`, uxori2 = `e0 ^ (e0 << 5)`, uxori1 =
`t ^ (t >> 17)` with `t = e0 ^ (e0 << 13)`. This is a second kernel on the same machinery. It does NOT show
timing, H_MAP for xorshift, or anything about the board.

### progress 09:46 -- negative controls
`Wip/Chcf/Neg.lean` ran with no output and rc 0. Both kernel-decided controls hold: changing bit 3's OR
LUT in uori0 to AND (INIT 14 -> 8) makes `BitLocal` false, and changing bit 5's XOR LUT in uaddi0 to
XNOR (INIT 6 -> 9) makes the bit-5 slice check false. So these certificate checks can fail. The
controls cover two units, not every certificate kind.

### progress 10:36 -- H_COMPUTE_FN: all 20 gcd_hw units + GcdJoin claimed
Committed after my own `./check.sh`:
- Gen/Compute/GcdD/Ushli0 and GcdShli0K0-3 compiled under check.sh (chk7, ~13 min per K file).
- GcdShli0 and GcdJoin passed check.sh: 5879 declarations, standard axioms only, OK. That audit
  covers K0-3 transitively.
- `tools/compute/gen.sh --check`: 20 of 20 generated units up to date.

New claims: ushli0 computes `e0 << k` for every e0 and every k < 32. `GcdJoin.j2..j162`: each of
the capstone network's 20 join functions `jg e js` equals the function of the unit with that
operation, on bdc's port wiring (32-bit tokens for uselect0, shift < 32 for ushli0).
`joins_listed`: the capstone has exactly those 20 joins.

The FOR SHARD A text at 09:22 is now usable. Still NOT shown: H_MAP (which physical unit
implements which join), the values on the constant ports, timing (H_COMPUTE_DELAY), and anything
about the board.

### progress 11:08 -- 11g claimed (bitstream import, all routes, both kernels)
`tools/fasm2lean3/check.sh` (full, with Lean) passed with rc 0:
- gcd_hw d,2,3,4: toolchain 9c732bc6303458df, --freq 100, fasm_audit PASS; bits = FASM; check3 0 fail.
- Drift: up to date. rhoinj: uncovered 0.
- Lean: 5910 declarations, standard axioms only.
- Negative controls in the bits (INIT, pips, FF init, CLKINV): each is caught by check3, and Lean
  proves `checkAll = false` for each.

`kcheck.sh xorshift` passed with rc 0 (seeds 1-4, 2942 declarations).

The generated files are now committed: FasmDesign/{Gcd2,Gcd3,Gcd4,Xorshift1-4}, FasmGcd2-4, FasmRho*,
FasmXorshift*. Claim, as in notes/C-11g-seeds.md: on every routed seed of gcd_hw and xorshift,
every physical instance decoded from the bitstream read-back computes its yosys cell under rho,
and rho is a bijection on nets outside route-throughs. Not shown: routing delays, the primitive
models themselves, and ipow (DSP48E1 refused).

### progress 11:10 -- audit P14 row 10 accepted
Audit P14 row 10 (CapstoneRefineOut0Wit OVERSTATED) is right. The certificate over oNet is a
relabelling: the data bits are 6 by construction, and BCert.dag ranges over arbitrary netlists.
The file's title and the out0_dag_witness docstring now say so (check.sh OK, 4346 declarations,
statements unchanged), and so does notes/C-8x4-refine.md. Commit d63d5221's message omitted it and
cannot be changed. The FEASIBILITY sentence "phys4/phys5 were vacuous" is shard A's file: FOR SHARD A,
P12a found only phys5_cls/_gen vacuous (audit P14 row 10).

### progress 11:10 -- state at hand-off
Everything this session produced is committed and pushed, and the tree is clean:
- H_COMPUTE_FN for all 20 gcd_hw units, GcdJoin, and the 5 xorshift units.
- The negative controls.
- 11g on all routes of gcd_hw and xorshift.
- Audit rows 18 and P14-10.

NEXT for C: H_NO_DEADLOCK'' via the confluence route (notes/C-8z5-nodeadlock.md, analysis
2026-10-31). First obligations:
(a) persistence of every excitation in the interleaving model except the mux-input acknowledge,
    with the depth-one exception from mux_out_not_mux;
(b) one constructive schedule per input that closes out0;
(c) the timed-to-interleaving bridge (8z4 serial, its hex premise for gcd_hw).
None of these is started.

## Session Sun Nov  1 07:20:55 UTC 2026 (shard C; session_01HC49FxWJ9vtZZwXVrasyvJ)
First C session under THE goal (owner, 2026-10-31): one theorem about the gcd_hw bitstream.
C owns the generic checker theorem: obligation completeness, loops, composition, refinement.

### progress 07:27 -- COUNTEREXAMPLE (simulation stage): pipelined pairs reorder or deadlock
Audit re-read (passes 15-18): no open REFUTED/OVERSTATED row on C files; row 20 (GcdJoin not
linked into the capstone) stands as an open link. Lock was 20 h old; taken.
THE goal requires a pipelined environment. Tested it first, since a refutation is worth most.
**Result, plainly:** gcd_hw does NOT return the k-th gcd for the k-th pair when pairs are
pipelined. A pair that skips the first loop overtakes one that iterates. With finite storage
(handshake network), two threads in the loops can deadlock instead.
- Token level, toksim.py (untrusted): values always right, order wrong, e.g. (2^20,2^20),(3,5) ->
  out0 [1, 2^20].
- Handshake network (CapstoneNet cell models, unit delay, gcd_rig's fork env made free-running),
  hwsim.py (untrusted): pair 2 accepted at tick 141; (2^20,2^20),(3,5) -> [1, 2^20]; (3,5),(3,5)
  and (64,64),(3,5) deadlock (no out0).
Not Lean yet; unit delay is one assignment, not the band. Details: notes/C-pipe-cex.md.
Next: Lean certificate of the token-level reorder, then the handshake-level witness.

### progress 07:43 -- token-level reordering CLAIMED (Lean); counterexample retargeted to the rig's vectors
Shard A's Spec.lean (Wip) puts the boundary at the kernel ports with ONE shared request, and the target
feeds the kernel from gcd_rig's 16-vector table. So the counterexample now uses the table's vectors:
- **Claimed** (`lean -DautoImplicit=false` on the core-only chain KahnLTS..GcdHw..PipeGcd, rc 0, 95 s;
  `#print axioms`: propext, Classical.choice, Quot.sound; no sorry/native_decide; drift check
  `tools/pipe/gen_reorder.py --check` ok): `Formal.Net.PipeGcd.gcd_hw_pipelined_reorders`.
  **Plainly:** in the token graph bdc emits for gcd_hw, with vector 9 (a=65536, b=4096) queued before
  vector 4 (1, 1) and two start tokens, there is a complete run (528 firings, each re-executed by the
  kernel) ending with out0 = [1, 4096]. It does NOT show the hardware takes this schedule.
  check.sh was not run: Mathlib is still building from source (setup.sh: cache unreachable); the
  lead's check.sh needs `lake build`. FOR SHARD A: please add Formal/Net/PipeGcd.lean to check.sh's run.
- Handshake model (hwsim, unit delay), target vectors: 9 then 4 -> out0 [1, 4096] (reorder);
  9 twice -> DEADLOCK (quiescent at 264, no out0); 15 then 5 -> DEADLOCK.
- FOR SHARD A: Spec.lean section 7 says the target "would not hold two pairs" because start is acknowledged
  only at completion (gcd_rig.v's header). The capstone's handshake model says otherwise: pair 1's input
  handshake completes at tick ~140, its result at 271+. See FOR-RESEARCH.md section C1 (added by C).

### progress 07:45 -- deadlock explained; two more Lean witnesses building
- Generated-netlist model (hwsimgen, per-LUT chains), unit delay and random per-node delays 1..4: vector 9 then 4
  reorders in every run; vector 9 twice deadlocks in every run. Which failure a pair sequence hits can depend on
  timing (vector 15 then 5: deadlock in CapNet, reorder here); that one occurs did not, in any run tried.
- Deadlock cause: both invocations' tokens in the first loop; the loop has bdc's 3 storage stages (one token);
  C-9's Ring.k_tokens: k tokens need 2k+1. Plainly: gcd_hw's loops have room for one invocation at a time.
- Building (core-only chain, 68 modules, direct `lean`; Mathlib still compiling for setup.sh):
  PipeWit (handshake-level reorder, rig vectors 9 then 4) and PipeDead (handshake-level deadlock, vector 9
  twice, with the one-tick step property on every non-source gate, so nothing is merely slow, and QuietNS at
  tick 265). Neither is claimed until it compiles.

### progress 07:52 -- GLS of the TARGET route: pipelined env loses results (not yet gated)
iverilog 12 installed (apt). Research's cells/gls generators (read-only) on formal/target's routed JSON + SDF
(SDF md5 = README's), baked delays, my testbench formal/tools/pipe/gls/tb_pipe.v (env_c forced: pair 2 offered
as soon as pair 1's input handshake completes). nextpnr-SDF GLS, not the fid GLS.
- 9 then 4: first result = 1 (pair 2's gcd; rig mism=0 vs vector 4), pair 1's never comes (100 us quiet). Same with
  a 20 ns data setup.
- 9 then 9: pair 2 never accepted, no result at all.
- 2 then 4: pair 1's result, then pair 2's never comes.
- sequential control (9 then 4): both results, correct, in order.
Pending before this is claimed: the SDF acceptance gate (gate.vvp, ANNOTATE_DONE and no SDF warnings) and the
sequential controls 9/9 and 2/4. Table: notes/C-pipe-cex.md.

### progress 07:54 -- PipeWit CLAIMED: the capstone's cell models admit reordered results
`lean -DautoImplicit=false` over the core-only import chain (direct lean, scratch oleans; Mathlib still building),
rc 0; `#print axioms gcd_hw_pipelined_reorder_handshake`: propext, Classical.choice, Quot.sound; no sorry/
native_decide/axiom in PipeWit{,Data}; `tools/pipe/gen_pipewit.py --check` ok.
**Plainly:** there is a run of the 465-channel CapNet network in which every non-source operator meets its cell model
(CellR, the capstone's H_CELLS), every channel is bundled (Held), the sources obey the four-phase protocol (requests
low at reset) and offer gcd_rig's vector 9 at tick 0 and vector 4 at tick 142, and out0 offers gcd 1 1 = 1 FIRST
(tick 272) and gcd 65536 4096 = 4096 second (tick 1044). Unit delays: one delay assignment, not the band; CapNet
is built from bdc's graph and link plan, not decoded from the bitstream.

### progress 07:56 -- PipeDead CLAIMED: deadlock under a pipelined env, every gate fast
Same check as PipeWit (direct lean -DautoImplicit=false, rc 0, 55 s; axioms propext, Classical.choice,
Quot.sound; no sorry/native_decide/axiom; `gen_deadwit.py --check` ok).
**Plainly:** `Formal.Net.CapNet.PipeDead.gcd_hw_pipelined_deadlock`: a run of the CapNet network in which every
non-source operator meets its cell model with explicit internal traces (CellI), every channel is bundled, EVERY gate
of every non-source operator (arbiter grants included) has the one-tick step property (BndG 1: nothing is merely
slow), the sources obey four-phase and offer gcd_rig's vector 9 twice (requests rise at 0 and 142), out0's request
is low at every tick (neither result is ever offered), and no non-source gate is excited at tick 265 (QuietNS).
So without H_START_ONCE the capstone's liveness fails outright: this is what H_START_ONCE is hiding. Unit delays,
CapNet (bdc's graph), not the band or the bitstream; the target-route GLS (notes/C-pipe-cex.md) agrees.

### progress 08:04 -- target GLS gated; owner notified; H_COMPUTE_FN units identical in the target
- Target GLS acceptance gate: ANNOTATE_DONE, 0 SDF warnings/errors. Sequential controls (9/9, 2/4, 9/4) all correct.
  So, on the nextpnr-SDF GLS of the target route: pipelined offers lose results in every run tried, and 9 then 4
  delivers pair 2's gcd first. Probe: the wedge is at the first loop's header muxes (umux0-2).
- Token level: offering pair k+1 once out0 holds k results: 400/400 random rig-vector sequences correct.
- The 20 fused compute units in the TARGET's yosys synthesis (formal/target/gcd_hw_03e82630.json.xz) extract
  (tools/compute/extract.py) to Lean byte-identical to the committed Gen/Compute/GcdD/*: so C's H_COMPUTE_FN
  theorems (all 20 units, every input, ranges as stated) are about the target's synthesis too. Not shown: that the
  target's BITS implement that synthesis (11g's import needs prjxray-db, not installed here; next step).

### progress 08:06 -- 11g on THE TARGET: Python half passes; Lean half building
Toolchain restored from the project's cache (cloud/toolchain-cache.sh fetch, key d7ce266cff0c8e1e, branch
toolchain-cache/d7ce266cff0c8e1e) for prjxray-db. On formal/target/gcd_hw_03e82630:
- fasm2lean3 on the READ-BACK FASM (fromBit) and on nextpnr's FASM: the same physical netlist (8925 LUT6_2, 306 FDRE,
  20 FDSE, 343 MUXF8, 857 MUXF7, 59 CARRY4, 14 buf, BSCAN; 0 floating pins).
- gen3 with the target's yosys netlist: 10629 instances, logical 9623 (9622 matched; the 9623rd is the unread MUXF7
  as on every seed), physical 10525 (0 unused), 1139 route-through outputs; check3 (Python mirror of Inst.check):
  0 fail; rhoinj: uncovered 0.
- Difference from the --freq 100 seeds: 5627 of 5645 library-cell LUTs bound to generated cells (seeds: 5645).
  To look at: which 18, and why (the target has BDC_SELECT_PADS / v4 placement).
- Lean: Formal/Net/FasmDesign/GcdT/* (generated), FasmRhoT* (generated), FasmGcdT.lean (FasmGcd2 with the target's
  counts) building one module at a time (direct lean). Not claimed until it compiles.
Meaning, once the Lean passes: every physical instance decoded from the target's bits computes its yosys cell under
rho, rho bijective off route-throughs; with H_COMPUTE_FN (20 units, byte-identical in the target's synthesis) the
compute units of the target's bits compute bdc's functions (still under H_MAP and the Boolean primitive models).

### progress 08:13 -- SpecSettle CLAIMED: interval timing (settle and hold) in the frozen Spec's semantics
`Formal/Timing/SpecSettle.lean` (lean -DautoImplicit=false, rc 0; axioms propext, Classical.choice, Quot.sound;
imports Formal.Target.Spec and Mathlib.Data.Rat.Floor). **Plainly:** for Spec's GateOK (per-pin monotone reads,
every read delay admissible under H_DELAY(g, κ), output = INIT at the reads): every admissible read delay of an arc
lies in [⌈fmin/g⌉, ⌈smax·g⌉] (any corner, any κ); if a gate's inputs hold values on windows [S_i, U_i], its output
holds INIT[addr] on [max(start, S_i + dmax_i), min(U_i + dmin_i)] (`gate_stable`); and a Boolean certificate
checker `certOK` (one STA pass over a gate list in topological order: inputs external or earlier, the local rule per
gate) is sound for every `Behaves` behaviour of a netlist (`cert_sound_net`). Controls (Wip/CSpec/SettleNeg.lean,
rc 0): the tight certificate of a one-gate buffer is accepted; one ps too early, one ps too late, the wrong value, or
an unknown input are each rejected. NOT covered: feedback (loop nodes cannot be certified by this rule), which
windows a design needs (the obligation generator), anything about the env.
This is the generic piece C owes THE goal for bundling/settling obligations, stated on Spec directly (C's older
Timing/Checker is sound only for its own run semantics).

### progress 08:18 -- tcheck on the target route (running); rule D screen understood
- formal/setup.sh: my broad `pkill -f "lake build"` (meant for a tcheck build) also killed setup's Mathlib build at
  ~07:58 (setup then reported done, rc 0, but Mathlib is incomplete). Restarted setup.sh (idempotent); it is
  building Mathlib again. No committed file was affected. Process note: kill by PID, never by pattern.
- tcheck (C-10, compiled, proved sound over its own semantics) rebuilt; toy and cert self-tests ok; sync.sh copied
  a docstring-only drift of Formal/Timing/Semantics.lean (from the lead's Prelim deletion).
- Work tree build/tree_T = `git archive 1a97b739 cells bdc` (the research commit the target was built from) + the
  target's SDF (md5 6f8b99e6, = README), routed JSON, FASM (md5 1a3909f6, = README), .bit.
- research's own rules on the target route (this tree's verify/*.py on the target SDF): rule E (skew.py) 118 select
  gates, 0 violated; rule J (arb_fork.py) every arbiter ok; tighten.py: rule A passes every comparator, F 29 lines ok
  (worst +1343 ps); its "38 boundaries do not meet" are all rule D, which the script itself calls a one-sided SCREEN
  superseded by rule E. So nothing new from the project's rules.
- Next: extract every rule's obligations with prjxray arcs (extract.py --rules2 AEFJWR --cert) and run tcheck on them:
  the band verdicts for the TARGET (the earlier C-10 runs were on --freq 100 routes, not these bytes).

### progress 08:23 -- tcheck on THE TARGET: every A/E/F/J row passes at both prjxray corners
extract.py --rules2 AEFJWR --cert on the target route (tree_T: research 1a97b739 cells + the target's SDF/FASM, md5s =
README): 184 controllers, 2735 obligations, 80102 arcs with prjxray numbers, 9872 falling back to the SDF band, 15
unordered prjxray records hulled. tcheck (proved-sound checker, toy/cert self-tests ok): 15738 instances checked.
Against research's own rules (compare2.py): A 50/50 agree PASS; E 116+115 agree, 2+3 disagree; F 28+28 agree, 1+1;
J 14/14/18 agree, 4+4 J0/Jp disagree. **Every disagreement is "band only"**: the rows pass at the fast and at the slow
prjxray corner (each corner consistent, no guard) and fail only with the 0.772/1.155 guard band applied: umux13 uj0/uj1
and umux19 uj1 (rule E; worst guarded -426 ps), ucmpi8.udly (F, -498), the arbiters of control_merge2/4/9 (J; worst
merge9 uarb1#1: fast +179, slow +480, guarded -770/-1237). Tables: tools/tcheck/results/target/compare5_T.tsv.
Meaning for NetCorrectSeq: at g = 1 the checked bundling/flush/arbiter-fork rows hold at a consistent corner; they set a
ceiling on the provable guard g (merge9's J row has +179 ps at the fast corner). Not shown: that these rows are all the
obligations (completeness), mixed corners within κ, W/R rows (not compared), anything in Lean about the target.

### progress 08:29 -- tcheck C-10k rows on the target: same pattern
Fd 29, X 81, Xi 32, Z 9 rows: 0 failures at the sdf, fast and slow corners (minima +1061 fast / +1735 slow for Fd,
+1502 / +2308 for X); X fails only with the guard band (fastG 2, slowG 9; worst umux18.uxa/uya -1373 ps slowG).
Tables: tools/tcheck/results/target/{r10k_rows,summary10k}_T.* (run10k.sh had overwritten the committed 4-seed tables;
restored).

### progress 08:36 -- 11g on THE TARGET CLAIMED (Lean): every instance decoded from the target's bits computes its yosys cell
Formal/Net/FasmDesign/GcdT/{Rho,C000..C042,All}, FasmGcdT, FasmRhoT{Data,Inv,Mark,Occ,} (generated by
tools/fasm2lean3/target.sh; FasmGcdT = FasmGcd2 with the target's counts): built one module at a time with direct
lean -DautoImplicit=false (scratch oleans), all rc 0; axioms of gcd_hw_target_netlist, gcd_hw_target_cells_init,
FasmRhoT.rho_bij: propext, Quot.sound; no sorry/native_decide.
**Plainly:** for formal/target/gcd_hw_03e82630.bit, read back by prjxray: every one of the 10629 physical instances is
Inst.Sound for the renaming rho (it computes its yosys cell of the target build's netlist), the two output pads map to
the logical OBUF inputs, 9622 instances carry a logical cell, the 5627 bound library-cell LUTs have the kind and INIT
of C's generated library cell, and rho is a bijection off the 1139 route-through outputs. NOT covered: timing,
glitches; the FASM-to-site decoding (trusted Python, H_SITE_DECODE; shard A's decoder is the Lean route); the 18
arbiter LUTs (ustate/ugrant of 9 bd_arbiters) whose INITs come from research's newer bd_arb.v, absent from C's
generated library (still checked against the yosys netlist by the Inst.Sound half).

### progress 08:37 -- tcheck C-10l rows on the target: same pattern
K 42, Xc 81, Xic 32, Xm 81 rows: 0 failures at sdf/fast/slow; with the shared-prefix credit (Xc) the X guard-band
failures drop from 11 to 1 (umux11.uxa slowG -313); Xm (max-node) 0 failures even guarded. So across every tcheck row
family on the target route (A, E, F, J, Fd, X, Xi, Z, K, Xc, Xic, Xm): no failure at a consistent unguarded prjxray
corner. Tables: tools/tcheck/results/target/*_T.*

### progress 09:24 -- arbiter-core INITs in the target: evidence only (Lean attempt abandoned)
The 18 target LUTs not bound to C's generated library are the 9 bd_arbiters' ustate/ugrant LUT6_2s. grep of the
generated GcdT data (the same data the Lean import checks): all 9 ustate carry INIT 0xFFF0FFB2ACACACAC and all 9 ugrant
0x0C0C0C0CA0A0A0A0 (research 1a97b739's held-arbiter bd_arb.v; the constants shard B's arbiter files use). A kernel
statement of this (decide over instance names with String.endsWith) was OOM-killed over all instances and still
unfinished after 30 min per-chunk; abandoned, NOT claimed. The right fix is a generated library for the target's
cells/rtl (C's tools/gen on 1a97b739's rtl), so gen3 binds these LUTs like the others; not started.

## Session Mon Nov  2 07:27 UTC 2026 (shard C; session_01HC49FxF4NXW5x4MW5wphev)
Lock-C was 22 h old (yesterday's C session, last journal entry 09:24); taken. Read PROGRAM (THE goal, owner
decisions 2026-11-01), STATUS, A/B journal tails, audit REPORT. Audit rows on C files: no new REFUTED/OVERSTATED
since yesterday; decision 3's `adm_le_dmax` fix in SpecSettle was done by A (JOURNAL 17:27). setup.sh running
(Mathlib cache unreachable; building from source). Plan: S5 (C) first, since it needs only core Lean.

### progress 07:44 -- S5 token level CLAIMED: gcd_hw under a sequential env, any number of pairs, every schedule
`Formal/Net/GcdHwSeq.lean` (core Lean only; `check.sh Formal/Net/GcdHwSeq.lean` OK; `#print axioms gcd_hw_seq`:
propext, Classical.choice, Quot.sound; no sorry/native_decide).
**Problem.** C-8i/8k's `gcd_hw_graph_computes_gcd` covers one pair offered to an empty graph. THE goal's
`NetCorrectSeq` needs any number of pairs under `SeqEnv`, where pair k+1 may enter while pair k's leftovers are
still inside (token simulation, 3000 runs: at the moment out0 gets its token, up to 15 internal channels still
hold tokens, e.g. 5/8/15/17/22/29 on the a=0 / b=0 fast paths, 177-197, 233/239/241, and 251 to sink15).
**Statement** (`Formal.Net.GcdHw.Seq.gcd_hw_seq`): bdc's gcd_hw graph (the 158 imported rules) closed with a
sequential environment written as 6 more rules (take: out0 -> result log + one credit; offer: credit + next (a, b)
from two input lists -> a, b, start; one credit at the start). For every list of pairs with a, b < 2^31, on every
schedule and control_merge arbitration: (1) some run completes with log = ps.map gcd; (2) EVERY complete run ends
with log exactly ps.map gcd; (3) at every point of every run the log is a prefix of ps.map gcd (no wrong, missing
or reordered result); (4) every partial run can be completed (no deadlock); (5) one bound on every run's length.
**How.** A token count over the spine minus control_merge12's sink branch, plus cm12's index, out0, the credit and
the offer path, stays <= 1 in every reachable state (new generic `closedQ`: `closed_of_check` extended to a token
moving from a control_merge's index through a mux to its output); that is what the existing diamond lemma needs,
so all complete runs end in one state (KahnLTS.terminal_unique); the run that drains each pair before taking its
result is built from the single-invocation theorem with a frame lemma (`run_ext`: tokens on channels no rule reads
-- end tokens, remaining inputs, the log -- do not change a run).
**Not covered.** Token level (unbounded FIFOs, H_SOURCE_ETERNAL as in C-8i); no circuit, delays or bitstream. It
is the token-level half of S5; S4 (the decoded circuit refines this graph under SeqEnv) is still open. The env may
offer a, b and start separately (more permissive than the target's shared request), never before the previous
result was taken. With two initial credits (a pipelined env) the invariant fails at the start, consistent with
PipeWit/PipeDead and the V9V4 refutation.
FOR SHARD A (STATUS.md, S5 row): token-level part proved by `Formal.Net.GcdHw.Seq.gcd_hw_seq`; open: its
connection to the circuit (S4).

### progress 07:52 -- THE target's netlist is cyclic beyond its storage self-loops (structure, untrusted Python)
`formal/tools/loops/loops.py` on `DecodedPS.net` (rebuilt from the committed Lean data by B's lean2json.py: 187,258
nodes, 186,873 gates). A pin is a self-feedback pin if following its node back through copy gates (k = 1, INIT 0b10)
reaches the gate's own output: 4,597 such pins on 4,597 gates (chains of 4-13 copy gates, i.e. the routing pips of
each C-element/latch loop). Cut all of them, and also the 42,391 pins outside their gate's INIT support: the node
graph still has 129 cyclic SCCs: 128 of 73-77 nodes, each one bit of a loop variable going round its loop
(`ulink_n_falseResult_51` stages 0..2 latch pair[k] -> `umux10.udat.pair[k]`, i.e. bdc's 3-stage loop link and its
header mux), and one SCC of 86,684 nodes with 8,653 LUTs (link latches, controllers, delay chains, compute units,
muxes: control and data of the loops together). Meaning for the checker (S2): a static cut of the storage loops
does not leave a DAG, so SpecSettle's topological certificate (`certOK`) cannot cover the kernel by cutting loops;
the obligations have to be event-based (per handshake phase, latch-enable windows), as rules A/E/F/J are. Next:
collapse the copy chains in Lean (pin -> source node with summed corner window), so cell-level reasoning works on
~12k logic gates instead of 187k nodes.

### progress 07:56 -- SpecChain CLAIMED: routing chains collapse in the Spec's semantics
`Formal/Timing/SpecChain.lean` (imports SpecSettle; `check.sh Formal/Timing/SpecChain.lean` OK; `#print axioms
collapse_net`: propext, Classical.choice, Quot.sound).
**Problem.** In `DecodedPS.net` every pip/wire/site hop is a copy gate, so a LUT pin reaches its driving LUT through
4-13 copy gates, each with its own read time and admissible delay. Can cell-level reasoning treat "pin i reads node s
with one delay"? **Proved** (Spec's GateOK, Sane (0 ≤ κ ≤ 1, 0 < g), one corner c ∈ [0,1]): `chain_read`: along a copy
chain (`chainOK`, a Bool check) there is one non-decreasing read time F with x v t = x u (F t) and t - F t a sum of one
Adm-admissible delay per chain arc at the same corner (`SumAdm`); `collapse`/`collapse_net`: a gate whose pins read
through such chains (gates of the netlist) satisfies `CGateOK`, GateOK's shape with sources for pin nodes and summed
delays (pin arc first), from `g.start + Σ (chainStart + dmax)` on. Glitches, transport and pulse swallowing of the
chain are kept (it is the composition of the reads). **Not shown:** the chains of the target (data + a check on
DecodedPS.net: next); one net with several readers is collapsed per reader (they may see it at different delays).

### progress 08:27 -- CViewPS CLAIMED: the collapsed view of THE target's circuit (S4 groundwork)
Files: generic `Formal/Timing/SpecChainM.lean` (chains given by a copy map: `follow`, `CmSound`,
`collapse_net_m`), `Formal/Timing/ChunkCM.lean` (copy map as per-chunk perfect binary trees of depth 12,
`cmSound_of_chunks`, `collapse_chunks`, `logicView_complete`), and `Formal/Net/CViewPS/` (Base, 75 T chunks,
CM, 75 V chunks, All: GENERATED by `formal/tools/cview/gen_lean.py` from the committed NetPS data via B's
lean2json; Collapsed.lean by hand). `lake build Formal.Net.CViewPS.Collapsed` OK (1132 jobs; each T or V chunk is
one ~40 s `decide +kernel`); `#print axioms` of `collapsed` and `view_complete`: propext, Classical.choice,
Quot.sound; scan.py clean.
**Plainly** (`Formal.Net.CViewPS.collapsed`): for every p with 0 ≤ κ ≤ 1, 0 < g and every behaviour x of THE
theorem's circuit (`Behaves p (circuit DecodedPS.net DecodedPS.boundary) x`), at x's one corner c, each of the
circuit's 19,878 non-copy gates (LUT5/6, MUXF, CARRY4 pieces, constants) satisfies `CGateOK`: pin i reads the node
at the far end of its copy chain (the circuit's own copy map, kernel-checked against the gate list) at a
non-decreasing time whose delay is a sum of one Adm-admissible delay per arc (pin arc + each pip/wire/hop), and the
output is INIT at those reads. `view_complete`: every non-copy gate of the circuit is in the view. 96,149 pins,
chains of 0-26 copy gates. **Not shown:** anything about what the gates compute together; before `cStart` nothing
(power-up). Python side-check (untrusted): the kernel's backward cone in the collapsed graph (from the acks,
out0/pend req and data) has 13,669 nodes and reads no undriven node except the 68 env nodes; the 158 pins that
read a floating node with the INIT depending on it are outside the cone (agrees with A's undriven check).
FOR SHARD B: storage nodes become CGateOK gates whose feedback pin has src = own output (4,597 of them), so
fb_stays/fb_forced/fb_switch can be restated on CGateOK with the feedback delay = loop sum (SumAdm) and applied to
every storage node of THE target at once.

### progress 08:28 -- SpecLoop CLAIMED: settle and storage-hold rules on the collapsed relation
`Formal/Timing/SpecLoop.lean` (`check.sh` OK, standard axioms). For CGateOK gates (every logic gate of THE target,
by CViewPS), sane parameters, c ∈ [0,1], ordered arcs: `sumAdm_bounds` (a composite delay lies in [Σdmin, Σdmax]);
`cgate_stable` (inputs stable on windows ⇒ output INIT[v] on the shifted intersection); `cgate_hold` (a storage
node whose feedback pin's source is its own output, loop delay ≥ 1 ps, other pins confirming q on their windows,
output q on the primed segment [T0 - Σdmax_loop, T0): output stays q on [T0, E]). Strong induction on time.
**Not shown:** how a forcing episode primes the loop (B's fb_switch condition on the collapsed loop), the
per-node obligations on THE target.
### progress 08:29 -- SpecLoop: cgate_force and cgate_switch added (check.sh OK)
`cgate_force`: pins forcing q whatever the feedback ⇒ output q on the window (no loop assumption). `cgate_switch`:
forced on [T1, T0) with T0 - T1 ≥ Σdmax of the routed loop, then confirmed on [T0, E] ⇒ output q on [T1, E]. The side
condition "forcing lasts at least the loop's Σdmax" is the per-storage-node obligation (B's fb_switch condition,
now on the collapsed loops of every storage node of THE target, via CViewPS).

### progress 08:45 -- HuffmanPS CLAIMED: every loop of THE target's circuit passes through a storage node
Generic `Formal/Timing/Huffman.lean` (`rankChunkOK`, `ranked_of_chunks`); generated `Formal/Net/CViewPS/{R,K}*.lean`,
`RK`, `Ranks` (formal/tools/cview/gen_rank.py); `HuffmanPS.lean` by hand. `lake build Formal.Net.CViewPS.HuffmanPS` OK
(1286 jobs); `#print axioms comb_ranked`: propext, Classical.choice, Quot.sound; scan.py clean.
**Plainly** (`Formal.Net.CViewPS.comb_ranked`): in the collapsed view of THE target's circuit, call a logic gate a
storage node if one of its pins reads its own output through the routing (4,597: C-elements, latches, arbiter
states) and the others combinational (15,281). There is a rank on nodes that strictly increases along every
pin-to-source link between combinational gates (same pin data as `collapsed`). So every cycle passes through a
storage node: THE target is 4,597 storage LUTs plus acyclic logic (depth ≤ 96, no INIT-support pruning needed). With
SpecLoop this localizes the loop part of S2: obligations only at storage nodes (`cgate_switch`: each forcing
episode ≥ its routed loop's Σdmax) and along acyclic paths (`cgate_stable` windows). It answers, for this target,
THE goal's "feedback loops handled inside the proof, not cut by hand": the cut set is derived and checked, not chosen.
**Not shown:** that the obligations hold; no behaviour beyond structure.

### progress 08:51 -- static switch-obligation table for THE target's 4,597 storage nodes (untrusted Python)
`formal/tools/cview/loopobl.py` on DecodedPS (collapsed view; tables tools/cview/out/obl{0,0.5,1}.tsv, summary
obl_summary.txt). Per storage node s and corner c (g = 1): L = its routed loop at the slow end of the κ=0 window
(Σ lerp(fmax,smax,c) over the feedback pin's composite arcs); R = the fastest path (Σ lerp(fmin,smin,c), support pins
only) from s's output back to the source of an episode-ending pin of s (for latch-like nodes the enable, i.e. a
pin one value of which makes the feedback irrelevant; for C-element-like nodes every non-feedback input; reset/env
pins excluded). An episode that ends only as a consequence of s's own switching lasts ≥ R; `cgate_switch` needs ≥ L;
κ* = (R-L)/(R+L) is where (1-κ)R = (1+κ)L. Minimum κ* per kind (corners 0/0.5/1): link ctl C-elements 0.142/0.152/
0.157 (worst ulink_n143 stage[2] ctl: L 386, R 514 ps at c=0); mux join uj 0.157/0.165/0.168; arbiter state 0.234/
0.262/0.274; mux uxa/uya ≥ 0.24; control_merge g ≥ 0.296; latches (enable return) ≥ 0.446; 1,673 latch nodes have no
return path to their enable at all. **Meaning:** a static, structural sufficient margin: no own-consequence episode
of any storage node violates the clean-switch condition for κ ≤ 0.14 at g = 1, any corner -- IF the shortest
structural path bounds the causal one (not proved; it is a lower bound only if every return goes along some path of
the collapsed graph, which the Spec semantics should give by a causality lemma, not yet written). B's simulated
episodes give ≈ 0.49 for the tightest node (actual paths are longer than the structural minimum). **Not covered:**
episodes ended by independent events (other inputs racing), the data-hold race at latch d pins (a bundling
obligation), g > 1.
FOR SHARD B: this is a static lower bound to compare with kstar; the structural worst nodes are ulink_n143 stage[2]
ctl and umux7.uj1, not the ones your simulation found tightest.

### progress 08:52 -- SpecLoop: causality (cgate_cause) and fundamental-mode settling (settle_ranked), check.sh OK
`cgate_cause`: if a collapsed gate's output differs at t1 ≤ t2 (from its start on), some pin's source toggles at a
time in (t1 - Σdmax, t2 - Σdmin] of that pin's composite arcs (no spontaneous change; the basis for reading path
delays as causal bounds). `settle_ranked`: for ranked combinational nodes over roots (every pin source a root or a
lower-ranked comb node, composite Σdmax ≤ M, starts ≤ A): if every root is quiet on [A, B], every comb node w is
quiet on [A + (ρ w + 1)·M, B]. Instantiated with CViewPS (comb_ranked: roots = the 4,597 storage nodes + env/undriven
nodes, depth ≤ 96) this says: once THE target's storage and environment nodes stop moving, the whole circuit is quiet
97·M later. **Not yet done:** the instantiation as one Lean statement on DecodedPS (needs gluing comb_ranked's
node-indexed data to collapsed's view list, and M for a concrete p); storage-node dynamics.

### progress 08:54 -- settle_PS CLAIMED: THE target settles in fundamental mode
`Formal/Net/CViewPS/Settle.lean` (lake build OK, 1288 jobs; `#print axioms settle_PS`: propext, Classical.choice,
Quot.sound; scan.py clean). **Plainly:** in every behaviour of THE theorem's circuit (Sane p), at its corner: for any
M bounding every combinational pin's composite Σdmax and any A past every combinational gate's start, if every
non-combinational node that feeds a combinational gate (the 4,597 storage nodes, env and undriven nodes) is constant
on [A, B], then every combinational node w is constant on [A + (ρ w + 1)·M, B] (ρ the kernel-checked rank; ≤ 96 per
the generator, not stated in Lean). From collapsed + comb_ranked + settle_ranked. **Not shown:** that the storage
nodes/env are ever quiet (dynamics), M for a concrete p.

### progress 08:56 -- quiet_PS CLAIMED: THE target never starts moving by itself
`SpecLoop.quiet_forever` (generic) and `Formal/Net/CViewPS/Quiet.lean` (`quiet_PS`; lake build OK; standard axioms;
scan clean). **Plainly:** in every behaviour of THE theorem's circuit (Sane p), at its corner, for M with every
logic pin's composite delay in [1, M] ps and every logic gate's start ≤ T - M: if the env/undriven nodes feeding
logic are constant from T - M on and every logic node (all 19,878, storage included) is constant on [T - M, T], every
logic node is constant for ever. Proof: the first toggle after T would need (cgate_cause) a source toggle strictly
earlier inside [T - M, ...]. This is the "stays idle" half of THE theorem's last clause. **Caveat:** the hypothesis
1 ≤ Σdmin per composite pin must hold for the p used (a composite arc with all fmin = 0 makes the statement vacuous
for that p); **not shown:** that the circuit becomes quiet after the last pair.
### progress 08:57 -- quiet_PS hypothesis fixed to fit the data
Checked on the data: 368 composite pins have Σfmin = 0 (CARRY4 pieces reading the CONST0 gate, k = 0, zero-delay
tie), so "every pin ≥ 1 ps" would have made quiet_PS vacuous at every p. quiet_forever/quiet_PS now require ≥ 1 ps
only for pins whose source is a non-constant logic node (a zero-delay pin from a root or a k = 0 gate is handled:
a k = 0 gate never toggles, by cgate_cause). Rebuilt; standard axioms; check.sh OK.

### progress 09:00 -- SpecLoop.light_cone (causality bound), check.sh OK
For collapsed logic nodes over roots, a potential φ with φ w ≤ φ(src w i) + Σdmin for every pin (Σdmin ≥ 1 unless the
source is a root or a k = 0 constant), Σdmax ≤ M, starts ≤ A - M: if nothing toggles in (A - M, A] and no root r
toggles in (A, φ r), then no logic node w toggles in (A, φ w). Plainly: a change cannot reach a node faster than the
fastest delay path from its cause. With φ = T0 + shortest path from a storage node s (and every other root quiet), it
bounds how soon s's own switch can withdraw its forcing: the causal half of the per-storage-node switch obligation
(B's cfb_switch / my cgate_switch; B wrote the CGateOK feedback lemmas in parallel, SpecFbChain, 08:06: same content,
no conflict). **Not shown:** the isolation hypothesis (in a running circuit other inputs move concurrently; that
needs the handshake-level argument, S4), and a kernel-checked φ for THE target (needs a concrete p: Σdmin is computed
from p).

### progress 09:01 -- NodeN143: one real storage node through the collapsed view (check.sh OK)
`Formal/Net/CViewPS/NodeN143.lean`: node 151633 (SLICE_X40Y49.A6, nextpnr name ulink_n143 stage[2] ctl, the storage
node with the smallest static margin) is a logic node and a storage node of THE target's circuit; its pin 1 reads its
own output through its routing (`srcPS 151633 1 = 151633`), and the loop's composite arcs are 7 (pin + 6 copy gates)
with Σ smax = 959 ps. So cgate_switch / B's cfb_switch apply to it with that loop; its obligation is "every forcing
episode lasts ≥ 959 ps" at the slow bound (g = 1, κ = 0). Each check is a ~1 s decide on the collapsed data, so any
node B or A needs can be bridged the same way.

### progress 09:02 -- SpecLoop.settle_value: settled values are the zero-delay values (check.sh OK)
As settle_ranked, plus any assignment v consistent with the combinational logic (v w = INIT_w at v of its sources) and
equal to the roots on [A, B]: every comb node w equals v w on [A + (ρ w + 1)·M, B]. With storage + env nodes as roots,
v is the zero-delay evaluation of THE target's acyclic logic (HuffmanPS) from the storage state, so each storage
node's next-state can be read off an abstract Huffman machine whenever the state has been quiet long enough. Next
toward S4: the abstract machine's state graph per handshake episode, with the per-node switch obligations.

### progress 09:14 -- THE target as an abstract Huffman machine: SI fails, "latches first" works (simulation, untrusted)
`formal/tools/cview/hufsim.py`: state = the 4,597 storage nodes; all other logic evaluated with zero delay (what
settle_value says the timed circuit settles to); one step fires one excited storage node; env = A's sim.py sequential
protocol. (1) **Plain speed-independent semantics (any excited storage node may fire next) is WRONG for THE target**:
gcd(12,18) returned 2, other seeds deadlock or return 0; 53 persistence violations (ctl C-elements, forks, cm12 arbiter,
latches). Expected for bundled data: with zero-delay logic the matched delay lines vanish, so control can outrun its
data latches. (2) **Relative timing "every excited data latch fires before any other storage node"** (4,185 latch-like
nodes: an enable pin one value of which makes the feedback irrelevant; 412 others: C-elements, arbiters, forks):
11 sequential pairs (0,0 7,0 0,5 1,1 17,5 0x42F,0x1CE 0x10E,0xC0 0x10000,0x1000 0x24,0x3C 0x400,0x300 0x18697,0x18697)
x 6 random control orders: every result = gcd, in order; every run the SAME 13,743 firings; ZERO persistence
violations. Also 12,18 48,18 x 4 orders: correct, 0 violations. Logs: tools/cview/out/hufsim_{seq,si}.txt.
**Meaning (if it holds in general):** THE target's control network (412 storage nodes) is speed-independent and
determinate given (a) zero-delay settling of the logic between storage nodes and (b) data latches settling before
control moves. So the timed proof splits exactly into: the SI control network (a determinacy/diamond argument like
KahnLTS, on reachable states), plus two timing obligation families: (a) settle windows (settle_value) between
storage switches, (b) bundling (latch before control), plus the per-node switch obligations (cgate_switch). **Not
shown:** any of this in Lean; exhaustive orders (random sampling only); pipelined env (refuted anyway).

### progress 09:21 -- tcheck on THE target's route (gcd_ps): every row passes at both consistent corners; binding row umux21 rule A, κ* ≈ 0.080
Tree: `git archive` research bfa659b4 (BQ#4's commit) cells+bdc + the target's SDF (md5 cbdbea3a), routed JSON, FASM
(md5 2dbf962d) = README's; prjxray-db from the toolchain cache (d7ce266cff0c8e1e). extract.py --rules2 AEFJWR --cert:
184 controllers, 2505 obligations, 74,876 arcs with prjxray numbers, 10,515 SDF fallback. tcheck (C-10, compiled,
proved sound over its own run semantics; toy and cert self-tests ok): 15,012 instances. Summary
tools/tcheck/results/target/summary5_PS.txt, rows t5_PS.out.xz.
- At the fast and the slow prjxray corner (each consistent, κ = 0, g = 1): **every row of every family passes**
  (A 89, E 322, E0 596, F 29, H 158, I 75, J 54, R 409, W 150).
- Failures only with the guard band (fastG/slowG: rule A umux21 and ushli0, 8 E0 select rows, F cm12.udly, J0/Jp of
  cm9/cm11 arbiters) and ONE row under the corner-mixing SDF band: **rule A, umux21's bundled data** (req ≥ 4282 vs
  data ≤ 3648 ps at the fast corner, 10151 vs 8180 at the slow one).
- Read as THE theorem's (g, κ) frontier (sums scale linearly in Adm's window): this row holds iff (1-κ)·R(c)/g ≥
  (1+κ)·D(c)·g; at g = 1 κ* = 634/7930 = **0.080** at corner 0 (0.108 at corner 1); at κ = 0, g* = √(4282/3648) ≈ 1.083.
  That is far tighter than the storage-node races (B: ≈ 0.42 simulated; my static bound 0.142). **Caveat:** rule A
  is a sufficient condition (research found it pessimistic on gcd_ps: unsized routes pass the full stack), so this
  bounds what a proof THROUGH rule A can certify, it is not a counterexample; and tcheck's semantics is its own, not
  Spec's (bridging tcheck to SpecSettle/SpecLoop windows is open).

### progress 09:22 -- tcheck κ* per row on THE target: binding row is rule F at ucontrol_merge12.udly, κ* ≈ 0.038
tools/tcheck/results/target/kappa_rows_PS.txt: for every row, from its fast- and slow-corner instance (req_min,
data_max), κ* = (req - data)/(req + data) (sums scale linearly in Adm's window, so the row holds at corner c, g = 1
iff κ ≤ κ*). Lowest: **F (delay-line flush) ucontrol_merge12.udly n=24: 0.047 fast / 0.038 slow** (flush 2679 ps vs
the next rise of its source ≥ 2890 ps at the slow corner); A umux21 bundled 0.080 (umux21 is gcd_hw's OUTPUT mux, it
drives out0: Spec's Correct reads out0 data only from Δo after its request, so this row is absorbed by the env's Δo
and is not an obligation of THE theorem as stated); then E0 select rows from 0.161 (umux14.uj1), J arbiter forks from
0.175 (cm9 uarb1), A ushli0 0.181. Correction to the 09:21 entry: the binding row is F cm12.udly, not A umux21.
**Meaning:** a proof that discharges its obligations through tcheck's rules certifies at most κ ≈ 0.038 at g = 1
(at κ = 0: g ≤ √(2890/2679) ≈ 1.039). Rules are sufficient conditions; whether violating F at cm12 actually breaks
gcd_ps is untested (a GLS/simb adversary on that delay line would say).

### progress 09:24 -- the binding tcheck row (F, cm12.udly) is not tight: adversarial simulation correct up to κ = 0.6
B's simb.py (A's simulator + per-gate window ends) on DecodedPS, sequential env (--datachange broad), corner 1,
posmap: ucontrol_merge12.udly's 24 stage LUTs and their routing (378 gates) at the SLOW end of the κ-widened window,
every other gate at the FAST end (so the line flushes as late and its source re-rises as early as Adm allows).
Pairs 12,18 48,18 17,5 0x42F,0x1CE: results [6, 6, 1, 21] correct at κ = 0, 0.06, 0.12, 0.3, 0.6 (tmax 20 µs; a
first κ = 0 run with the default 5 µs horizon stopped before the 4th result, not a failure). So rule F's 0.038 at
that line is a sufficient-condition artefact for this adversary; THE theorem's real κ margin is not set by it. The
storage-node races (B: ≈ 0.42-0.5 simulated) remain the tightest real behaviour found. One adversary, 4 pairs:
evidence, not proof.

### progress 09:25 -- reset structure of THE target's storage nodes (untrusted Python, collapsed view)
Of the 4,597 storage nodes: 4,185 have no reset pin, exactly the latch-like set of hufsim (data latches; Spec allows
any power-up state and a transport loop could carry a power-up pulse, but Correct's idle clause names only req/ack
nodes, and a latch's loop is overwritten when it is first enabled); 403 read the reset with rst = 1 forcing their
output (C-elements, mux joins, forks, arbiter C-elements); 9 read the reset but are not forced by it alone (the 9
bd_arbiter ustate LUTs, B's ArbClean territory). So no control storage node is left unreset: checked, no finding.

### progress 09:33 -- reset_state CLAIMED: reset puts 403 control storage nodes of THE target in their reset state
`SpecLoop`: `Forces` (a Bool check that one pin value forces an INIT), `addr_testBit`, `cgate_force_pin` (that pin's
source holding b ⇒ output q on the shifted window, whatever the other pins and the feedback read). `CViewPS/ResetData`
(generated list, 403 entries) and `Reset.lean`: `resetList_ok` (kernel: each entry is a logic node of the circuit,
its pin's source is the reset node 186905, and that pin at 1 forces the INIT to the listed value) and
`reset_state`: in every behaviour of THE theorem's circuit (Sane p), at its corner, if reset is high on [0, R), each
listed node equals its reset value at every t with startPS ≤ t, Σdmax(reset pin) ≤ t ≤ R - 1 + Σdmin(reset pin).
lake build OK (1291 jobs), standard axioms, scan clean. **Not covered:** the 4,185 data latches (no reset) and the
9 arbiter states (reset + other inputs); that R exceeds those start times is Env's R, a parameter.

### progress 09:37 -- boundary_reset CLAIMED: THE target's handshake outputs start low
`Formal/Net/CViewPS/BoundaryReset{Data,}.lean` (data generated, kernel-checked: 30-node combinational cone of b.ack
and out0.req with zero-delay values, every cone value = INIT at its sources, every source in the cone with a smaller
global rank or one of 5 roots; the roots are reset-forced storage nodes of resetList with the same values).
`boundary_reset`: in every behaviour of THE theorem's circuit (Sane p), at its corner, with reset high on [0, R),
for any M bounding the cone's composite pin delays, A past the cone's starts and the roots' starts and reset-pin
Σdmax, and B ≤ R - 1: b.ack (node 104695) is low on [A + 8M, B] and out0.req (160957) on [A + 19M, B]. a.ack and
start.ack are themselves reset-forced storage nodes (low by reset_state). Python (untrusted) agrees: all four 0 under
reset. lake build OK, standard axioms, scan clean. This is the initial-state half of Correct's CircIn/CircOut for
the circuit's outputs (given R large enough); **not shown:** pend's request (shared with the input request, an env
node) needs nothing; anything after reset.

### progress 10:04 -- island_PS CLAIMED: THE target stays idle when nothing is offered, whatever its data latches hold
Generic `Formal/Timing/Island.lean` (check.sh OK): `ForcesP` (some pins at given values force the INIT whatever the
others read), `forcesP_sound`, `settle_partial` (ranked settling with partial forcing), `island_forever` (if every
member of a self-confirming island holds its value for M ps and the env members hold theirs, all hold for ever).
Instance `Formal/Net/CViewPS/Island{Data,Defs,Chk0..7,PS}.lean` (data from tools/cview/idlex.py: a ternary
fixpoint with every data latch and arbiter state X, then the island grown back from the four outputs). lake build OK
(1305 jobs; the one-decide version peaked at ~14 GB and was killed, so the check is split in 8 chunks);
`#print axioms island_PS`: propext, Classical.choice, Quot.sound; scan clean.
**Plainly** (`island_PS`): in every behaviour of THE theorem's circuit (Sane p), at its corner: if reset is high on
[0, R), the shared input request (186985) and pend.ack (104477) are low at all times, every island member starts
and every storage member's reset arrives by A, member pin delays are in [1, M] on forcing pins and ≤ M on all pins,
and A + 87·M ≤ R - 1, then all 414 island members are low from R - 1 - M on, for ever: in particular a.ack, b.ack,
start.ack and out0.req. Kernel-checked per member: logic node; forcing pins' sources are members or the two env
nodes; those pins at 0 force the INIT to 0 whatever the other pins (data latches, arbiter states) read; comb members'
member sources have smaller rank (≤ 85); the 94 storage members are reset-forced to 0. Next: Correct for n = some 0.

### progress 10:06 -- correct_n0 CLAIMED: THE theorem's conclusion Spec.Correct on the decoded target, for n = some 0
`Formal/Net/CViewPS/Idle0.lean` (lake build OK, 1306 jobs; `#print axioms correct_n0`: propext, Classical.choice,
Quot.sound; scan clean). **Statement** (`Formal.Net.CViewPS.correct_n0`): for every p with 0 ≤ κ ≤ 1, 0 < g, and R, su,
Δo, M, A such that every island member's start and every storage member's reset arrival is ≤ A, every island member
pin's composite Σdmax ≤ M, every forcing pin's Σdmin ≥ 1 and A + 87·M + 1 ≤ R: for every x, va, vb,
`Behaves p (circuit DecodedPS.net DecodedPS.boundary) x → Env x DecodedPS.boundary R su Δo (some 0) va vb →
Correct x DecodedPS.boundary R Δo (some 0) va vb`. That is THE theorem (NetCorrectSeq's conclusion) for the case
"no pair is ever offered", WITHOUT H_ARB and without SeqEnv, for every delay assignment in Adm.
**Plainly:** if the PS never offers a pair, the decoded gcd_ps circuit keeps a.ack, b.ack, start.ack and out0.req
low from the end of reset for ever, whatever its 4,185 data latches and 9 arbiter states power up with; so every
CircIn/CircOut clause, the data clause (vacuous) and the idle clause hold. **Non-vacuity on the data (Python):** at
g = 1, κ = 0 the forcing pins' composite fast delays are ≥ 114 ps, M = 3,881 ps works, A ≈ 15.6 ns, so the hypotheses
hold for a reset of R ≥ ~353 ns (the 87·M settle bound is loose). The hypotheses on p are not yet discharged in Lean
for a concrete p (a decide over the 414 members' arcs). **Not shown:** any n ≥ 1, i.e. the computing part.
This replaces nothing in STATUS's list (the allowed hypotheses here are H_DECODE via net, H_DELAY via Behaves, H_PRIM,
H_ENV; for n = 0 no derived hypothesis remains), but it is the first Lean theorem of THE statement's shape.

### progress 10:45 -- correct_n0_p1 CLAIMED: zero pairs at g = 1, κ = 0, only the reset length remains
`Formal/Net/CViewPS/{P1Defs,P1Chk0..7,Idle0P1}.lean` (lake build OK; standard axioms; scan clean). At p1 = (g = 1, κ = 0)
dmax = smax, dmin = fmin and Gate.start = max smax (`dmax_p1`, `dmin_p1`, `start_p1`), so the island's delay
hypotheses become Nat facts, kernel-checked one theorem per island entry (414; a one-decide-per-chunk version peaked
at ~14 GB and was killed, per-entry ~3 GB): starts ≤ A1 = 15,600 ps, every member pin's composite smax sum ≤ M1 =
3,881 ps, every forcing pin's composite fmin sum ≥ 1, storage members' reset-pin smax sums ≤ A1.
**Statement** (`Formal.Net.CViewPS.correct_n0_p1`): for every R ≥ A1 + 87·M1 + 1 = 353,248 ps and every su, Δo, x, va, vb:
`Behaves p1 (circuit DecodedPS.net DecodedPS.boundary) x → Env x DecodedPS.boundary R su Δo (some 0) va vb →
Correct x DecodedPS.boundary R Δo (some 0) va vb`. Plainly: with every arc in its corner window (any one corner, no
scatter, no guard), a reset of at least ~353 ns, and no pair offered, the decoded gcd_ps circuit satisfies THE
theorem's conclusion. Hypotheses: H_DECODE (that net is the bits), H_DELAY at (1, 0), H_PRIM, H_ENV; no H_ARB, no
SeqEnv. **Not shown:** n ≥ 1; κ > 0 or g > 1 (the same proof works with other bounds; not instantiated).

### progress 10:45 -- summary of this session so far (for A's STATUS.md and the owner)
Lean-checked (standard axioms), all on branch claude/formal:
- S5 token level: `GcdHw.Seq.gcd_hw_seq` (any number of pairs, sequential env, every schedule; audit CONFIRMED T13).
- THE target's structure: `CViewPS.collapsed`/`view_complete` (19,878 logic gates read their sources through
  checked copy chains, composite delay = sum of Adm delays), `comb_ranked` (every loop passes through one of 4,597
  storage LUTs; audit recount CONFIRMED T15).
- Generic timing/causality on the Spec semantics: SpecChain/SpecChainM/ChunkCM, SpecLoop (cgate_stable/hold/force/
  switch, cgate_cause, light_cone, settle_ranked, settle_value, quiet_forever, cgate_force_pin), Island
  (ForcesP, settle_partial, island_forever).
- On THE target: `settle_PS`, `quiet_PS`, `reset_state` (403 storage nodes), `boundary_reset`, `island_PS`, and
  **`correct_n0` / `correct_n0_p1`: Spec.Correct for n = some 0** (no H_ARB, no SeqEnv; at g = 1, κ = 0 for any
  reset ≥ 353,248 ps).
Untrusted evidence: tcheck on THE target's route (all rows pass at both corners; sufficient-rule κ* ≈ 0.038, not
tight in an adversarial simulation up to κ = 0.6); Huffman-machine simulation (plain SI wrong, "latches first"
determinate and correct); static storage-switch table (κ* ≥ 0.142).
STATUS suggestion (A owns the file): S5 token level done; for NetCorrectSeq the n = 0 case is proved; S2's loop part
is localized to storage nodes (comb_ranked + SpecLoop); S4/S6 for n ≥ 1 open.

### progress 10:46 -- after each pair the control returns to the reset idle state, up to 2 arbiter-site nodes (simulation)
hufsim (latches first), pairs 12,18 48,18 17,5 0,0, 2 orders: at every quiescent point between pairs, the 412
non-latch storage nodes equal their post-reset idle values except SLICE_X39Y21.C6 and SLICE_X39Y24.A6 (arbiter sites
in B's table: an arbiter remembers its last grant). The idle island of island_PS treats arbiter states as unknown,
so (if this holds in general) the same island keeps the circuit idle between pairs: the n = 0 argument is the
"between pairs" step of a multi-pair proof. Side note: with the env acting between every firing, one persistence
violation at SLICE_X3Y22.D6 (next to start.ack) and run lengths 3947/3949: an interface-order effect to look at.
- The persistence violation at SLICE_X3Y22.D6 is `bridge_i.ufork` (gcd_ps wrapper, outside udut): the 3-input
  C-element joining a.ack, b.ack, start.ack (+ rst, feedback) into the PS-side acknowledge. Spec's env sits at the
  kernel ports and may lower the shared request as soon as all three kernel acks are high, before this join has
  fired; the real AXI side waits for the join. It drives only toward the PS (env side), so Correct (stated at the
  kernel ports) is unaffected; but it means H_ENV at the kernel ports is NOT what the board's harness does: the board
  waits one C-element longer (stricter), so the theorem's env covers the board's. No finding against the theorem.

### progress 10:49 -- correct_n0_all CLAIMED: zero pairs, for every g > 0 and 0 ≤ κ < 1
`Formal/Net/CViewPS/Idle0All.lean` (lake build OK, standard axioms, scan clean). With C = ⌈(1+κ)·g⌉: every upper
delay bound scales by at most C (`dmax_le`, `start_le`, `sumMax_le`, `chainStart_le`, `cStart_le`; `rat_ceil_eq`
bridges core's Rat.ceil in Gate.start and Mathlib's ⌈⌉), and every forcing pin keeps a fast delay ≥ 1 ps while κ < 1
(`dmin_pos`, `sumMin_pos`). **Statement** (`correct_n0_all`): for every p with Sane p and κ < 1, and every reset
R ≥ C·A1 + 87·C·M1 + 1 (A1 = 15,600, M1 = 3,881 ps), Behaves p (circuit DecodedPS.net DecodedPS.boundary) x → Env ...
(some 0) ... → Correct ... (some 0) .... **Meaning:** for zero pairs THE theorem's (g, κ) frontier is all of κ < 1, g > 0,
given a reset of about C × 353 ns. (κ = 1 lets a pin's lower window reach 0 ps; the island argument needs ≥ 1 ps.)

### progress 10:55 -- check.sh over all 18 hand-written Lean files of this session: OK (2,948 declarations audited)
Caveat for the zero-pair theorems: they are implications from `Behaves p (circuit DecodedPS.net DecodedPS.boundary) x`;
their non-vacuity needs some behaviour of that netlist to exist (simulations produce them; no Lean witness for the
gcd_ps netlist yet; A's Lean witnesses are for the previous target).

### progress 11:30 -- witness_n0 CLAIMED: the zero-pair theorems are not vacuous (a Lean witness behaviour of THE target)
`Formal/Net/CViewPS/{WitBase,E000..E074,Enc,W000..W074,Wit0}.lean` (lake build OK, 1469 jobs; standard axioms; scan clean).
Generic `WitBase`: a behaviour in which every node switches at most once (`sig1` codes), every pin read at its
FAST_MIN; `gateW` checks a gate's equation at its start and at each breakpoint; `gateOK_of_gateW` (via `lastBp_spec`):
that finite check gives Spec.GateOK p1 0 for all time. Data (tools/cview/witn0.py + gen_wit0.py, untrusted): a power-up
state consistent with every circuit gate under reset (62,788 nodes high, found by relaxation), reset released at
400,000 ps, transport simulation at FAST_MIN: 3,604 nodes switch once, all settled 3.4 ns later; every one of the
circuit's gates kernel-checked per 2,500-gate chunk (~1-4 min, ~5 GB each).
**Statements:** `witness_n0 su Δo va vb : ∃ x, Behaves p1 (circuit DecodedPS.net DecodedPS.boundary) x ∧
Env x DecodedPS.boundary 400000 su Δo (some 0) va vb` and `witness_n0_correct`: Correct holds of it (from
correct_n0_p1). So the hypotheses of correct_n0_p1 are jointly satisfiable on the decoded gcd_ps netlist: the
zero-pair result is not vacuous. This closes the 10:4x caveat.

### progress 11:31 -- summary update
Audit (claude/audit e07f8832) CONFIRMED correct_n0 / correct_n0_p1 / correct_n0_all, boundary_reset, HuffmanPS and
gcd_hw_seq, with "non-vacuity open" for the zero-pair chain; witness_n0 (11:30) answers it. THE statement on THE
target now has: n = 0 proved for every g > 0, κ < 1 (reset ≥ ⌈(1+κ)g⌉·353 ns) and shown non-vacuous at (1, 0).
Next for C: a multi-transition witness (a computing run, n = 1, with ArbOK and SeqEnv) would show NetCorrectSeq's
hypotheses satisfiable for n ≥ 1; the proof for n ≥ 1 needs the S4 composition (notes/C-route-S4.md).

### progress 11:32 -- groundwork for an n = 1 witness (untrusted)
`formal/tools/cview/witn1.py`: transport simulation of THE target's circuit at FAST_MIN with a sequential env for one
pair (data from t = 0, request at R + 1 ns, falls when all three acks are high, out0.ack and pend.ack follow their
requests after Δo = 3 ns): result 6 = gcd(12, 18); 97,926 transitions on 39,051 nodes, at most 7 per node, done by
785 ns. A Lean witness for n = 1 (Behaves ∧ Env (some 1) ∧ SeqEnv, plus ArbOK T for a stated T) needs: WitBase
generalized to transition lists (same lastBp argument), ~100k data numbers in chunk trees, and proofs of the Env/SeqEnv
clauses over piecewise-constant boundary signals. Not started in Lean.

### progress 12:12 -- Wit1 CLAIMED: a Lean-checked gate-level run of THE target computing gcd(12, 18)
`Formal/Net/CViewPS/{WitBaseL,L000..L074,EncL,X000..X074,Wit1}.lean` (lake build OK, 1622 jobs; standard axioms; scan
clean). `WitBaseL`: the single-transition witness check generalized to transition lists (`sigL`, `gateWL`,
`gateOK_of_gateWL`). Data: tools/cview/witn1.py (transport run at FAST_MIN; power-up consistent under reset; operand
buses 12 and 18; reset released at 400 ns; request raised at 401 ns, lowered when all three input acks are high;
out0.ack and pend.ack follow their requests 3 ns later) and gen_wit1.py: 97,926 transitions on 39,051 nodes (≤ 7 per
node), every circuit gate kernel-checked at every breakpoint (75 chunks, ≤ 6.7 GB each).
**Statements:** `behaves_w1 : Behaves p1 (circuit DecodedPS.net DecodedPS.boundary) xW1`; `w1_result`: in xW1,
out0.req rises at 771,456 ps, out0.ack at 774,456 ps, and the out0 data bus at 774,455 ps is Nat.gcd 12 18. Plainly:
one concrete behaviour of the decoded bitstream's circuit, satisfying every gate relation of THE theorem at g = 1,
κ = 0, computes gcd(12, 18) = 6. This is a single run (a Lean-checked GLS), NOT a theorem about all runs; the
Env/SeqEnv/ArbOK clauses for it are not proved (next: they would show NetCorrectSeq's hypotheses satisfiable for n = 1).

### progress 12:16 -- w1_all_hyps CLAIMED: all of NetCorrectSeq's hypotheses are satisfiable for one pair on THE target
`Formal/Net/CViewPS/Wit1Env.lean` (lake build OK; standard axioms; scan clean). For the Lean-checked run xW1 (12, 18):
`w1_all_hyps su T (hT : 785472 ≤ T)`: Behaves p1 (circuit DecodedPS.net DecodedPS.boundary) xW1 ∧ ArbOK T arbs xW1 ∧
Env xW1 DecodedPS.boundary 400000 su 3000 (some 1) (fun _ => 12) (fun _ => 18) ∧ SeqEnv xW1 DecodedPS.boundary 400000.
The Env/SeqEnv clauses are proved from the pulse shapes of the 8 boundary signals (pls, pls_change, rises_pulse);
ArbOK because the 9 arbiter states are constant after the run's last transition (so only for T ≥ 785,472 ps: a weak T;
a witness for the meaningful T ≥ the state-LUT delay would need the arbiter traces checked against their inputs).
**Meaning:** THE statement (NetCorrectSeq) is not vacuous for n = 1 at (g, κ) = (1, 0), R = 400 ns, Δo = 3 ns, T ≥ 785
ns: there is a behaviour of the decoded bitstream's circuit meeting every hypothesis, and in it out0 carries gcd(12, 18)
= 6 (w1_result). Caveat: with Δo = 3000 equal to the run's ack delay, Correct's data clause has an empty sampling
window in this run (ack rises exactly Δo after the request), so this witness does not exercise that clause.

### progress 12:17 -- end-of-afternoon summary (shard C, 2026-11-02)
Lean, standard axioms, all pushed: S5 token level (gcd_hw_seq); THE target's collapsed view, loop structure, settle/
quiet/reset/boundary-reset theorems; Spec.Correct for n = 0 for every g > 0, κ < 1 (correct_n0_all) with a Lean witness
(witness_n0); a Lean-checked gate-level run computing gcd(12, 18) on the decoded bitstream (behaves_w1, w1_result) that
meets every hypothesis of NetCorrectSeq for n = 1 (w1_all_hyps, T ≥ 785 ns). Open: NetCorrectSeq for n ≥ 1 (the cell-level
composition S4, with the per-storage-node switch obligations and bundling windows; see notes/C-route-S4.md).
### progress 12:18 -- w1_arbOK: the one-pair witness meets H_ARB(T) for every T ≥ 220 ps
`w1_arbOK` / `w1_all_hyps'` (Wit1Env.lean; standard axioms; scan clean): every arbiter-state toggle in the run comes at
most 219 ps after a toggle of one of its state LUT's other inputs (kernel-checked, with the transition lists strictly
increasing so each listed time is a real toggle: `sigL_toggles`), hence ArbOK T for all T ≥ 220. This covers the
audit's meaningful range (T ≥ the state LUT's delay, ≤ 664 ps at g = 1), replacing the weak T ≥ 785 ns of w1_all_hyps.

### progress 13:03 -- w1_hyps_and_correct CLAIMED: one Lean-checked run meets ALL of NetCorrectSeq's hypotheses AND Correct
Witness regenerated with the env's acknowledges 4 ns after their requests (Δo = 3 ns in Env), so Correct's data clause
has a real 1 ns sampling window: tools/cview/witn1.py ... 400000 4000 (97,926 transitions, result 6); all 75 chunk
checks rebuilt (two streams; an earlier overlapping build clashed, rerun clean). Updated: Wit1 (`w1_result` now at
775,455 ps), Wit1Env (ack delay 4000; ArbOK bounds). New `Formal/Net/CViewPS/Wit1Correct.lean`: `w1_correct :
Correct xW1 DecodedPS.boundary 400000 3000 (some 1) (fun _ => 12) (fun _ => 18)` (input acks follow the protocol and
are live; out0 and end requests follow the protocol, rise once, are live; out0's data during [request + 3 ns,
acknowledge) is Nat.gcd 12 18 (data bits settle at 768,160 ps, `busVal_after`); idle from 785,729 ps with one rise
each) and `w1_hyps_and_correct su T (220 ≤ T)`: (Behaves p1 ... ∧ ArbOK T arbs ∧ Env ... ∧ SeqEnv ...) ∧ Correct ....
lake build OK (1624 jobs), standard axioms, scan clean. **Meaning:** a concrete gate-level behaviour of the decoded
bitstream, at g = 1, κ = 0, satisfying every hypothesis of THE statement for one pair and its full conclusion. One
run: a consistency check of the statement (not vacuous, not contradicted, at n = 1); no claim for other runs.
