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
