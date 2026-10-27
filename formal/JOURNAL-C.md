# Shard C journal (composition, ring, timing checker, netlist import, other tools)

## Verdicts (shard C)

- **Track 9 (ring needs three stages): works.** `Formal/Net/Ring.lean` (check:
  `formal/check.sh`). Ring of bd_link_ctl C-elements; `RingGen` restates the
  headlines over the generated bd_c2n netlist (a flipped INIT breaks them),
  interleaving semantics (H_SI): dead for N<=2; with one token live iff N>=3
  (`ring_three`); k tokens need N>=2k+1 (`k_tokens`); fair window N(N-1)/2
  transitions (`RingFair`).
  The rule "3" is 2k+1 at k=1, resting on H_ONE_TOKEN (unproved). Not yet tied
  to bounded-delay traces (probe 8d). Effort to finish: ~1-2 days.
- **Track 8 (composition): works, at three levels, with a checker-to-FIFO
  theorem.** Protocol level (`Handshake*`): n-stage four-phase pipeline is a
  FIFO and live given per-link obligations (SetupHold around ack-fall; Sep =
  rule I/SDELAY; Hold = rule H/DACK; H_LATCH). End to end (`EndToEnd*`): the
  verified checker accepting a routed link netlist (fixed per-arc delays)
  implies that FIFO conclusion, with H_CEL_SI and H_LATCH derived from the real
  INITs on routed pin copies; found an obligation the project rules lack (latch
  open width). Gate level (`Muller*`; for EVERY n via `MullerAll*`, 9c): with a free
  feedback wire the real bd_c2n chain glitches already at n=1; with isochronic
  feedback or H_FB_BEFORE_INPUT it is hazard-free. Timed bridge (`Bridge*`):
  persistent + NoOvertake channels => timed traces are SI runs; per-change
  transport delay is unsound for SI. Kahn (`Kahn*`): determinacy, and the gcd
  loop (Dynamatic's control_merge header under H_ONE_INVOCATION) equals C gcd
  under every schedule; merge non-determinate. Gaps: forks/joins/merges at
  handshake level (8f), per-event glitching delays in the multi-token run,
  the gcd graph not imported from bdc. Operator composition (`Ops*`, Phase 3):
  any network of bdc's op cells refines the token semantics (prefix at every
  time, determinate), gate-level fork/join/steer/mux, arbitrated merge; gcd_circuit on the
  hand-drawn loop is VACUOUS for a != 0 (proved deadlock: that graph has no
  storage on its data loop), so the real bdc graph is required: done (`GcdHw*`, 8i): the graph bdc
  emits for gcd_hw, imported from bdc's own code with a drift check, ends every
  complete run on every schedule/arbiter outcome with exactly the C function's
  result (one-invocation invariant proved); with 8k: = Nat.gcd for a, b <
  2^31, every partial run completes, bounded, no fairness assumption (token
  level). Circuit level (`Capstone*`, 8l): every op cell gcd_hw uses has an operator
  theorem; every gcd_hw cycle carries >= 3 links (bdc's placement); safety
  proved conditional on a token-equation solution; hypothesis list in
  formal/notes/C-gcd_hw-hypotheses.md. `gcd_hw_circuit_safe` (8m): every run of the concrete 465-channel
  network latches only Nat.gcd a b on out0 under H_CELLS, H_BUNDLE and
  H_CM_FORCED, now reduced to H_CUT (8q: req-rise counting; arbiters see
  no free contention under it); H_CUT and H_CM_FORCED proved (8r) from H_START_ONCE
  (start offered once per result; a free-running start source breaks it)
  and H_WALK, now proved for all a, b < 2^31 (8s): `gcd_hw_circuit_safe3`
  needs only H_CELLS, H_BUNDLE, H_START_ONCE. Caveats: H_START_ONCE ("start
  rises once, ever") is false for the rig, which re-offers start after every
  result (8s2 is proving the first-result/per-invocation version); H_BUNDLE is
  stated on zero-delay traces, so tcheck discharges it only through a
  physical -> zero-delay refinement that is not yet proved (8w finding; 8x).
  No joint witness run yet (8t). Liveness: pipelines and single rings proved
  with linear bounds (8n, 8o); gcd_hw: arbiters provably never contested, so
  an uncontested-only settle bound suffices (8u); `gcd_hw_live` still rests
  on two open network obligations, H_NO_DEADLOCK and H_FIRING_BOUND (8z).
  Other kernels (8v): ipow's bdc graph = b^e mod 2^32 on every schedule for
  all i32 inputs, live; collatz conditional on C termination (unconditional
  1 <= n < 256). Token level only. Muller
  timed (`MullerTimed*`): the feedback condition derived from delay bounds,
  exact (converse witness), n<=3; on shipped placements it is
  placement-dependent and unchecked by the flow. Effort to gcd_hw end to end:
  ~2-3 weeks.
- **Track 10 (verified timing checker): works.** `Formal/Timing/{Semantics,
  Checker,CheckerToy}.lean`: interval STA over BoundedDelay arcs, executable,
  sound; per-node exact only over the choice of cell functions (fixed LUT
  functions: `win` is an upper bound, CheckerFixedFn). Bundling check exact
  in that same sense when req and data share only the launch; with a shared
  arc it is conservative under fixed delays (one example); the old
  "justified under per-event delays" needs a wire to glitch, which monotone
  routing rules out (audit C.md #2). Sound shared-prefix credit:
  SharedPrefix.pot2_sound under H_CLEAN_EDGE (10l). Known front-end gap: the
  prjxray model omits the slice OUTMUX hop (audit; 10m re-running all rows). Rules
  (array version, prjxray per-pip intervals, CPPR): ~1-2 weeks.
  Rules E/A/J (`Formal/Timing/Rules.lean`): a verified checker makes them exact
  relative to a stated delay model, not to silicon; the blocker is delay DATA.
  Each rule has a proved counterexample (E: SDF charges a flat ~25 ps per LUT
  pin, prjxray says A1 516 ps vs A6 5 ps slow max; A: sound under E's band only
  for data paths <= 403 ps, exactly (ruleA_band_threshold); J: the pip-count estimate of the shared A0 route
  over-credits). nextpnr's SDF carries slow-corner max only (min=typ=max), so
  "shortest path" checks have no lower bound. Counterexamples are constructed
  netlists, not found in shipped routes (no routed SDF on disk).
- **Phase 1 Gen: done.** `Formal/Gen/` + `formal/tools/gen/gen.sh --check`:
  all 36 modules of cells/rtl (63 targets) generated from the project's yosys;
  163 theorems tie them to every B transcription and A's LutCells INITs; a
  flipped INIT bit breaks the build. bd_mem's BRAM is opaque.
- **Track 11 (netlist import): works.** (a) yosys JSON: 11 cells, project's own
  yosys 0.62 flow, generator + drift check (`formal/tools/import/import.sh
  --check`), proved equal to B's independent binary specs (the Kleene
  comparisons only show the same INIT and pin order); a flipped INIT
  bit fails the build. (b) bitstream: `formal/tools/fasm2lean/check.sh`;
  bd_c2->bd_c2n routed on 4 seeds, FASM read back from the .bit, physical INIT
  + pip-walked pin map proved to compute the logical cells; mutated INIT/pips
  caught (which fasm_audit cannot see for re-pointed pips). (c) routed bd_link W=3 + bd_arbiter on 4 seeds: bits == yosys
  import up to a checked renaming (`Formal/Net/FasmLink`, `formal/tools/
  fasm2lean2/check.sh`), grant exclusion of the routed bits. LUT6/LUT6_2 only;
  FF/CARRY4/F7F8 semantics ~3-5 days, whole designs ~2-3 weeks. Finding: the placer's pin permutation is real
  (BLUT INIT 0x3220.. vs logical 0x00E8..), and moves delay by up to ~0.5 ns.
- **Track 12 (other tools): works with ~1 day per tool, as a bound-finder,
  not a prover.** UPPAAL/Workcraft/TChecker/PRISM downloads blocked (403);
  z3/SMT (12a: BMC + k-induction + Spacer, unbounded per fixed delay box) and
  Storm (12b): exact delay thresholds and witness
  traces in seconds for fixed integer delays (C-element: env min response >=
  feedback max; shipped arbiter: server latency >= ~60 ps, A0 rising skew <
  116 ps -- CAVEAT: 12a/12b/12c took prjxray's fast/slow corner pair 56/124
  as rise/fall, so these thresholds may be artefacts; 12d is redoing them at
  one consistent corner), but nothing for all delays; pure delay + spread
  runs out of memory.
  Best use: find the bound, then prove it in Lean. Zone-based dense time
  (12c, TChecker by git clone): done, same corner caveat.

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
