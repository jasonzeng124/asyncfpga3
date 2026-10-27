# Shard C journal (composition, ring, timing checker, netlist import, other tools)

## Verdicts (shard C)

- **Track 9 (ring needs three stages): works.** `Formal/Net/Ring.lean` (check:
  `formal/check.sh`). Ring of bd_link_ctl C-elements with the real bd_c2n INITs,
  interleaving semantics (H_SI): dead for N<=2; with one token live iff N>=3
  (`ring_three`); k tokens need N>=2k+1 (`k_tokens`); fair-window progress.
  The rule "3" is 2k+1 at k=1, resting on H_ONE_TOKEN (unproved). Not yet tied
  to bounded-delay traces (probe 8d). Effort to finish: ~1-2 days.
- **Track 8 (composition): works, at three levels, with a checker-to-FIFO
  theorem.** Protocol level (`Handshake*`): n-stage four-phase pipeline is a
  FIFO and live given per-link obligations (SetupHold around ack-fall; Sep =
  rule I/SDELAY; Hold = rule H/DACK; H_LATCH). End to end (`EndToEnd*`): the
  verified checker accepting a routed link netlist (fixed per-arc delays)
  implies that FIFO conclusion, with H_CEL_SI and H_LATCH derived from the real
  INITs on routed pin copies; found an obligation the project rules lack (latch
  open width). Gate level (`Muller*`, SI exhaustive, n<=4): with a free
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
  level). Circuit-level refinement of that graph + hypothesis list: 8l. Muller
  timed (`MullerTimed*`): the feedback condition derived from delay bounds,
  exact (converse witness), n<=3; on shipped placements it is
  placement-dependent and unchecked by the flow. Effort to gcd_hw end to end:
  ~2-3 weeks.
- **Track 10 (verified timing checker): works.** `Formal/Timing/{Semantics,
  Checker,CheckerToy}.lean`: interval STA over BoundedDelay arcs, executable,
  sound and per-node exact. Bundling check exact when req and data share only
  the launch; with a shared arc it is conservative under fixed delays (CPPR
  pessimism) but justified under per-event delays (glitches pass). Rules
  (array version, prjxray per-pip intervals, CPPR): ~1-2 weeks.
  Rules E/A/J (`Formal/Timing/Rules.lean`): a verified checker makes them exact
  relative to a stated delay model, not to silicon; the blocker is delay DATA.
  Each rule has a proved counterexample (E: SDF charges a flat ~25 ps per LUT
  pin, prjxray says A1 516 ps vs A6 5 ps slow max; A: sound under E's band only
  for data paths <= 402 ps; J: the pip-count estimate of the shared A0 route
  over-credits). nextpnr's SDF carries slow-corner max only (min=typ=max), so
  "shortest path" checks have no lower bound. Counterexamples are constructed
  netlists, not found in shipped routes (no routed SDF on disk).
- **Phase 1 Gen: done.** `Formal/Gen/` + `formal/tools/gen/gen.sh --check`:
  all 36 modules of cells/rtl (63 targets) generated from the project's yosys;
  163 theorems tie them to every B transcription and A's LutCells INITs; a
  flipped INIT bit breaks the build. bd_mem's BRAM is opaque.
- **Track 11 (netlist import): works.** (a) yosys JSON: 11 cells, project's own
  yosys 0.62 flow, generator + drift check (`formal/tools/import/import.sh
  --check`), proved equal to B's binary/Kleene transcriptions; a flipped INIT
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
  116 ps), but nothing for all delays; pure delay + spread runs out of memory.
  Best use: find the bound, then prove it in Lean. Zone-based dense time
  (12c, TChecker by git clone) pending.

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
