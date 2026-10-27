# Shard C journal (composition, ring, timing checker, netlist import, other tools)

## Verdicts (shard C)

- **Track 9 (ring needs three stages): works.** `Formal/Net/Ring.lean` (check:
  `formal/check.sh`). Ring of bd_link_ctl C-elements with the real bd_c2n INITs,
  interleaving semantics (H_SI): dead for N<=2; with one token live iff N>=3
  (`ring_three`); k tokens need N>=2k+1 (`k_tokens`); fair-window progress.
  The rule "3" is 2k+1 at k=1, resting on H_ONE_TOKEN (unproved). Not yet tied
  to bounded-delay traces (probe 8d). Effort to finish: ~1-2 days.
- **Track 8 (composition): works (protocol level + Muller stage).**
  `Formal/Net/Handshake*.lean`: n-stage four-phase pipeline is a FIFO and live
  given per-link obligations (source SetupHold around ack-fall; internal Sep =
  rule I/SDELAY, Hold = rule H/DACK; per-stage H_LATCH). Kahn/gcd (8b),
  gate-level Muller SI (8c), SI->timed bridge (8d), checker->FIFO end-to-end
  (8e) pending. Gaps: forks/joins/merges, general wire delays.
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
- **Track 11 (netlist import): works.** (a) yosys JSON: 11 cells, project's own
  yosys 0.62 flow, generator + drift check (`formal/tools/import/import.sh
  --check`), proved equal to B's binary/Kleene transcriptions; a flipped INIT
  bit fails the build. (b) bitstream: `formal/tools/fasm2lean/check.sh`;
  bd_c2->bd_c2n routed on 4 seeds, FASM read back from the .bit, physical INIT
  + pip-walked pin map proved to compute the logical cells; mutated INIT/pips
  caught (which fasm_audit cannot see for re-pointed pips). LUT-only so far;
  whole designs ~2-3 weeks. Finding: the placer's pin permutation is real
  (BLUT INIT 0x3220.. vs logical 0x00E8..), and moves delay by up to ~0.5 ns.
- Track 12: pending.

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
