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
  E/A/J exactness (10b) pending. Effort to real routed netlists: ~1-2 weeks
  (array version, prjxray per-pip intervals, CPPR).
- Tracks 11, 12: pending.

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
