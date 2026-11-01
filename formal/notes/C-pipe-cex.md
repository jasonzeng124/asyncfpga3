# C-pipe: gcd_hw under a pipelined environment -- counterexample (exploration stage)

## Problem, plainly
THE goal (PROGRAM.md, owner 2026-10-31) asks for: for every sequence of pairs offered on the
input channel, where the environment may offer pair k+1 as soon as the input handshake of pair
k completes, the k-th output is gcd of the k-th pair, and every pair is answered.

**This is false for gcd_hw's handshake network**, in two ways, found by simulation:
1. **Reordering.** A later pair that skips the first loop overtakes an earlier pair that
   iterates in it. The k-th output is then the gcd of a different pair.
2. **Deadlock** (finite storage). Two threads in the loops block each other at the loop-header
   muxes and arbitrated merges. No output is produced at all.

## Evidence (NOT yet Lean; both tools are untrusted simulators)
| model | tool | environment | result |
|---|---|---|---|
| token level (Kahn graph `Formal/Net/GcdHw.lean` `rules`, unbounded FIFOs, any schedule) | `formal/tools/pipe/toksim.py a1,b1 a2,b2 --runs N` | all pairs present on a, b, start at once | values always right (300 random 2-3 pair runs, multiset = gcds); ORDER wrong: (2^20,2^20),(3,5) -> [1, 2^20] in 30/30 random schedules; (12,18),(3,5) -> [1, 6] in 7/40 |
| handshake network (`Formal/Net/CapstoneNet.lean` ops, the cell models of C-8t/C-wit, every gate delay 1) | `formal/tools/pipe/hwsim.py a1,b1 a2,b2` | gcd_rig's bd_fork over a, b, start; env_c' = not in_ack (free-running four-phase; offer k+1 when in_ack has fallen for k) | (2^20,2^20),(3,5): pair 2 accepted at tick 141, out0 offers [1, 2^20] at ticks 603, 1291. (3,5),(3,5); (8,8),(3,5); (64,64),(3,5); (64,64),(64,64): quiescent with no out0 offer (deadlock). (4,4),(3,5) -> [4, 1] (in order) |

For (2^20,2^20),(3,5) the handshake trace passes every cell-model field check of
`capwit3/sim.py check` (the only reported errors are the source-data check, which assumes one
value per source, and RigEnv, which is the SEQUENTIAL environment); every boundary channel
keeps four-phase order (no simultaneous req/ack change).

Deadlock state for (3,5),(3,5) (scratch dump): muxes 133, 136, 138-140 hold input y granted
while the select token for x waits; arbitrated merges 178, 180 hold y granted. 30 channels
pending.

## What this does NOT show yet
- Unit delays are ONE delay assignment, not the prjxray band. The reordering for (2^20,2^20),
  (3,5) has a wide margin (pair 2 out at 603 ticks vs pair 1 at 1291: 20 extra loop
  iterations), so it should survive any band; that is argued, not proved.
- CapstoneNet is the network built from bdc's graph and link plan, not the bitstream.
- The gcd_rig.v comment "the kernel acknowledges start only when it is finished" disagrees
  with this model (pair 1's input handshake completes at tick ~140, out0 at 430 for (12,18)).
  Which is right should be checked in research's routed GLS.

## Next
1. Lean, token level: a concrete schedule from the two-pair store to a store with out0 =
   [gcd p2, gcd p1] (`execL natVI rules init sched = some l`), kernel-checked.
2. Lean, handshake level: the unit-delay trace as a kernel-checked witness of the CapNet
   cell models (C-wit machinery) with the pipelined env, for reorder and for deadlock.
3. Research: a fid GLS of the target bitstream with a pipelined env (FOR-RESEARCH).
