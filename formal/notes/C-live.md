# Liveness of bdc's handshake networks: what is proved (shard C, 2026-11-18)

Research's suite found deadlocks (quadrec: a ring holding as many tokens as it has room for;
nested / nest3 / lfsrfind in the default flow: an inner loop with zero trips) and fixed them with
a "token floor" in bdc (`research/data/suite/ringfloor.md` on `claude/research`). This note says
what formal has proved about that condition. Every file below checks with plain `lean` (core
Lean only, no Mathlib); run `formal/check.sh formal/lean/Formal/Net/StageNet*.lean`.

## The condition, in one line

In a fixed mode (every mux, merge and steer routing one way), the handshake network can lose a
stage forever **iff some closed walk of its marked graph holds no token**; without such a walk
nothing ever deadlocks and, under fair scheduling, every stage keeps firing.

The marked graph: for every pair of storage stages `p -> t` (`p` feeds `t` through joins, forks,
a mux's select join or a steer, never through another stage) there is an arc `p -> t` that holds
a token when `p` and `t` differ, and an arc `t -> p` that holds a token when they agree. A
closed walk may use both kinds, so it goes forward along some channels and backward along
others; that is research's "walk, turning back at joins and forks". Research's counting
(stages minus two per resting value forward, two per resting value backward, +1 per join turn)
is a way of counting the tokens on such a walk at an iteration boundary.

## The files

| file | what it proves | assumes |
|---|---|---|
| `Formal/Net/StageNet.lean` | stage model: `excited_iff_noZ`; a trap (set closed under token-free arcs into it) is invariant (`trap_step_iff`), its stages are dead forever (`trap_dead`); no trap => no reachable deadlock (`deadlock_free`) and every stage fires infinitely often in weakly fair runs (`fair_all_fire`); trap <=> token-free cycle (`trap_of_cycle`, `cycle_of_trap`) | speed independence (one stage at a time), fixed mode |
| `Formal/Net/StageNetRing.lean` | for a stage with one feeder and one consumer the stage rule is exactly the `bd_c2n` / `bd_c2n_set` LUT in run mode | shard B's verbatim INITs |
| `Formal/Net/StageNetGate.lean` | stage controllers plus ONE C-element per join and per fork: the gate network projects onto the stage network (`proj_step`) and its deadlocks are stage deadlocks; `gate_deadlock_free` | invariant `Inv` at the start (true at the all-zero reset) |
| `Formal/Net/StageNetTree.lean` | the same for any acyclic network of C-elements and buffers between stages: matched delay lines, `bd_ctree` joins, fork acknowledge trees; `tree_deadlock_free` | wiring well-formedness `WF` (a property of the netlist), `Inv` at the start |
| `Formal/Net/StageNetCert.lean` | a decidable certificate: a rank that rises along every token-free arc proves "no trap"; `Cert.check_sound`. `formal/tools/live/gencert.py` writes one per exported stage graph | the exporter is untrusted; the kernel checks the certificate |

## What is NOT proved

- **Mode changes.** All of the above is for fixed routing. Entering and leaving a loop, an inner
  loop that runs zero or one trip, and the first token after reset change which arcs exist.
  Research's model has the same limit; `formal/tools/live/fixtures/` explores the mode changes
  of the small kernels exhaustively at stage level (untrusted, bounded trip counts).
- **Gates other than C-elements and buffers on the handshake:** a steer's AND gates, a mux
  select's AND, FASTFALL's AND. With the routing fixed the first two are a wire or a constant;
  the FASTFALL gate is not modelled.
- **The arbitrated merge** (its grant is a race, `Cells/Arb*`), memory ops, data.
- **Timing, glitches, X.** The gates are binary and speed independent: a deadlock here is a
  deadlock for every delay, but "no deadlock" assumes every excited gate eventually fires
  cleanly. Runts and metastability are the timing shards' business (C36-C52, B).
