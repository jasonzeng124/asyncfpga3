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

## Tools (untrusted; each checked against the others and against research's simcheck rows)

| tool | what it does | run |
|---|---|---|
| `formal/tools/live/cells/` | gate-level speed-independent BFS on the verbatim cell INITs (links, C-element joins / forks / trees, bd_mux, bdc_muxn, cond_br, bdc_amerge2 with its arbiter, FASTFALL lines), protocol and index monitors; compares with the stage model | `run.sh` (RESULTS.md, RESULTS2.md, muxglitch.txt) |
| `formal/tools/live/fixtures/live.py` | exhaustive state search of a whole emitted design (every state-holding cell element, conditions nondeterministic, one or two invocations): LIVE for every trip count, or DEADLOCK with the choices and the token-free walk | `LIVE_BDC_DIR=<bdc> python3 -B live.py X.mlir`; `run.sh OUT` for the sweep (results.jsonl, RESULTS.md, MODEL.md) |
| `formal/tools/live/views.py` | research's ring_tokens.py, both views, on every fixture x flow x floor | `python3 views.py OUT.tsv` |
| `formal/tools/live/reentry/reentry.py` | research's walk view plus one "pass-through" view per loop (the one-trip re-entry mode); 183 / 183 with live.py | `python3 -B reentry.py X.mlir` (exit 1 = flagged) |
| `formal/tools/live/gencert.py` | stage graph JSON -> Lean `Cert.check ... = true` certificates | `python3 gencert.py OUT.lean G.json...` |

## Findings (FOR-RESEARCH C53-C58)

- Fixed mode: research's condition is exact (Lean, C53); the real cells agree with the stage model (C53, C56).
- Mode changes matter: matrix and stencil_2d (default flow) deadlock when an inner loop is re-entered after the enclosing loop
  iterates; the token floor's walk view does not see it (C55). Cause: condition 2 on a fork-join pair (inner header control_merge
  -> exit -> enclosing back edge -> inner mux entry input vs. its index -> select) in the one-trip mode (C58); research's back-edge
  rule also misclassifies such entry inputs (C57). One stage on the entry input, or a header olink, fixes both.
- Not speed independent (timing obligations, C55 / C56): the arbitrated merge's next output request vs. the previous winner's
  acknowledge falling (stale index); FASTFALL head buffer drain; bd_mux x_ack at a select change (a runt there loses a token).
