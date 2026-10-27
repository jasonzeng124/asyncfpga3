# C probe 9c: the gate-level Muller chain (`bd_pipe` control) for ALL n

## Verdict

**Works.** For every n >= 1, both under isochronic feedback and under the
relative-timing semantics (free feedback wire plus H_FB_BEFORE_INPUT), every
reachable state of the real `bd_link` chain is hazard-free and obeys every
pair rule. This gives the four-phase protocol on every link and token order
on every execution. The timed corollary also holds for every n: every
inertial timed trace that satisfies `FbBound` is an rt run, and so has the
protocol, token order and no glitch.

The model and the semantics are 8c's and 8g's, unchanged, and no new
hypothesis is added; the only extra assumption is `1 ≤ n`. Everything is core
Lean, with no sorry, axiom or native_decide. The axioms used are propext,
Classical.choice and Quot.sound.

The argument is the stage-cut the brief asked for:
- an invariant local to **two adjacent positions** (narrower than the
  3-stage window expected);
- a finite check on 3- and 4-position windows (5 positions for 8g's loop
  certificate), each done once by `decide +kernel`;
- a gluing lemma proved by hand for every n.

## What checks

    cd /home/user/asyncfpga3/formal && ./check.sh Formal/Net/MullerAll.lean Formal/Net/MullerAllTimed.lean
    # -> [audit] 1152 declarations checked, [check] OK   (about 95 s wall for both)
    cd formal/lean && export PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$PWD/.lake/build/lib/lean
    ../slot.sh lean Wip/C9c/Axioms.lean   # #print axioms: propext, Classical.choice, Quot.sound only
    ../slot.sh lean Wip/C9c/Neg.lean      # negative controls (#eval false, false, false, then (true, true))

(Axioms.lean and Neg.lean need the oleans of the two Formal files, which I
built into `.lake/build/lib/lean/Formal/Net/` with `lean -o`.)

| file | wall time | peak RSS |
|---|---|---|
| `MullerAll.lean` | 19 s | 1.4 GB |
| `MullerAllTimed.lean` | 71 s | 0.95 GB |

That is far below 8c's 6 GB for n <= 4, and it covers every n.

## Files

- `formal/lean/Formal/Net/MullerAll.lean` contains:
  - the local view (`V`, `posOf`, `typOf`, `lnext`/`lexc`/`lallowed`/`lenabled`);
  - the tables `adjIso`/`adjRt` and the window checks
    (`chkMid`/`chkLeft`/`chkRight`/`chkInit`, `chkAll_iso`, `chkAll_rt`);
  - the gluing lemmas;
  - the results for every n.
- `formal/lean/Formal/Net/MullerAllTimed.lean` contains the guard windows,
  `guard_glob`, `cert_all`, and the timed results for every n.
- `formal/lean/Wip/C9c/Axioms.lean` holds the axiom listing.
- `formal/lean/Wip/C9c/Neg.lean` holds the negative controls.
- `formal/lean/Wip/C9c/py/` holds the Python model:
  - `model.py`: 8c's semantics, with state counts matching 8c's table;
  - `proj.py`: the pair projections;
  - `ind.py`: exactness and inductiveness of the pair invariant, n = 1..6;
  - `gen.py`: prints the tables.

  Run them with `cd Wip/C9c/py && python3 ind.py`.

## Theorems (namespace `Formal.Net.MullerAll`)

Untimed, every `n ≥ 1`:
- `iso_good`, `rt_good`: `∀ s, Reach m n s → Good m n s`. This is the same
  `Good` as 8c's `iso_good_4` / `rt_good_3`, now for all n.
- `iso_hazard_free`, `rt_hazard_free`.
- `iso_protocol`, `rt_protocol`: `Handshake.Protocol` on every pair of
  `pairs n`, on every execution.
- `iso_token_order`, `rt_token_order`: `#c_k ≤ #c_{k-1} ≤ #c_k + 1`.
- `rt_ep`: 8g's enabledness persistence (EP).
- Building blocks:
  - `reach_inv`: reachable ⇒ `Inv`;
  - `inv_step`: closure;
  - `persist_glob`: no excitation and no rt-enabledness is ever withdrawn;
  - `follow_glob`: the pair rules;
  - `loc`: every node is a function of its own position and its two
    neighbours;
  - `V_fire`: firing a node changes only its own position;
  - `pairs_loc`.

Timed, every `n ≥ 1`:
- `cert_all : Cert n`. It replaces 8g's `checkT n = true`, which was
  kernel-checked only for n <= 3.
- `timedAll_reach`, `timedAll_step_run`, `timedAll_protocol`,
  `timedAll_token_order`, `timedAll_hazard_free`. These are 8g's
  `timed3_*`, now for all n. The hypotheses are `Timed n lo hi x` and
  `FbBound n lo hi`.
- Building blocks:
  - `guard_glob`: the gluing lemma for `guardOkB`;
  - `winP`/`winS`: the windows are faithful;
  - `rel_pred`/`rel_succ`: the loops written in window offsets;
  - `wf_all`, `cover_all`.

## The invariant (the answer to "find a hand invariant local to k-1..k+1")

**Positions.** Each position holds one number:
- position 0: a sentinel (48);
- position 1: the source (16 + src);
- position k+2: stage k, its 4 bits (c, b, w, f) read as a number below 16;
- position n+2: the sink (32 + snk);
- position n+3: a sentinel.

**`Inv m n s`.** For every q ≤ n+2, the pair (V q, V (q+1)) is in a fixed
table. The table is the same for every n and every stage:
- iso: 13 rows, 60 pairs; every f bit stays 0;
- rt: 21 rows, 140 pairs.

The tables are literal data (`adjIso`, `adjRt`), read off a Python BFS of
n = 5. They are a certificate: Lean checks them and does not trust them.
The rt table restricted to two stages reads, for example: stage value 2
(b = 1, others 0: a req in flight to the right) may only be followed by
5, 7, 13, 15 or the sink 33. That is, the right neighbour has already
latched (c = 1) or its own pieces are in transit.

**Python finding (not proved in Lean).** For n = 1..6, the set of states that
satisfy `Inv` is EXACTLY the reachable set, in both modes:

| n | iso | rt |
|---|---|---|
| 1 | 18 | 26 |
| 2 | 72 | 160 |
| 3 | 288 | 986 |
| 4 | 1152 | 6076 |
| 5 | 4608 | 37442 |
| 6 | 18432 | 230728 |

So the reachable set of the chain is pairwise definable: a Markov chain of
stage patterns. Lean uses only the direction reachable ⇒ Inv.

## Why the closure is a finite check (the gluing)

- `loc`: every node's gate function (`nextVal`), its rt restriction
  (`allowed`), its value and its excitation are a fixed function of
  (V (q-1), V q, V (q+1)) and its type, where q is the node's position. This
  is proved by hand per node form (src, snk, c, b, w, f), with the boundary
  cases k = 0 and k = n-1.
- `V_fire`: firing node y changes position `posOf y` only, by `xor 2^type`.

Hence:
- **Closure** of a pair (q, q+1) touched by y needs the triple around y.
  `chkMid` checks it for all triples allowed by the table.
- **Persistence** (hazard-freedom and EP) of x against y:
  - same position: `chkMid`;
  - left neighbour: the quadruple (q-2..q+1), `chkLeft`;
  - right neighbour: the quadruple (q-1..q+2), `chkRight`;
  - otherwise nothing x reads changes.
- **The pair rules**: every pair of 8c's `pairs n` joins nodes at the same
  or adjacent positions (`pairs_loc`), so `chkMid` covers them through
  `followL`.

For 8g's certificate:
- **EP** is the same persistence.
- **`guardOkB`** for the loops of stage k reads loop nodes at positions
  k+1..k+3 and their excitations, and the moving nodes' enabledness. So the
  check runs on windows:
  - (Q-2..Q+1) for the pred loop;
  - (Q-1..Q+2) for the succ loop;
  - where Q = k+2.

  The unused fifth slot is a constant sentinel. Any node outside the moving
  window leaves the level and the in-flight bit unchanged (`level_congr`).
  The check runs in 32 `decide +kernel` theorems, one per value of the
  middle stage and per loop side, to keep each kernel run small. A single
  theorem over all 35 k five-windows took more than 11 GB and was abandoned.

Negative controls (`Wip/C9c/Neg.lean`). The same mid-window check:
- fails for the physical free network with the rt table;
- fails for the rt semantics with the iso table;
- fails when the rt table loses one pair, (0, 2).

So the checker is not vacuous, and the table is tight at that pair.

## The local invariant IS inductive: no counterexample state

The brief asked for the counterexample state in case it was not. It is
inductive, at window width 2, in both modes. No global information is needed.

## Fidelity of each primitive

The models are unchanged from 8c and 8g. See `C-8c-muller.md` and
`C-8g-mullertimed.md`; summary:
- **`bd_c2n` LUT6.** It uses the real INIT, through Core `evalL`.
  `evalL_c2n` restates the LUT as `cfun a b q = (a ∧ ¬b) ∨ (q ∧ (a ∨ ¬b))`,
  checked on all 8 pin values against `evalL INIT_bd_c2n`. The only purpose
  is a cheap kernel table; nothing is re-modelled.
- **LUT1 buffer** `2'h2`: `evalL_buf`.
- **Wires.** Every wire is a free node. The forks are delay-insensitive.
  In iso mode only, the feedback is isochronic.
- **Environment.** Idealised four-phase source and sink, as in 8c.
- **Values** are binary. Atomic LUT (H_ATOMIC_LUT, as in 8c and 8g).
- **Reset** is clean (`s = 0`), and the reset release is not modelled.
- **Timed part.** All of 8g's hypotheses are unchanged: H_INERTIAL, H_LUMP,
  H_ATOMIC_LUT, H_RESET_CLEAN, H_ENV, and `FbBound` (the explicit per-stage
  inequality `hi(f_k) < lo` of each neighbour loop). This file adds only the
  generic `Cert n`.

## What does not work / open

- **Exactness of `Inv`** (Inv ⇒ reachable) is observed in Python for n ≤ 6
  and not proved. It is not needed for any claim. It would be needed only to
  claim that the table is the reachable set, for example to show that a
  given pair pattern does occur. That is not proved here: liveness and
  reachability of every pattern are not stated.
- **No new modelling.** Everything open in 8c and 8g stays open:
  - the equality case of `FbBound` (it needs a Kleene timed LUT);
  - corner-consistent numbers;
  - routed `bd_pipe` delays per stage;
  - the data path and bundling (8a);
  - X / metastability.
- **The table is fixed per mode.** A different cell (for example
  `BD_LINK_DC`, SDELAY > 1 with several LUTs in the req path, or DACK > 0)
  needs its own table and its own window functions. The method carries over:
  BFS a small instance, project onto adjacent pairs, check inductiveness on
  windows. The per-node `loc` gluing must be redone for new node forms.
- **`Formal.lean`.** I did not add the two new modules to the library root.
  It is not my file, and the lakefile globs `Formal/**` anyway, per its header.

## Effort

About 2.5 h. Most of it went into the gluing: `loc`, `V_fire`, `pairs_loc`
and `guard_glob`. The finite checks were cheap once the windows were sized
right.

## What it buys the project

- The `bd_pipe` control chain at gate level, with real INITs and every wire
  of unknown delay, is proved hazard-free and four-phase **for any pipeline
  depth**. This holds:
  - under isochronic feedback;
  - under the relative-timing condition;
  - with the timed version, under the explicit per-stage inequality
    `hi(fb route) < lo(ack route) + lo(LUT6) + lo(req path)` (and the
    analogous succ-side one).

  Before this, the result held only for n ≤ 3 or 4. A routed pipe of any
  length now needs only the per-stage `FbBound` check (track 10 / 11b),
  and no state-space search.
- A reusable pattern for chain- and ring-shaped control networks:
  - find a pairwise-definable reachable set by BFS projection;
  - check closure and persistence on 3- and 4-windows by `decide`;
  - glue by `loc` and `V_fire`.

  The kernel cost is independent of n.

## Surprises

- The invariant needs only width 2 (adjacent positions), not the 3-stage
  window suggested. The reachable set is exactly the set of stage words
  whose consecutive pairs are admissible.
- 8g's loop certificate (EP + level checks) also localises, to 4 positions
  per loop side. The only real obstacle was kernel memory for one big
  `decide`; it was solved by splitting the check per middle-stage value.
