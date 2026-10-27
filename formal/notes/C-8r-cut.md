# C-8r: discharging H_CUT (capstone O1, network half)

Shard C, probe 8r, 2026-10-27. About 2.5 h.

## Verdict

**Works, with one finding and one remaining token-level hypothesis.** H_CUT, and with it
H_CM_FORCED, is now PROVED for every circuit run meeting H_CELLS and H_BUNDLE, given two named
hypotheses. Neither of them is about the arbiters or about counts in the circuit:

1. **H_START_ONCE** (environment): the `start` channel is offered at most once.
   - This is the finding. With 8m's environment model it is **necessary**. 8m models `start`
     with `Src`, the free-running `bd_src`. Under that model H_CUT is false for some runs that
     H_CELLS allows. The scenario is below.
   - The rig, `cells/hw/gcd_rig.v`, re-offers `start` only after the result comes back, so
     during one invocation it offers `start` once.
2. **H_WALK** (`WalkOK`): a statement about the token run alone, with no circuit trace in it.
   - The control token walks along the circuit spine, steered by the token run's own values.
     H_WALK says: at each arbiter stage it reaches, the token run's control_merge label for that
     stage's next output token names the input the token arrived on.
   - **Not proved in Lean.** It is checked on 32 input vectors by `Wip/C8r/walkcheck.py`. Two
     negative controls make it fail.

So the requested theorem, "only H_CELLS and H_BUNDLE", is **not** reached as stated, and it
cannot be with 8m's `Src` model of `start`. What is proved instead:

```
theorem gcd_hw_circuit_safe'' (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (H_WALK : ∃ y, Good a b y ∧ WalkOK (σY a b y) (omOf a b y)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b))
```

The difference from 8q's `gcd_hw_circuit_safe'`: H_CUT was a circuit-trace property about
request counts at the 9 arbiter stages. It is replaced by
- an environment property (H_START_ONCE), and
- a pure token-level property (H_WALK) that can be decided for any given `(a, b)`.

## The obstruction: a second start token breaks H_CUT under `Src`

`Capstone.Src` (8l) lets `start.req` rise again whenever `start.ack` is low. That is the gate
model of `bd_src`, a free-running source. In the circuit:

1. `start` → fork0 → `g4` → bjoin(cond 9) → control steer → ... → the first link.
2. Once a link latches the first token, the acknowledges propagate back and close `start`'s
   handshake. The source may then offer a second token. `a` and `b` are free-running too, so
   the condition tokens that steer it are available.
3. The second token travels the same entry path to the loop header's arbiter. Its entry input
   `x` re-requests as soon as its first handshake has closed, that is, once the arbiter has
   passed the first token into the loop. Nothing waits for the loop to finish.
4. Take any input where the loop iterates at least once, e.g. `a = 12, b = 18`. Then
   `ω 0 = false` (entry) and `ω 1 = true` (back edge).
   - When `x` offers its second token, `z` has offered `n = 1` token.
   - 8q's bound is `cnt ¬ω 1 + [¬ω 1] = 1`. But `x` has offered 2. **H_CUT is violated.**

**Status of this argument.** It is argued, not mechanised: a 465-channel witness trace was not
built. Every step uses only the unbounded SI delays of H_CELLS.

**What it means.** The violation is not a design bug. It is a modelling gap in the
environment. The rig's environment is a two-node ring: `uenv0`/`uenv1` re-request `start`
only after `res_req`, i.e. after `out0`. The rig's own header says "exactly one gcd is ever in
flight".

**H_START_ONCE.**
- **Satisfiable together with `Src`.** `Src` allows an unbounded delay before re-requesting,
  so a run that offers once meets both. The all-quiet run meets every hypothesis.
- **Grade B** for the rig, within one invocation.
- **Test.**
  - GLS of `gcd_rig`: count `start_req` rises between reset and the first `res_req`. It must
    be 1.
  - Structurally, it follows from the rig's env ring, if that ring were modelled. That is the
    route to grade A. The theorem then covers one invocation; repeated invocations would need
    the walk to restart at `start` after the spine token has been sunk.

## Theorems (all proved: no sorry, no axiom beyond propext / Classical.choice / Quot.sound, no native_decide)

### `Formal/Net/CapstoneCutCells.lean` (namespace `Formal.Net.Capstone.Cut`)

**Strict causality of each spine cell.** "An output offer at `t` needs the input offer before
`t`." Each one is 8q's exact counter identity at `t`, plus the gate's own guard at the rising
step.

| theorem | statement | from |
|---|---|---|
| `fork_strict` | `#off(out)(t+1) ≤ #off(in)(t)` | `F.wire` |
| `join_strict` | the same, for every input of a join (bjoin included) | `J.cel`, `off_idle` |
| `link_strict` | the same, for a link | 8l's table: an `o.req` rise needs `d = 1`, and the input is mid-transaction |
| `steer_strict` | `#off(out b)(t+1) ≤ selOff b t` | `S.lut` |

**`amerge_data_upto`.** This is 8l's `amerge_op_forced` (data half), with H_CM_FORCED needed
only for the offers made up to the offer being valued. The patched stream changes only the
output indices not yet offered by time `r`.

### `Formal/Net/CapstoneCutSpine.lean` (namespace `Formal.Net.CapNet.Gcd`)

**The spine.**
- `spL` marks 67 of the 465 channels as spine channels. It is generated by
  `Wip/C8r/spinegen.py`: the segments of GcdHw's `spine`, the control branches' `jL`, and the
  arbiter outputs `z`/`acc`.
- `spok_all` checks the spine's shape at all 367 operators, by kernel `decide` over a Bool
  traversal (`SpOK`). The generator is not trusted: a wrong `spL` fails this check.
- `SpOK` requires:
  - a spine output comes only from a spine input, via a fork (exactly one spine output), a
    link, a bjoin (`[cond, data]` with only the data input on the spine), a control steer (both
    outputs on the spine), an arbiter stage (`x`, `y`, `z` on the spine, `x ≠ y`), or the
    `start` source;
  - data operators have no spine outputs.
- `noloop`: no channel is produced and consumed by the same operator.

**The walk.**
- `nxt σ c k` is the next spine channel after the `k`-th visit to `c`.
- `walk σ p` gives the next channel `cur` and the earlier visit counts `W` of every channel.
- `WalkOK` is H_WALK.

**Generic walk facts.**
- `flow`: visits plus [`cur` = c] = transitions into `c` + [c = start].
- `cnt_visit`: reindexes walk time to visit index.
- `in_cp`: transitions into a link, fork or bjoin output equal the visits of its input.
- `in_st`: transitions into a steer output equal the input's visits whose select matches.
- `am_side`: under H_WALK, an arbiter's input visit counts are the oracle's label counts at the
  output's visit count, plus the token if it is about to pass.

### `Formal/Net/CapstoneCut.lean` (namespace `Formal.Net.CapNet.Gcd`)

**`main`: one induction on time.** At every `t` it carries three facts:
- **`Inv t`:** there is a `p` such that the circuit's offer counts on all 67 spine channels are
  exactly `(walk σ p).W`.
- **`ForcB t`:** every arbiter offer before `t` has the oracle's winner.
- **`Agree ch σ t`:** every offer before `t` carries the stream solution's value.

**The step lemmas.**
- **`forc_at`.** Forcing at `t` comes from `Inv t`, `am_counts` (`am_side` instantiated) and
  8q's `offer_pending`.
- **`agr_at`.** Values at `t` come from 8f/8j/8l's per-operator `OpData`, via 8m's
  `cell_op`/`eqn_sound`. The arbiter case uses `amerge_data_upto`.
- **`rise_cur`.** A spine channel can rise at `t` only if it is the walk's `cur`. Proof:
  - per producer kind, a strict lemma together with `in_cp`, `in_st` or `am_counts` gives
    `W c + 1 ≤ transitions into c`, and `cur_of_bound` concludes;
  - for `start`, H_START_ONCE plus `tr_start` (the walk never re-enters `start`);
  - non-spine kinds are excluded by `SpOK`.

  So at most one spine channel rises per step, and `Inv` advances by 0 or 1 walk steps.

**Results.**
- `gcd_hw_forced`: H_CM_FORCED, proved.
- `gcd_hw_cut`: H_CUT (8q's `CutOp`), proved.
- `gcd_hw_circuit_safe''`: as above. It goes through 8m's `gcd_hw_circuit_safe`, which is
  unchanged.
- `gcd_hw_arbiters_uncontended'`: no free contention at any stage, now without H_CUT. It goes
  through 8q's theorem.

### `Wip/C8r/`
- `spinegen.py`: generates `spL`.
- `check_spine.sh`: drift check (`check_spine: ok`).
- `walkcheck.py`: the H_WALK tester. For each vector it:
  - runs the GcdHw token graph to quiescence;
  - checks `out0 = gcd`;
  - walks the circuit spine exactly as `walk` does;
  - checks `WalkOK` at every arbiter arrival;
  - checks that the walk ends;
  - checks that each GcdHw spine channel's first segment is visited exactly `|history|` times.

  Negative controls: `NEG=1` inverts stage 0's oracle (7 of 16 vectors fail, the others never
  reach that stage), and `NEG=2` inverts every steer select (16 of 16 fail).
- `Axioms.lean`: `#print axioms` only; it proves nothing.

## Run

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    for f in CapstoneCutCells CapstoneCutSpine CapstoneCut; do
      ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/$f.olean Formal/Net/$f.lean; done
    ../slot.sh lean Wip/C8r/Axioms.lean
    Wip/C8r/check_spine.sh; python3 Wip/C8r/walkcheck.py 10
    NEG=1 python3 Wip/C8r/walkcheck.py 2; NEG=2 python3 Wip/C8r/walkcheck.py 2   # must FAIL
    cd .. && ./check.sh Formal/Net/CapstoneCutCells.lean Formal/Net/CapstoneCutSpine.lean \
      Formal/Net/CapstoneCut.lean

Result, 2026-10-27:
- `check.sh` printed `[audit] 3347 declarations checked`, `[check] OK`, in 50 s.
- `CapstoneCutSpine` takes 32 s at 2.5 GB peak (`spok_all`, `noloop_chk`). `CapstoneCut`
  takes 2 s at 0.5 GB.
- `walkcheck`: `ok (32 vectors)`. The vectors include `a = 0` and/or `b = 0`, equal inputs,
  `2^31 - 1`, and powers of two. Up to 821 walk steps and 127 arbiter arrivals per vector.
- Both negative controls FAIL, as they must.

The lead has to add the 3 modules to `Formal.lean`; I do not own it.

## What remains, and the effort

**H_WALK in Lean (~1 day).** H_WALK says the circuit-spine walk reproduces the token run's
spine order. The route:
1. **Token level.** In every reachable store the spine carries one token
   (`closed_of_check`). So in the complete run, the cm firing after the token reaches input `i`
   consumes from `i` and appends `i`'s label. Proving this needs a forward argument over the
   remainder of the run (`gcd_hw_graph_live`), plus history determinacy: every complete run
   has the same histories, so `Hh a b y` does not depend on `y`.
2. **Simulation.** Each walk step must be matched by a run prefix that has the spine token in
   the walk channel's GcdHw group. Link segments and `jL` stay in the group. `z`/`acc` are
   the cm firing; `acc` exists for the 3-input cascade.
3. **Per-vector alternative.** For a fixed `(a, b)`, H_WALK is decidable once a concrete `y`
   is exhibited. That would be a kernel non-vacuity check, but the run has thousands of
   firings, so it may be too large for the kernel.

**H_START_ONCE from the rig (~0.5 day).** Model the env ring (`uenv0`, `uenv1`, the fork)
as cells and prove "start re-requested only after `res_req`". Then extend the walk
periodically, re-entering `start` once the spine token has been sunk, to cover repeated
invocations.

## What it buys

- **O1's network half is closed** except for the token-level H_WALK and the environment
  hypothesis.
  - Arbiter forcing, the count bound, and "no free contention" now all follow from the gate
    models, bundling, one start token, and a property of the abstract token run.
  - That property can be decided per input and is tested on 32 vectors.
- **Finding: the environment model matters for O1.** With the free-running `Src` for
  `start`, the circuit model allows two invocations in flight. The H_CUT/forcing argument
  then genuinely fails, and with it the single-token reasoning that gives determinism. The
  rig is safe only because its env ring serialises invocations.
  - `C-gcd_hw-hypotheses.md`'s H_SRC row should say this: "offers start once per result",
    not "offers by the four-phase protocol".
  - The rig comment "One token also means exactly one gcd is ever in flight" is the design
    invariant this proof needs.

## Fidelity of the models used

Nothing new at cell level.
- `Fork`, `Join`, `Steer` (8f), `Link` (8l) and `CM.AMerge` (8j) are used through their
  existing invariants.
- **H_START_ONCE** is an environment restriction. It is a strict subset of the `Src`
  behaviours, and it holds for the rig within one invocation (grade B, test above).
- **H_WALK** is not a primitive model. It is a fact about the token run, of the same kind as
  C-8i's results, and it is decidable per input.
- **The spine set.** Its shape is kernel-checked. Its choice affects only whether H_WALK
  holds; `walkcheck` checks that it does.

## Surprises

- **H_CUT was not provable as posed.** 8q noted that "sources fire once", but the `Src` gate
  model does not fire once.
- **The circuit induction was easier than the 1-1.5 days estimated.** A walk with visit
  counters makes the index bookkeeping (S2) automatic, and the per-cell bound reduces to one
  generic `flow` lemma.
  - The only global fact needed is the arbiter arrival order. That fact is H_WALK.
- **`Src` needs no change for safety.** Restricting the trace (H_START_ONCE) is enough, because
  an SI source may wait forever.
