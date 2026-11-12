# B probe 7n: finishing the involution arbiter

File: `formal/lean/Formal/Cells/ArbInvolution2.lean` (about 920 lines). It imports
only `Formal.Cells.ArbInvolution` (probe 7m, read-only). It adds no shared
definitions. New definitions that only this file uses: `ext`, `Passes`, `Margin`,
`swapP`, `ALoopM`, `AGrantM`, `hyp`, `Pc`, `G5c`, `G6c`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH ../slot.sh lake env lean Formal/Cells/ArbInvolution2.lean

Status: **checks clean**, with 0 errors and 0 warnings in about 10 s. The file
contains no `sorry`, `admit`, `axiom` or `native_decide`. I ran `#print axioms` on
the 13 main theorems (the ones in **bold** below, plus `Pc_orb`) from a scratch
copy. Every one depends only on `propext`, `Classical.choice` and `Quot.sound`.

Before the first check, `ArbInvolution.olean` was missing. I compiled it as the
probe instructions say:

    ../slot.sh lake env lean Formal/Cells/ArbInvolution.lean -o .lake/build/lib/lean/Formal/Cells/ArbInvolution.olean

`CElemInvolution.olean` was already present.

## Model (unchanged from 7m)

* The REAL INITs of `bd_arbcell`, evaluated through `lutB`/`o5B`/`o6B` (7a's `stF`,
  `gr1`, `gr2`), are applied in zero time.
* The state LUT plus its feedback route is ONE involution channel `P`.
* O5 and O6 of the grant LUT are separate involution channels `G5` and `G6`.
* The channels are A's `InvolutionPair`/`tent`, through 5e's signal-level fragment
  `InvChanF`. That fragment allows at most one cancellation, and only of the LAST
  two tentative edges.
* Requests are ideal steps. `r1` rises at `0` and `r2` at `s`. The same request and
  `q` signals reach both LUTs (H_NO_PIN_SKEW).

## Results (namespace `Formal.Cells.ArbInvolution2`)

### 1. Resolving gaps (open item 1)

**Question.** Near `s*`, can a final cancellation in a grant channel leave one grant
stuck high while the other keeps pulsing?

**Answer: no, in every solution.** A cancellation removes a PAIR of tentative
edges, so it never changes the final value of a channel's output. On a resolving
orbit, `q` has finitely many edges, so both grants also have finitely many edges.

* **`grants_resolve`**: let `0 < s < δ∞↑` be any gap that does not oscillate forever.
  * In every solution of the cell with its grant LUT, there is a time `T` after
    which `q = c`, `g1 = c` and `g2 = ¬c`, for one constant `c`.
  * No `BBM` is needed.
  * `c = 1` exactly when the number `m` of real `q` edges is odd.
* **`grants_exclusive`**: under `BBM G5 G6`, `g1 ∧ g2` is false at every time, for
  EVERY gap `0 < s < δ∞↑`. This covers both the oscillating case (7m) and the
  resolving case, including a final cancellation in either grant channel.

How the proof goes:
* `run_fin`: on a finite input of `K` edges, the O5 output has `k1 ∈ {m, m−2}` edges
  and the O6 output has `k2 ∈ {m+1, m−1}`.
* `interleaveG` is 7m's interleave, restated for any increasing edge sequence.
  The finite `q` prefix is padded with `ext` to fit it.
* `excl_fin` is a case split covering the 4 shape combinations. It turns up a
  coupling of the cancellations, which is the interesting part. Under `BBM`:
  * if O6 cancels the last `q` pulse and O5 does not, then the chain
    `a(m−2) < a(m−1) < b(m) ≤ b(m−1) < a(m−2)` is a contradiction. So that
    combination either has no overlap, or is impossible;
  * the mirror case, where O5 cancels and O6 does not, gives the same kind of
    contradiction.

### 2. `H_GRANT_PASS` derived (open item 4)

* `Passes G h` is a named hypothesis per grant output. It says that an isolated
  pulse of width `h` survives `G`, for both polarities:
  * field `H_PASS_HI`: A's `pulseWidth h > 0`;
  * field `H_PASS_LO`: the same for a low pulse.

  Test: the pulse-shrink curve of that LUT output at input width `h`.
* `tent_step`: if consecutive input edges are at least `h` apart and `Passes G h`
  holds, then the two tentative outputs do not cancel, whatever the history.
* `Margin P g` is a property of the loop channel. It is a definition, not an
  assumption: a `q` pulse narrower than `g` makes the next pulse so wide that the
  one after it cancels.
* **`margin_orb`**: on any chain of `M` real loop edges, every `q` gap
  `orb(n+1) − orb(n)` with `n + 2 < M` is at least `g`. The initial gap `δ∞↑ − s`
  (the first pulse of `r2 ∧ ¬q`) is also at least `g` when `M ≥ 2`. Only the last
  two `q` pulses of a resolving orbit can be narrower.
* **`margin_exists`**: every `P` has such a `g > 0`. The proof uses the continuity
  of A's delay functions, which 5e derived from strict monotonicity. No extra
  hypothesis is needed. (`IsDMin` is not used either.)
* **`grants_exist_all`** and **`grants_exist_auto`**: there is `g > 0` that depends
  only on `P`. If both grant channels pass `g`-pulses, then the full cell has a
  solution at EVERY gap `0 < s < δ∞↑`.
  * At an oscillating gap, this discharges 7m's `H_GRANT_PASS5/6`.
  * At a resolving gap, the grant channels can cancel only the last `q` pulse,
    which the fragment covers. This is `run_of_prefix`.

  So the exclusion and resolution theorems are not vacuous whenever the grant
  outputs filter less than the margin of the state loop.

### 3. Mirror scenario (open item 2)

* `swapP P` is the pair with `δ↑ ↔ δ↓`. It is again an involution pair, because
  A's fields map onto each other.
* `ALoopM` and `AGrantM` describe the mirror run: reset `q = 1`, `r2` first at `0`,
  `r1` at `s`.
  * The named hypothesis `H_CH1` models a channel idle at 1 by its complement:
    `¬x ↦ ¬q` is A's channel `swapP P`, idle at 0.
  * Physically: the first edge is a FALL of `x`, and it gets the falling delay
    `δ∞↓`.
  * The grants are still idle at 0, so `G5` and `G6` are unchanged.
* The real INITs satisfy `stF_mirror` (`¬stF a b q = stF b a ¬q`) and
  `gr_mirror1/2` (O5 and O6 swap). `bbm_comm`: `BBM G5 G6 → BBM G6 G5`.
* `toA` and `toAG`: every mirror solution is a 7m solution for `swapP P`, with the
  requests, the grants and `G5`/`G6` exchanged.
* The results transfer as follows:
  * **`arbM_eternal`**: a critical gap `s*' ∈ (δ∞↓ − δ↓(0), δ∞↓)`, where `q`
    oscillates forever.
    * `s*'` is the critical gap of `swapP P`. It differs from 7m's `s*` unless
      `δ↑ = δ↓`, so the two arrival orders have DIFFERENT critical gaps.
  * **`arbM_slow_resolution`**: arbitrarily late resolution, with `q` eventually 1.
    So `r1`, the later request, wins.
  * **`grantsM_eternal`**, **`grantsM_exclusive`** and **`grantsM_resolve`**: the
    same grant theorems as in 7m and section 1.
  * **`grantsM_exist_auto`**: non-vacuity, with the margin of `swapP P`.

### 4. A concrete overlapping triple (open item 3)

Shard A's exp-channel is NOT claimed with a real `exp`/`log`. The claimed code has
only the abstract `ExpLog`; the instance is in A's Wip. I therefore used my own
explicit, rational member of A's class:

* `hyp A B k` sets `δ↑ T = A − k/(T+B)` and `δ↓ T = B − k/(T+A)`. All of A's fields
  are proved; it is causal iff `k < A·B`.
* `Pc = hyp 1 1 (3/8)` is the loop channel.
  * **`Pc_orb`**: its critical gap is EXACTLY `s* = 3/4`. The `q` edges are at
    `1 + n/4` forever (`Pc_osc`).
  * This is a constructive witness for 5e/7m's `crit_exists`, which only proved
    that such a gap exists.
* `G5c = hyp (1/4) (1/4) (1/128)` is the O5 channel, and
  `G6c = hyp (5/16) (5/16) (1/128)` is the O6 channel, 25% slower.
  * Both pass pulses of width `1/4` (`G5c_pass`, `G6c_pass`). With `tent_step`,
    this discharges `H_GRANT_PASS` (`c_pass5`, `c_pass6`).
* **`overlap_reachable`**:
  * the cell has a solution;
  * in EVERY solution, both grants pulse forever, and `g1`, `g2` are high together;
  * `¬ BBM G5c G6c`.

  The edge times are:

  | Edge | Time |
  | --- | --- |
  | `g2` rises | `17/16` |
  | `g1` rises | `5/4` |
  | `g2` falls | `41/32` |
  | `g1` falls | `47/32` |

  So the overlap is `[5/4, 41/32)`, which is `1/32` wide. The units are relative:
  the loop's `δ∞ = 1`.

  Overlap at the critical gap is therefore reachable, not just conditional.

## What did not work / not done

* **Interior cancellations stay outside the model.** `InvChanF` (5e) has no run
  when the cancellation is in the interior.
  * Section 2 shows this never happens if the grant outputs pass pulses of width
    `g(P)`. Under that condition the theorems are unconditional.
  * If a grant output filters MORE than the loop margin, the theorems are vacuous
    for that channel. Fixing that needs A's full trace semantics.
* **Overlap at EVERY period** (persistence) is not proved for the concrete triple.
  Only one overlap is proved.
  * Proving it needs the steady state of `d(n+1) = δ(1/4 − d(n))`, whose fixed
    point is irrational for `hyp`.
  * Steady-state reasoning says the overlap recurs, because the shift between
    O5 and O6 is not a multiple of the period, but this is not proved.
* **Overlap at a resolving gap** (for example a normal latched arbitration with
  O5/O6 skew, which is 7a's transport-skew overlap) is not instantiated. It would be
  a 1-edge version of `first_edge_overlap`.
* **Final cancellations.** No concrete instance shows that a grant channel's final
  cancellation is actually reached. `margin_orb` shows that the last `q` pulse can
  be arbitrarily narrow, but only in the sense that no lower bound exists; no
  witness is built.
* **Not modelled:**
  * pin skew between `ustate` and `ugrant` (H_NO_PIN_SKEW);
  * `bd_arbiter`'s A0 hold;
  * series composition of channels (LUT plus route lumped).

  All three are as in 7m.

## Verdict

**Works.** All four open items of 7m are closed in about 1 h. The whole file checks
in 10 s.

What it buys the project:
* **Exclusion.** For `bd_arbcell` in Fuegger's binary gate model, with the real
  INITs, `BBM` between O5 and O6 gives mutual exclusion of the grants:
  * at EVERY request gap;
  * in BOTH arrival orders;
  * through metastability and through every grant-channel cancellation that the
    fragment allows.
* **Resolution.** A resolution always hands over exactly one grant to the winner.
* **Non-vacuity.** The theorems are non-vacuous whenever the grant outputs pass
  pulses of a width that depends only on the state loop.
* **BBM is necessary, not just sufficient.** Without `BBM`, an O6 that is 25%
  slower than O5 gives a provable `(1,1)` at the critical gap.

What it means for routing:
* The measurable obligations per route are `BBM` and `Passes(g(P))`. Both come
  from the per-output rise/fall delay curves of `ugrant`.
* `BBM` can be checked from the routed per-output delay arcs, before a board
  exists:
  * at a `q` rise, O6's fall must beat O5's rise;
  * at a `q` fall, O5's fall must beat O6's rise.

Effort to go further:
* persistence of the overlap: about half a day;
* removing the fragment: 1–2 days, shared with A's trace semantics.

## Fidelity per primitive

* **State LUT, grant LUT**: the real INITs through `lutB`/`o5B`/`o6B`, in zero time.
  All delay and pulse shaping are moved into the output channels.
* **Feedback route**: lumped with the state LUT into one involution channel.
* **Idle-at-1 channel (mirror)**: modelled by complement as `swapP P`. This is
  exact for A's transition semantics, because complementing both signals swaps
  which delay function applies to each edge. It is stated as the named hypothesis
  `H_CH1`, not derived from a signal-level channel that starts at 1.
* **`Passes`**: a pulse-shrink measurement at one width per polarity.
* **`Margin`**: a definition derived from `P`.
* **`hyp` channels**: members of A's class (strictly monotone, involution, causal)
  that are not fitted to anything. They are concrete witnesses, not a model of the
  xc7z010 fabric. Fitting real LUT outputs needs A's exp-channel or measured curves.
