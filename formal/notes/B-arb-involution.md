# B probe 7m: arbiter metastability from the binary gate model (involution channel)

File: `formal/lean/Formal/Cells/ArbInvolution.lean` (about 550 lines). It imports
`Formal.Cells.CElemInvolution` (probe 5e) and `Formal.Cells.ArbBinary` (probe 7a,
for the decoded INITs `stF`, `gr1`, `gr2` and the lemmas `stF_eq`, `gr1_eq`,
`gr2_eq`). It adds no shared definitions.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH ../slot.sh lake env lean Formal/Cells/ArbInvolution.lean

Status: **checks clean** (0 errors, 0 warnings, about 5 s). There is no
`sorry`/`admit`/`axiom`/`native_decide`. `#print axioms` on all 15 main
theorems (listed below) shows only `propext`, `Classical.choice` and
`Quot.sound`.

Before the first check, `CElemInvolution.olean` was missing. I compiled it as the
probe instructions say (`../slot.sh lake env lean Formal/Cells/CElemInvolution.lean -o
.lake/build/lib/lean/Formal/Cells/CElemInvolution.olean`).

## Model

* **State LUT**: `bd_c2n_set`, REAL INIT `0xFFB2FFB2FFB2FFB2`, pins
  `I0=r1 I1=r2 I2=q I3=rst=0`. It is evaluated through `lutB` (`stF`), and
  `stF_eq` (7a) proves it equals `C(r1, ~r2)`. The Boolean function is
  applied in zero time (Fuegger's gate model).
* **Loop channel**: the LUT and the feedback route to `I2` are lumped into ONE
  involution channel `P` (shard A's `InvolutionPair`, with 5e's signal-level
  fragment relation `InvChanF`).
* **Grant LUT**: REAL INIT `0x0C0C0C0CA0A0A0A0` (`gr1` = O5 = `r1.q`,
  `gr2` = O6 = `r2.~q`), applied in zero time.
  * O5 and O6 are two separate involution channels, `G5` and `G6`.
  * The grant LUT reads the SAME `r1`, `r2`, `q` signals as the state LUT.
* **Input**: probe 7a's runt. Both requests rise from idle: `r1` at `0`, `r2` at
  `s`, with `0 < s < δ∞↑(P)` (less than one loop delay).
  * The idle value is `q = 0`, so side 2 was the last winner. This is forced by
    `InvChanF`, whose signals start at 0.

Structures (every field is a named hypothesis with a doc comment):

* `ALoop P s r1 r2 x qp` has fields `H_R1`, `H_R2` (request pins), `H_LUT` (real
  INIT, zero time) and `H_CH` (one involution channel).
* `AGrant P G5 G6 s ...` adds the following fields to `loop`:
  * `H_GLUT1` and `H_GLUT2`: the real grant INIT, in zero time, on the same pin
    signals. This is H_NO_PIN_SKEW.
  * `H_G5` and `H_G6`: one involution channel per output.
* `BBM G5 G6` is the break-before-make hypothesis between O5 and O6:
  * `H_BBM1`: `G6.δ↓ x < G5.δ↑ y` for `x < y`. At a `q` rise, the O6 fall
    beats the O5 rise.
  * `H_BBM2`: `G5.δ↓ x < G6.δ↑ y` for `x < y`. At a `q` fall, the O5 fall
    beats the O6 rise.

  Both conditions apply only when the falling output has the smaller history
  argument. Test: the per-output rise/fall pulse-shrink curves of `ugrant`.
* Named hypothesis arguments: `H_GRANT_PASS5` and `H_GRANT_PASS6` in
  `grants_exist`. They say that the grant channels do not cancel on their input
  sequences.

## Key observation

`stF_runt` shows that on this input the arbiter's state LUT computes exactly 5e's
`bd_c2` OR loop: `[0,s) ∨ q`.
* The set literal `r1.~r2` is a runt of width `s`.
* Before 0 and after `s`, the request vector (0,0) or (1,1) holds `q`.

So `to_CLoop` maps every arbiter loop solution to a 5e `CLoop` with runt width
`s`, and 5e's derived recurrence `orb P s` governs `q`. This is the formal version
of the owner's model. The arbiter's q node is the same feedback-LUT C-element as
`bd_c2`, so its metastability comes out of the same gate model, with no
postulate.

## Theorems (namespace `Formal.Cells.ArbInvolution`)

### Section 1: the state loop
* `stF_runt`: on the runt input, the real `bd_c2n_set` INIT equals the real
  `bd_c2` INIT with `a=1`, `b=[0,s)`, `rst=0`, at every time and for every `q`.
* `to_CLoop`: `ALoop P s ... → CLoop P s aR (bR s) rstR x qp`.
* `arb_q_orb`: for `0 < s < δ∞↑`, in every solution `q` has transition times
  `orb P s`. Either this continues forever (`Osc`), or `q` stops at the first
  cancellation `m` and is then constant.
* `arb_exists`: every gap `s ∈ (0, δ∞↑)` has a solution.
* **`arb_eternal` (goal 1)**: there is a critical gap `s* ∈ (δ∞↑ − δ↑(0), δ∞↑)`
  that has a solution. In EVERY solution for `s*`, `q` takes both values after
  every time bound.
* **`arb_slow_resolution` (goal 2)**: for every `ε > 0` and `B` there is a gap
  `s ∈ (s* − ε, s*)` that has a solution. Every solution for that `s`
  resolves, with `q` eventually 0, yet `q` is still 1 after `B`.
  * Note what "`q` eventually 0" means: the LATER request `r2` wins, although
    `r1` came first. The race is decided against arrival order, arbitrarily
    late.

### Section 2: the grants
* `den_r1` and `den_r2` are signal algebra results:
  * `r1 ∧ q` is `q`.
  * `r2 ∧ ¬q` is the alternating signal with transitions `s, o0, o1, ...`
    (`cons1 s orb`). The proof needs the orbit to be unbounded or finite
    (`locate`).
* `grants_osc`: at an oscillating gap, in every solution:
  * the grant channel inputs are `den orb` and `den (s :: orb)`;
  * both grant runs are cancellation-free;
  * `g1 = den (G5.tent orb)` and `g2 = den (G6.tent (s :: orb))`.
  The last two shapes of `InvChanF` are impossible, because the inputs are
  infinite.
* `interleave`: under `BBM`, with `a = G5.tent orb` and `b = G6.tent (s::orb)`,
  the edges are ordered `b(2k) < b(2k+1) < a(2k) < a(2k+1) < b(2k+2)`. At every
  `q` edge, the falling grant moves first. The proof is an induction on the
  edge index, using strict monotonicity, A's `dom_ok` and the two `BBM`
  inequalities. At the base case, `H_BBM1` is used with a large `y` together
  with `δ↑ < δ∞↑`.
* **`arb_grants_eternal` (goal 3)**: at the critical gap, in every solution of
  the cell with its grant LUT:
  * **both grants pulse forever**: `g1` and `g2` each take both values after
    every time bound (`tent_gt`: a non-cancelling output lags its input, and
    the orbit is unbounded);
  * **under `BBM` they are never high together**: `g1 u && g2 u = false` for
    all `u`.
* `sym_bbm`, `exp_bbm`: identical symmetric O5/O6 channels (`δ↑ = δ↓`) satisfy
  `BBM`. In particular, A's exp-channel (RC plus pure delay) used for both
  outputs satisfies it.
* `first_edge_overlap`, `first_edge_iff`: if `BBM` fails at the first edge, `g1`
  and `g2` ARE simultaneously high (at `max a0 b0`). The condition is that the
  first O5 rise comes before the first O6 fall, which is equivalent to
  `G5.δ∞↑ < G6.δ↓(δ∞↑(P) − s − G6.δ∞↑)`. A second condition is also needed:
  `b0 < a1`, meaning `g2` has risen before `g1`'s first fall.
* `grants_exist`: at the critical gap, if neither grant channel cancels
  (`H_GRANT_PASS5/6`), the full system has a solution. By `grants_osc` this
  condition is also necessary.

## Answer to (3): can g1 and g2 be high together?

**Binary involution model.**
* A metastable `q` reaches both grants as an infinite train of FULL-SWING
  pulses on BOTH `g1` and `g2` (`arb_grants_eternal`). Each grant is
  intermittently high forever.
* Whether the two are ever high at the SAME instant is decided only by the
  relative rise/fall delays of the two LUT outputs:
  * with break-before-make between O5 and O6 (for example, identical symmetric
    channels), the pulses strictly alternate and never overlap;
  * if O6's fall is slower than O5's rise at the first edge (O5/O6 skew),
    they overlap (`first_edge_overlap`).
* The grant LUT's Boolean function never produces `(1,1)` (7a's
  `settled_exclusion`). Every binary-model overlap is therefore a channel
  (timing) effect, as in 7a's transport model (`exclusion_zero_skew`).

**Comparison.**
* **Kleene (7b)**: a metastable `q` gives exactly `(X,X)` on the grants
  (`both_grants_x_iff`), and never `(1,1)` or `(1,X)` (`grant_pairs`). The
  binary counterpart of `(X,X)` is "both grants pulse, unboundedly". Kleene's
  "never a definite 1 on both" matches the BBM case. Kleene evaluates both
  outputs at one instant on one shared `q`, so it cannot see O5/O6 skew. The
  overlap in the non-BBM case is invisible to it. Here, as in 7a, the binary
  model is the more pessimistic one.
* **Analog (7c, Buridan)**: for every `T`, some timing leaves `q` (and hence
  a grant) at an INVALID level at `T` (`analog_arbiter_not_exclusive`). The
  involution model never produces intermediate levels. It replaces the
  mid-rail plateau by an unbounded pulse train: `arb_eternal` is the binary
  form of "unresolved at every T".
* **What the models agree on**: arbitrarily late resolution near a critical
  timing (`arb_slow_resolution` vs. Buridan plus 7d's `e^{-T/τ}`).
* **Where they differ**: the analog model reaches both grants with half-levels.
  The binary model reaches them with alternating pulses, which overlap only
  through O5/O6 skew.

## What did not work / not done

* **Coverage of the critical gap.** All grant results are stated only at the
  critical (oscillating) gap. For resolving gaps near `s*`:
  * the grant runs end in shape 2 or 3 of `InvChanF`;
  * a cancellation in a grant channel at the end can leave `g1` stuck high
    while `g2` pulses.

  I did not analyse this. The same induction applies to the prefix, and the
  tail needs a case split.
* **Grant existence and `H_GRANT_PASS`.** Grant solutions exist only under
  `H_GRANT_PASS`. Whether the grant channel cancels on the critical orbit is
  not derived from anything. If it cancels, the fragment `InvChanF` has no run
  (interior cancellation), and the grant theorems are vacuous for that channel.
  Fixing this needs A's full trace semantics (A's Wip `filtered_output_trace`).
* **Exact characterisation of overlap.** There is no exact iff for overlap at
  ALL edges. The first violation of `BBM` at an edge does not by itself imply
  overlap, because a whole `g2` pulse can still fit in a `g1` gap.
  * Sufficient condition for exclusion: `BBM`.
  * Sufficient condition for overlap: `first_edge_overlap`.
* **Concrete overlapping pair.** No concrete involution pair is built that
  violates `BBM` and also has `b0 < a1`. Two exp-channels with different `Tp`
  shift everything, and the second condition then depends on `s*`. This
  would need a concrete `ExpLog` (the real `exp` instance is only in A's Wip).
* **Mirror scenario.** The mirror case was not done: reset value `q = 1`, with
  `r2` first and `r1` within `s` (a reset runt). The INIT is symmetric under
  `r1↔r2, q↔¬q`. The channel is not symmetric unless `δ↑ = δ↓`: the mirror
  uses the swapped pair (`δ↑↔δ↓`).
* **Pin skew.** Request/`q` pin skew between `ustate` and `ugrant` is not
  modelled (H_NO_PIN_SKEW). `bd_arbiter` (A0 hold, R0) is not modelled here.
  With `A0 = 0` its state LUT equals `stF` (7a's `stA_eq`), so Section 1
  transfers verbatim when `A0` stays low.
* **Inherited from 5e.** The `InvChanF` fragment covers at most one final
  cancellation. Also inherited: the uniqueness of `s*` and the matching
  exponential upper bound on the window.

## Verdict

**Works.** All three goals are proved, in about 1 h. Goals 1 and 2 cost almost
nothing once `stF_runt` showed that the arbiter runt IS 5e's OR loop. Goal 3 is
new and needed one induction (`interleave`) plus signal algebra.

Effort to finish:
* resolving-gap grant behaviour: about half a day;
* a concrete BBM-violating pair: about half a day, once A's `ExpLog`
  instance is claimed;
* removing `H_GRANT_PASS` and the fragment: 1–2 days, shared with A's full
  trace semantics.

What it buys the project:
* A gate-level derivation, from the real INITs, that `bd_arbcell` has a
  critical request gap with eternal binary oscillation and unbounded
  resolution time. No arbiter-specific postulate is used.
* A precise statement of what reaches the grants: alternating full-swing
  pulses on BOTH grants.
* The finding that simultaneous `(1,1)` in this model depends only on O5/O6
  output-delay asymmetry, which is measurable per route.

For downstream users: the ack C-elements A1/A2 see pulse trains on both
grants, so both requesters can receive grant activity while the arbiter is
unresolved. Their behaviour under such trains is track 5's question; it is
not analysed here.

## Fidelity per primitive

* **State LUT**: the real INIT via `lutB`, in zero time. All mux-tree delay
  and pulse shaping is moved into the loop channel. There is no X and no
  intermediate level.
* **Feedback route**: lumped with the state LUT into one involution channel
  (as in 5e). Series composition of involution channels is not proved.
* **Grant LUT**: the real INIT via `o5B`/`o6B`, in zero time.
  * O5 and O6 are separate involution channels.
  * The grant LUT reads the same `q` signal the state LUT reads: `q`'s fanout
    branch to `ugrant` has no extra delay or shaping (H_NO_PIN_SKEW). A branch
    channel would be a third involution channel in series, which is not
    modelled.
* **Requests**: ideal steps at the pins, the same at both LUTs.
* **Channels**: A's `InvolutionPair` (strictly monotone, involution law,
  causality). This is validated for inverter chains in the literature.
  * For a LUT output it has to be fitted per output and edge.
  * The `BBM` comparison is a direct test: on the same fitted curves,
    compare O6's fall delay with O5's rise delay at equal history argument,
    and the reverse.
