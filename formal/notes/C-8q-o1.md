# C-8q: capstone O1 (discharging H_CM_FORCED)

Shard C, probe 8q, 2026-10-27. About 2 h.

## Verdict

**Partly done. O1 is not closed.** The arbiter half of O1 is proved: forcing and contention,
at every one of the 9 stages. What remains is the network half. It is now a count-only
hypothesis, H_CUT, in place of H_CM_FORCED.

- **What is proved.** `gcd_hw_circuit_safe'` has the same conclusion as 8m's theorem: every
  value latched on `out0` is `gcd a b`. Its hypotheses are H_CELLS, H_BUNDLE and H_CUT, and
  H_CM_FORCED is gone. 8m's `gcd_hw_circuit_safe` is used unchanged.
- **What it is not.** It is NOT the requested theorem with only H_CELLS and H_BUNDLE.
  Discharging H_CUT needs a network simulation; the estimate is below.
- **Checks.** No sorry, no axiom beyond propext / Classical.choice / Quot.sound, no
  native_decide. `check.sh` passes on the 3 new files.

## Theorems (all proved)

`Formal/Net/CapstoneO1Stage.lean`, namespace `Formal.Net.Capstone.O1`. These are about one
arbiter stage, using 8j's gate model `CM.AMerge` with free grants.

- **`CutBound x y z ω`** is the new hypothesis shape. Fix a time `t`, and let `n` be the number
  of offers `z` has made so far. Suppose the first `n` winners were `ω`. Then:
  - input `x` has offered at most `#(¬ω before n) + [¬ω n]` tokens;
  - input `y` has offered at most `#(ω before n) + [ω n]` tokens.

  These are exactly the input tokens that control_merge firings `0..n` of the token run
  consume. In short: **the circuit is never ahead of the token run at this stage's inputs.**
- **`zc_eq`.** 8j's internal "passed" counters `zc0`/`zc1` equal the winner counts at the
  number of `z` offers.
- **`offer_pending`.** At each `z` offer, the winning input has exactly one token that it has
  offered and the stage has not yet passed on (8j's table: `dx = 2` / `dy = 2`).
- **`stage_forced`.** `AMerge` + Protocol on x, y, z + `CutBound ω` ⇒ every offered `z` token
  has `winner = ω`. This is H_CM_FORCED for the stage. The proof is by strong induction on the
  token index.
- **`free_contended_pending`** (kernel `decide` over the 38-state table): if both requests are
  high and no grant is held, then both inputs have a pending token.
- **`stage_uncontended`.** Same hypotheses ⇒ ∀ t, `x.req t ∧ y.req t → g1 t ∨ g2 t`.
- **`cut_can_fail`** (negative control): an early `y` request violates the bound.
  **`cut_quiet`**: the bound is satisfiable.

`Formal/Net/CapstoneO1Cells.lean` holds step 1 of the simulation: per-cell offer counters, as
exact identities.
- **`fork_cnt`:** `#off(in) = #off(out_i) + [in.req ∧ ¬out_i.req]`.
- **`join_cnt`:** `#off(in_i) = #off(out) + [¬out.req ∧ ¬out.ack ∧ in_i.req]`.
- **`steer_cnt`:** `#(in offers with sel = b) = #off(out b) + [j.req ∧ sel = b ∧ ¬out_b.req]`.

The link already had its counters in 8f (`link_out_le`, `link_capacity`). The arbiter's are
`zc_eq`/`offer_pending`. The mux counters are not exported; the mux is off the spine, so the
spine argument needs it only for values.

`Formal/Net/CapstoneO1.lean`, namespace `Formal.Net.CapNet.Gcd`. This is the concrete network.
- **`cell_proto`, `gcd_hw_protocol`.** Every channel obeys the 4-phase protocol from H_CELLS
  and H_BUNDLE alone. No forcing is used, because `amerge_op`'s protocol half is
  unconditional.
- **`CutOp`.** H_CUT for each operator: `CutBound` at each `.amerge x y z w`, and `True`
  elsewhere.
- **`cm_forced_of_cut`.** H_CELLS + H_BUNDLE + H_CUT(y) ⇒ 8m's `Forced` for every operator.
- **`gcd_hw_circuit_safe'`:**
  ```
  theorem gcd_hw_circuit_safe' (a b : Nat) (ch : Fin NC → Chan)
      (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
      (H_BUNDLE : ∀ c, Held (ch c))
      (H_CUT : ∃ y, Good a b y ∧ ∀ o : Fin NO, CutOp ch (omOf a b y) (opAt o)) :
      (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
      (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b))
  ```
- **`gcd_hw_arbiters_uncontended`.** Under H_CELLS, H_BUNDLE and H_CUT(y): at every arbiter
  stage, and for every grant pair meeting its gate model, both requests high implies one grant
  is held.

## Are the arbiters never contended?

**Literally, "no two requests are ever high together" (8j's H_EXCL_REQ): NO.** This is not
shown, and I expect it to be false for the circuit under the SI gate models.
- **Why.** After input `x` wins, `x.req` stays high until `x`'s producer sees `x.ack` and lowers
  it, and that delay is unbounded. Meanwhile the token runs around the loop:
  - the fork after `z` forwards it;
  - the links latch and ack it;
  - nothing on the loop waits for `x`'s return-to-zero.

  So the back edge's `y.req` can rise while `x.req` is still high.
- **Status of this claim.** It is argued, not proved. A network-level witness run would need
  O5's network run, which does not exist yet.
- **On real routes.** Whether it happens on silicon is a timing question: one LUT for the
  return-to-zero against a whole loop iteration. It probably never happens there, but no
  theorem needs it.

**What does hold: there is no free contention.** This is `stage_uncontended`.
- Whenever both requests are high, a grant is already held.
- The model's grants can rise only while the other grant and `A0` are low, and `g1` follows
  `x.req`. So the late `y` request waits behind a decided arbiter.
- By the time `A0` falls and `q` is free again, `x.req` is already low. The mutex only ever
  sees one live request when it decides.
- This is the property that liveness without bounded arbitration time needs: the fabric's
  arbiter has no metastability filter, and here it never has to resolve a race.
- It is proved conditional on H_CUT, like the forcing.

## H_CUT: the remaining hypothesis

- **What it says.** For one complete token run `y` and each of the 9 stages, the circuit has
  never offered more tokens on an arbiter input than the run consumes there up to and including
  the stage's next firing.
- **Why it is cleaner than H_CM_FORCED.** It is only about counts: it does not mention the
  arbiter's choice, and it does not mention data. It also has the shape of a safety
  simulation, "never ahead".
- **Test (GLS or board).**
  - In a routed GLS of gcd_hw, count the `req↑` events on the two inputs and the output of each
    `bdc_amerge2` stage at every time.
  - Compare them with the label stream of the token run, from C-8i's importer simulation.
  - Any time an input count exceeds the bound is a violation.
  - This needs only counters on req nets, not the arbiter's internal state.
- **Fidelity.** It is a property of the composed network, not a primitive model, so no
  fabric fidelity question arises. If O1 holds it is true of every run. It holds trivially on
  the quiet run.
- **Periodic labels after the invocation ends.** Past the last firing, `omOf` repeats with its
  period. The bound then allows one extra entry-side token. That is loose, but true, since
  sources fire once.

## What is still needed to discharge H_CUT (the plan, refined)

The single-token control spine makes the argument linear. The general "reachable cut" or
configuration machinery is not needed.

1. **The run's spine event sequence.**
   - In run `y`, the spine carries one token. Its successive visits e₀, e₁, …, e_N form a
     sequence: (spine channel, token index) pairs, totally ordered.
   - Generate this sequence from C-8i's run.
   - Map each visit to its circuit channels (link segments, `z`/`acc` buses, `jL` ghost buses)
     with a netgen extension, and kernel-check the map.
2. **Spine causality in the circuit (SPINE_CAUSAL).** If the circuit offers e_i at time r, it
   offered e_{i−1} strictly before r.
   - The proof is a per-operator lemma for each spine operator kind: fork, link, bjoin, steerC
     or steerD, arbiter stage. Each is "output offer k ⇒ the corresponding input offer
     happened earlier". The counters for these are now exported; the arbiter uses
     `offer_pending`.
   - Steer routing depends on data. The select value of each offered `j` token must equal the
     run's. That comes from a time-bounded `net_refines`, which needs forcing only for earlier
     offers.
   - So the induction is on time, jointly with forcing, as in `stage_forced`.
3. **Deriving H_CUT.** Suppose `y` had offered the token consumed by the first label-1 firing
   after `n`. That token is a spine visit later than `z`'s firing `n`. By SPINE_CAUSAL, `z`
   would already have offered `n + 1` times. Contradiction. The same argument works for `x`
   and for the cascade's `acc`.
4. **Plug in.** `gcd_hw_circuit_safe'` is unchanged; only H_CUT is discharged.

| item | estimate |
|---|---|
| spine sequence + map (generator, kernel check, memory-safe as Bool list traversals) | 0.5 day |
| per-operator spine causality (5 kinds; counters done) | 0.5 day |
| time-bounded `net_refines` + joint induction | 0.5 day |
| total | 1-1.5 days |

## Run

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    for f in CapstoneO1Stage CapstoneO1Cells CapstoneO1; do
      ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/$f.olean Formal/Net/$f.lean; done
    ../slot.sh lean Wip/C8q/Axioms.lean      # #print axioms only; proves nothing
    cd .. && ./check.sh Formal/Net/CapstoneO1Stage.lean Formal/Net/CapstoneO1Cells.lean \
      Formal/Net/CapstoneO1.lean

Result, 2026-10-27:
- `check.sh` printed `[audit] 2977 declarations checked`, `[check] OK`, in about 10 s.
- Each file takes a few seconds and stays under 1 GB.
- Axioms:
  - `free_contended_pending`: none;
  - the cell counters: propext and Quot.sound;
  - the rest: propext, Classical.choice and Quot.sound. Classical.choice enters through 8j's
    `winner`.

The lead has to add the 3 modules to `Formal.lean`; I do not own it.

## What it buys

- **Isolated the arbiter's part of O1.** The arbiters' free choice is provably never exercised,
  and their mutex is never asked to resolve two live requests. Both follow from one count-only
  hypothesis that a simulation produces directly.
- **H_EXCL_REQ is the wrong target.** It is not derivable, and probably false under SI. Liveness
  work should use "no free contention" instead.
- **Remaining obligation is precise.** It is reduced to one network-level fact, SPINE_CAUSAL,
  with its building blocks (the counters) in place.

## Fidelity of the models used

Nothing new is introduced.
- `CM.AMerge` (8j): SI, binary, grants free. It covers H_ARB, H_ARB_EXCL and H_AMERGE_RTZ
  (B's obligations).
- `Fork`, `Join`, `Steer` (8f).
- The 8m network, unchanged.
- H_CUT is a network property, not a primitive model.

## Surprises

- **8j's H_EXCL_REQ is too strong.** The circuit only needs exclusion at the moment the arbiter
  is free, and the late request is harmless because `g1` tracks `x.req`.
- **No reachable-cut construction is needed.** The bound only has to hold up to the stage's
  next firing, and the spine is one token, so a linear causality chain suffices instead of a
  general reachable cut.
- **Core `omega` failed on syntactically equal `if … = true then 1 else 0` terms** that carried
  different Decidable instances. `exact` (which checks up to defeq) closed them.
