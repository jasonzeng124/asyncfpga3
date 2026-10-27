# C-8k: the gcd_hw C function is Nat.gcd on [0, 2^31)^2; the bdc gcd graph outputs Nat.gcd and every run finishes

## Verdict

**Works.** Core Lean only, no sorry / axiom / native_decide. All three goals of the probe are proved:

1. H_NONNEG31, the open goal of C-8i, with an explicit logarithmic fuel bound.
2. The combined corollary. For every 0 <= a, b < 2^31, every complete run of the gcd graph that bdc
   emits for gcd_hw ends with exactly `[Nat.gcd a b]` on `out0`.
3. Token-level liveness for those inputs. There is no infinite run. All runs are bounded by one `N`.
   Every partial run can be completed, and every maximal run is complete and correct. No fairness
   assumption is needed.

The work took about 1 h, much less than the time box.

## Files and run command

| file | what |
|---|---|
| `formal/lean/Formal/Net/GcdHwNat.lean` | i32 per-op lemmas, loop lemmas, `gcdC_fuel`, `gcdC_nonneg31_96`, `gcdC_nonneg31` |
| `formal/lean/Formal/Net/GcdHwLive.lean` | graph corollary `gcd_hw_graph_computes_gcd`, and the liveness theorems |

```
cd formal && ./check.sh Formal/Net/GcdHwNat.lean Formal/Net/GcdHwLive.lean
# [audit] 1109 declarations checked / [check] OK, 12 s total
```

Each file compiles in about 3 s and under 1 GB. The files depend on the C-8i oleans (GcdHwLib, GcdHw,
GcdHwSeg, GcdHwProof) and on 8b's KahnGcd. Build order: GcdHwNat, then GcdHwLive.
`Formal.lean` and `check.sh` still need the two modules added by the lead; I do not own them.
`Wip/C8i/Nonneg31.lean` is C-8i's file, so I left it untouched. Its `sorry` statement is now
`Formal.Net.GcdHw.Gcd.gcdC_nonneg31`, with exactly the same statement.

## Theorems (namespace `Formal.Net.GcdHw.Gcd`)

* Per-op, on values below 2^31:
  * `shrsi1`: `shrsi 32 x 1 = x/2`
  * `eq0`: `x == 0`
  * `cEv_iff`: the bb2/bb3 condition means both are even
  * `slt1`: `x < 1` means `x = 0`
  * `cSc_iff`: the strip exit condition means `x` is odd or `x = 0`
  * `absd_eq`: `absd` equals 8b's `absdiff`
  * `minC_eq`: `minC` equals `min`
  * `shli_eq`: `shli` does not wrap while `r * 2^k < 2^32`
  * `addi1`
* Loops, against 8b's transcription (`Formal.Net.Kahn.Gcd`):
  * `strip_eq` / `strip_fuel`: strip is `strip2` for fuel 32 or more
  * `loop3_eq`: bb3 is `shared`
  * `shared_bound`: a new lemma; `shared` only divides out the factor it counts
  * `main_eq`: the main loop returns `gcd` when `a * b < 2^n` and the fuel is at least `n + 33`
* `gcdC_fuel`: if `a, b < 2^31` and `fuel >= fuelBound a b = log2(a*b) + 34`, then
  `gcdC fuel a b = some (Nat.gcd a b)`. This holds for every fuel above the bound.
* `gcdC_nonneg31_96`: fuel 96 is enough for every input, because `a*b < 2^62`.
* `gcdC_nonneg31`: C-8i's stated goal, with fuel `a + b + 64`.
* `gcd_hw_graph_computes_gcd` (assumes `a, b < 2^31`):
  * a complete run exists;
  * every complete run, under any schedule and any arbitration of the 8 multi-input
    control_merges, ends in `final (Nat.gcd a b)`, the store with `[gcd]` on `out0`, `[0]` on
    `end`, and nothing else;
  * all runs are bounded.
* `gcd_hw_graph_live`: every partial run can be extended to `final (gcd)`. Every completion from it
  ends there, after the same number of firings.
* `gcd_hw_graph_bounded`: there is one `N` that bounds every run.
* `gcd_hw_graph_no_infinite_run`: there is no infinite firing sequence from the initial store.
* `gcd_hw_graph_maximal`: a run that stops (nothing is enabled) has `[Nat.gcd a b]` on `out0`.

## How

* **Reuse of 8b.** I did not prove the two transcriptions equal as whole functions; 8b's `gcdC` has
  fuel only on its main loop, and its shape differs. Instead each loop of the C-8i transcription is
  proved equal to the matching 8b function: `shared` for bb3 and `strip2` for the strips. 8b's
  arithmetic lemmas then close the proof: `gcd_strip2`, `strip2_odd`, `strip2_pos`, `strip2_le`,
  `shared_spec` and `gcd_strip2_both`. The main loops differ structurally. C-8i's `mainLoop` is a
  do-while: it strips, then tests the stripped difference. 8b's `cLoop` tests `a` first. So
  `main_eq` is proved directly, using the same lemmas.
* **Fuel bound.**
  * Every value stays below 2^31, so each strip takes at most 32 steps (`strip_eq`, by induction
    on `x < 2^f`).
  * In the main loop, `a` and `b` are odd and the difference `d` is even, so `strip2 d <= d/2`.
    Since `d * min(a, b) < a * b`, the product `x * m` of the new pair is less than half of `a * b`.
  * So the iteration count is at most `log2(a*b) + 1`. The inner strip of each iteration needs
    another 32 of the shared fuel, which gives `+34`.
  * `Nat.lt_log2_self` and `Nat.log2_lt` (core) convert between `log2` and powers.
* **Liveness.**
  * C-8i proved the spine invariant closed (`closed_of_check`) and the diamond property
    (`wfOn_diamond (wfOn_of_check ...)`).
  * 8b's `prefix_run` turns these, plus one terminating run from `reach_gcdC`, into "every
    partial run can be completed to the same terminal store".
  * Infinite runs are excluded by the uniform bound from `no_longer`: an infinite sequence would
    yield a run of length `N + 1`.
  * This is liveness under *every* scheduler, fair or not, because the system is confluent and
    bounded. No fairness hypothesis appears anywhere.
* **Memory.** Kernel `decide` is never applied to a symbolic i32 term. Literal powers are
  normalised with `Nat.reducePow` and closed by `omega`. One trap is worth recording for reuse:
  after rewriting `flip 32 x` to `x + 2^31`, the closing `rfl` of `rw` tries to evaluate
  `decide (x + 2^31 < 1 + 2^31)` and hits max recursion. The fix is to do the step with
  `simp only` and a `have e : decide (...) = ...` instead of `rw`.

## Hypotheses and fidelity

Nothing new is modelled here. The primitive models are C-8i's, unchanged: `Ops.*` at bdc's Verilog
semantics, unbounded FIFO channels at token level, and H_SOURCE_ETERNAL for the 4 source chains.
H_ONE_INVOCATION is proved from the initial store. The C-8i notes give the fidelity of each.

The input range `a, b < 2^31`, i.e. non-negative i32, is a hypothesis of the theorem statements, not
a model assumption. It cannot be dropped: (-6, 4) loops forever in the C (C-8i #eval), and by C-8i
the graph does too.

Liveness here is token-level only. Hardware liveness (handshake progress, finite link capacity, no
metastable arbiter hang) is the track-8a gap listed in C-8b and C-8i.

## What does not work / open

* Nothing open within the probe's scope.
* Not done: liveness and correctness for negative inputs. The function is genuinely non-terminating
  there.
* Not done: the BitVec equality of `Ops` (C-8i lists it, about 1 h).
* Not done: capacity-bounded channels. KahnBounded transfers determinacy, but not liveness, because
  a bounded run can deadlock where the unbounded one cannot. That would need the schedule to fit
  the capacities.

## What it buys the project

This is the first end-to-end token-level statement for a real bdc-compiled kernel. The graph is
generated from bdc's own code, from Dynamatic's gcd fixture. For all non-negative i32 inputs:

* every schedule and arbitration terminates;
* none deadlocks;
* the output is exactly `[Nat.gcd a b]`.

This is the token-level half of the Phase 3 capstone theorem.

## Decisions taken (no one to ask)

* I stated the fuel bound as `log2(a*b) + 34` rather than `O(log a + log b)` in two terms;
  `log2(a*b) <= log2 a + log2 b + 1`, so it is the same order. I also proved the constant bound 96.
* I proved `gcdC_nonneg31` with C-8i's exact statement, so the lead can delete the Wip `sorry` file
  or point it at this theorem.
* I put the corollary and the liveness theorems in one file, `GcdHwLive.lean`, because both are
  short.
