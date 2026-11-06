import Formal.Cells.SpecCElem

/-!
# Formal.Cells.SpecLatch — a routed transparent latch closes cleanly under THE Spec semantics

Shard B, THE goal, S3 (the data-latch cell theorem; most of THE target's 4,597 storage gates are latches).

## Problem, plainly
A latch on the target is a LUT `q = en ? d : q` whose output returns through its routing to its feedback pin `j`.
Its enable `e` and data `d` pins read their source nodes through their own routes, each with a composite read
delay somewhere in `[lo i, hi i]`. When the enable closes, the reads of `e` at different output times may see it
open or closed (a skew window of width `hi e - lo e`), and while some read still sees it open the output follows
`d`; when a read sees it closed the output is the feedback read, which is stale for up to `hi j`. Shard C's
`SpecLoop.cgate_switch` needs the forcing and the confirmation windows to abut, which a skewed enable read never
gives (`hi e > lo e`). When does the latch close without a runt and hold its value, for every behaviour?

## Result (`latch_close`)
Premises: the collapsed relation (`CGateOK`) with bands; INIT facts `hopen` (enable open: output = data, after
polarity, whatever the feedback reads) and `hclosed` (enable closed: output = feedback read); other pins held.
The enable's source is open on `[τ - We, τ - 1]` and closed on `[τ, E]`; the data's source shows `v` on
`[τ - Wd, τ + hi e]`. Timing (`A` is the time from which the conclusion holds):
`τ + hi e ≤ A + We` (every read of the enable from `A` on, before the close is
read, sees it open), `τ + hi d ≤ A + Wd` (every read of the data from `A` on sees `v`), and `A + hi j ≤ τ + lo e`
(**the loop condition**: the output has shown `v` for at least the feedback's longest delay before the first read
can see the enable closed). Conclusion: `q = v` on `[A, E + lo e]`: the latch holds the data value through the
close, with no runt, until a read can see the enable reopen.

Equivalently, the enable must be open for at least `(hi e - lo e) + hi j` (skew of its own route plus the loop)
and the data must be stable from `hi d + hi j - lo e` before the close until `hi e` after it: setup, hold and minimum
pulse width, derived from the gate model rather than assumed.

## Not covered
That the network supplies these windows (the bundling obligations: C's composition, rule I's territory); the
reopening (it is the forced transparent case, `hopen`); latches whose INIT is not of this form.
-/

namespace Formal.Cells.SpecLatch

open Formal.Target Formal.Timing.SpecChain Formal.Cells.SpecFbChain

/-- **A routed latch closes cleanly and holds.** -/
theorem latch_close {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc}
    {S : Nat} {x : Beh} (hg : CGateOK p c g src arcs S x) {lo hi : Nat → Nat}
    (hb : CBands p c g.k arcs lo hi)
    {e d j : Nat} (he : e < g.k) (hd : d < g.k) (hj : j < g.k) (hed : e ≠ d) (hej : e ≠ j) (hdj : d ≠ j)
    (hfb : src j = g.out) (hloj : 1 ≤ lo j)
    (pe pd : Bool) (held : Nat → Bool) (ov : Nat → Bool)
    (hopen : ∀ v : Nat → Bool, (v e ^^ pe) = true →
      (∀ i, i < g.k → held i = true → v i = ov i) → g.init.testBit (addr g.k v) = (v d ^^ pd))
    (hclosed : ∀ v : Nat → Bool, (v e ^^ pe) = false →
      (∀ i, i < g.k → held i = true → v i = ov i) → g.init.testBit (addr g.k v) = v j)
    (hheld : ∀ i, i < g.k → held i = true → ∀ t, x (src i) t = ov i)
    (τ E We Wd A : Nat) (v : Bool)
    (hopenW : ∀ t, τ ≤ t + We → t < τ → (x (src e) t ^^ pe) = true)
    (hclosedW : ∀ t, τ ≤ t → t ≤ E → (x (src e) t ^^ pe) = false)
    (hdata : ∀ t, τ ≤ t + Wd → t ≤ τ + hi e → (x (src d) t ^^ pd) = v)
    (hAS : S ≤ A) (hAe : τ + hi e ≤ A + We) (hAd : τ + hi d ≤ A + Wd) (hloop : A + hi j ≤ τ + lo e) :
    ∀ s, A ≤ s → s ≤ E + lo e → x g.out s = v := by
  obtain ⟨F, -, hF⟩ := hg
  have hrd : ∀ t, S ≤ t → ∀ i, i < g.k → lo i ≤ t - F i t ∧ t - F i t ≤ hi i ∧ F i t ≤ t := by
    intro t ht i hi'
    obtain ⟨hr, -⟩ := hF t ht
    have h1 := hr i hi'
    exact ⟨(hb i hi' _ h1.2).1, (hb i hi' _ h1.2).2, h1.1⟩
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro hAs hsE
  obtain ⟨-, hy⟩ := hF s (by omega)
  have hheldR : ∀ i, i < g.k → held i = true → x (src i) (F i s) = ov i := fun i hi' hh => hheld i hi' hh _
  have hre := hrd s (by omega) e he
  have hrdd := hrd s (by omega) d hd
  have hrj := hrd s (by omega) j hj
  -- the data read (whenever used) sees v
  have hdv : F e s < τ → (x (src d) (F d s) ^^ pd) = v := fun h => hdata _ (by omega) (by omega)
  by_cases hcl : τ ≤ F e s
  · -- the enable read sees it closed: the output is the feedback read, which is v by induction
    have hcr : (x (src e) (F e s) ^^ pe) = false := hclosedW _ hcl (by omega)
    rw [hy, hclosed _ hcr hheldR, hfb]
    exact ih (F j s) (by omega) (by omega) (by omega)
  · -- the enable read sees it open: the output is the data read
    have hor : (x (src e) (F e s) ^^ pe) = true := hopenW _ (by omega) (by omega)
    rw [hy, hopen _ hor hheldR]
    exact hdv (by omega)

end Formal.Cells.SpecLatch
