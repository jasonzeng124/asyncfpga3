import Formal.Cells.ArbClean
import Formal.Cells.SpecFbChain

/-!
# Formal.Cells.ArbCleanChain — a separated arbitration, with the state LUT's feedback through the routing

Shard B, THE goal, S3/H_ARB. `ArbClean.q_clean_set_gen` (a separated arbitration is decided by the gate relation
alone, no H_ARB) assumes the state LUT's feedback pin reads its own output node directly. On the decoded targets
the feedback runs through copy gates. This file restates it for shard C's collapsed relation `SpecChain.CGateOK`
(pins read SOURCE nodes through copy chains with summed admissible delays), using `SpecFbChain.cfb_switch`.

## Problem, plainly
If arbiter state LUT `q` sees r1 high, r2 low, reset low and A0 low (its set condition) at its pins' sources for at
least its routed feedback delay's upper bound, and r1 stays high (reset low) afterwards, does q go to 1 and stay 1,
whatever r2 and A0 do afterwards -- for every behaviour, with every copy gate on the feedback route reading at its
own admissible delay?

## Result
`cq_clean_set_gen`: yes, with the two table facts (`hset`, `hconf`, decided per gate by `ArbClean.setFact`/
`confFact`, e.g. `ArbCleanPS.targetQPS_facts`) and `CBands` on the composite delays (e.g. from
`SpecFbChain.cbands_of_sums`).

## Not covered
That each arbitration of the target IS separated by that much in every behaviour (simulation only: >= 49.9 ns on
gcd_ps, JOURNAL-B); the collapse itself is C's `SpecChain.collapse` (needs the chain data per gate).
-/

namespace Formal.Cells.ArbCleanChain

open Formal.Target Formal.Timing.SpecChain Formal.Cells.SpecFbChain
open Formal.Cells.ArbClean (Roles OnReads)

theorem cvisible_val {x : Beh} {k : Nat} {src : Nat → Nat} {lo hi : Nat → Nat} {j t : Nat} {v : Nat → Bool}
    (hv : CVisible x k src lo hi j t v) {i : Nat} (hi' : i < k) (hij : i ≠ j) {b : Bool} {s e : Nat}
    (hst : s ≤ t) (hte : t ≤ e) (h : OnReads x lo hi i (src i) b s e) : v i = b := by
  obtain ⟨u, h1, h2, h3⟩ := hv i hi' hij
  rw [h3]; exact h t u hst hte h1 h2

/-- **Clean set through a routed feedback, any pin order.** -/
theorem cq_clean_set_gen {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc}
    {S : Nat} {x : Beh} (hg : CGateOK p c g src arcs S x) (R : Roles)
    (hk : R.r1 < g.k ∧ R.r2 < g.k ∧ R.fb < g.k ∧ R.rst < g.k ∧ R.a0 < g.k)
    (hne : R.r1 ≠ R.fb ∧ R.r2 ≠ R.fb ∧ R.rst ≠ R.fb ∧ R.a0 ≠ R.fb)
    (htk : ∀ jb ∈ R.tied, jb.1 < g.k ∧ jb.1 ≠ R.fb)
    (hset : ∀ v : Nat → Bool, v R.r1 = true → v R.r2 = false → v R.rst = false → v R.a0 = false →
      (∀ jb ∈ R.tied, v jb.1 = jb.2) → g.init.testBit (addr g.k v) = true)
    (hconf : ∀ v : Nat → Bool, v R.r1 = true → v R.fb = true → v R.rst = false →
      (∀ jb ∈ R.tied, v jb.1 = jb.2) → g.init.testBit (addr g.k v) = true)
    (hfb : src R.fb = g.out)
    {lo hi : Nat → Nat} (hb : CBands p c g.k arcs lo hi) (hlo : 1 ≤ lo R.fb) {s e e' : Nat}
    (hs : S ≤ s) (hlong : s + hi R.fb ≤ e + 1) (hee : e ≤ e')
    (htied : ∀ jb ∈ R.tied, OnReads x lo hi jb.1 (src jb.1) jb.2 s e')
    (hr1 : OnReads x lo hi R.r1 (src R.r1) true s e')
    (hr2 : OnReads x lo hi R.r2 (src R.r2) false s e)
    (hrs : OnReads x lo hi R.rst (src R.rst) false s e')
    (ha0 : OnReads x lo hi R.a0 (src R.a0) false s e) :
    ∀ t, s ≤ t → t ≤ e' → x g.out t = true := by
  apply cfb_switch hg hb (j := R.fb) hk.2.2.1 hfb hlo hs hlong
  · intro t h1 h2 v hv
    exact hset v (cvisible_val hv hk.1 hne.1 h1 (by omega) hr1)
      (cvisible_val hv hk.2.1 hne.2.1 h1 h2 hr2)
      (cvisible_val hv hk.2.2.2.1 hne.2.2.1 h1 (by omega) hrs)
      (cvisible_val hv hk.2.2.2.2 hne.2.2.2 h1 h2 ha0)
      (fun jb hj => cvisible_val hv (htk jb hj).1 (htk jb hj).2 h1 (by omega) (htied jb hj))
  · intro t h1 h2 v hv2 hv
    exact hconf v (cvisible_val hv hk.1 hne.1 (by omega) h2 hr1) hv2
      (cvisible_val hv hk.2.2.2.1 hne.2.2.1 (by omega) h2 hrs)
      (fun jb hj => cvisible_val hv (htk jb hj).1 (htk jb hj).2 (by omega) h2 (htied jb hj))

end Formal.Cells.ArbCleanChain
