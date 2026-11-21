import Formal.Cells.SpecLatch

/-!
# Formal.Cells.SpecLatchSep — a latch's enable-width window from its controller's toggle separation

Shard B, THE goal, S3 → S4 (one composition step inside a link stage). On THE target every latch's enable source is
a link controller C-element (all 4,185 latches of LatchViewPS; tools-B check), and `SpecCElem.celem_forced'` /
`CElemView.target_celem_forced` conclude that its toggles are at least `M` apart. `sep_const`: a signal with no
toggle in `(τ - M, τ)` is constant on `[τ - M, τ - 1]`. `latch_close_sep`: `SpecLatch.latch_close` with the
enable-open premise replaced by "the enable source toggles to closed at `τ` and did not toggle in `(τ - M, τ)`"
(We := M). So the latch's minimum-width condition `τ + hi e ≤ A + M` (with `A + hi j ≤ τ + lo e`) is met whenever
the controller's separation `M ≥ (hi e - lo e) + hi j`: it follows from the controller's own cell theorem, leaving
only the data windows (bundling) as the latch's environment premise.
-/

namespace Formal.Cells.SpecLatchSep

open Formal.Target Formal.Timing.SpecChain Formal.Cells.SpecFbChain Formal.Cells.SpecCElem Formal.Cells.SpecLatch

theorem sep_const (s : Sig) (τ M : Nat) (hsep : ∀ u, u < τ → τ < u + M → ¬ Tog s u) :
    ∀ t, τ ≤ t + M → t < τ → s t = s (τ - 1) := by
  intro t h1 h2
  by_contra hne
  obtain ⟨u, hu1, hu2, hu3⟩ := tog_between s (a := t) (b := τ - 1) (by omega) hne
  exact hsep u (by omega) (by omega) hu3

/-- **Latch close with the enable width taken from the enable source's toggle separation.** -/
theorem latch_close_sep {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc}
    {S : Nat} {x : Beh} (hg : CGateOK p c g src arcs S x) {lo hi : Nat → Nat}
    (hb : CBands p c g.k arcs lo hi)
    {e d j : Nat} (he : e < g.k) (hd : d < g.k) (hj : j < g.k) (hed : e ≠ d) (hej : e ≠ j) (hdj : d ≠ j)
    (hfb : src j = g.out) (hloj : 1 ≤ lo j)
    (pe pd : Bool) (held : Nat → Bool) (ov : Nat → Bool)
    (hopen : ∀ v : Nat → Bool, (v e ^^ pe) = true →
      (∀ i, i < g.k → held i = true → v i = ov i) → g.init.testBit (addr g.k v) = (v d ^^ pd))
    (hclosed : ∀ v : Nat → Bool, (v e ^^ pe) = false →
      (∀ i, i < g.k → held i = true → v i = ov i) → g.init.testBit (addr g.k v) = v j)
    (τ E M Wd A H : Nat) (v : Bool) (hH : ∀ i, i < g.k → hi i ≤ H)
    (hheld : ∀ i, i < g.k → held i = true → ∀ t, A ≤ t + H → x (src i) t = ov i)
    (hτ : (x (src e) (τ - 1) ^^ pe) = true)
    (hsep : ∀ u, u < τ → τ < u + M → ¬ Tog (x (src e)) u)
    (hclosedW : ∀ t, τ ≤ t → t ≤ E → (x (src e) t ^^ pe) = false)
    (hdata : ∀ t, τ ≤ t + Wd → t ≤ τ + hi e → (x (src d) t ^^ pd) = v)
    (hAS : S ≤ A) (hAe : τ + hi e ≤ A + M) (hAd : τ + hi d ≤ A + Wd) (hloop : A + hi j ≤ τ + lo e) :
    ∀ s, A ≤ s → s ≤ E + lo e → x g.out s = v :=
  latch_close hg hb he hd hj hed hej hdj hfb hloj pe pd held ov hopen hclosed τ E M Wd A H v hH hheld
    (fun t h1 h2 => by rw [sep_const _ τ M hsep t h1 h2]; exact hτ) hclosedW hdata hAS hAe hAd hloop

end Formal.Cells.SpecLatchSep
