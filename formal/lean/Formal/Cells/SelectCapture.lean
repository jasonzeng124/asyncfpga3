import Formal.Cells.ForceTree
import Formal.Cells.LatchHoldPin

/-!
# Formal.Cells.SelectCapture — a latch capturing through a select mux, every delay in the band (shard B, 2026-11-15)

**Problem, plainly.** (PROGRAM.md 2026-11-15, item 4.) A bundled-data latch bit (`bd_latch`: a LUT with enable
pin `e`, data pin `d`, feedback pin `j`) captures a value that reaches its data pin through combinational LUTs,
e.g. `bd_datamux` (`z = s ? y : x`) whose select `s` and inputs `x`, `y` are launched by other controllers. When
is the captured value correct for EVERY delay assignment the band allows, glitches included?

**Proved.**
* `select_capture`: take a forcing tree for the data pin's source `m` (`ForceTree.force_tree`: per-node windows,
  each LUT forced by a subset of its pins, e.g. the select and the selected input) with roots that hold their
  values on their windows. If, at the latch,
  - **(setup, research's rule I)** `a m + Wd ≤ τ`: the data pin's source shows its new value from `Wd` before the
    close event `τ` (the first time the enable source shows "closed"), and
  - **(hold, research's rule H)** `τ + hi e ≤ b m + lo d + 1`: it keeps that value until the slowest possible
    close at the LUT (`τ + hi e`) minus the fastest data-pin route (`lo d`),
  plus `latch_close_pin`'s own premises (enable open before τ for `We`, closed on `[τ, E]`, the loop inequality
  `A + hi j ≤ τ + lo e`, held side pins), then the latch output is `val m ⊕ pd` on `[A, E + lo e]`.
  Glitches on the mux's unforced pins (the deselected input) and on the select before `a` or after `b` are
  covered: nothing is assumed about them.

**Not shown.** That a real build's select links meet the window inequalities (the windows of the roots come from
chain certificates on the controllers, `LatchHoldCert`, or from quietness; no row emitted yet); completeness.
-/

namespace Formal.Cells.SelectCapture
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecLoop Formal.Timing.Island
  Formal.Cells.ForceTree Formal.Cells.LatchHoldPin Formal.Cells.SpecFbChain

/-- **A latch bit captures through a forcing tree.** -/
theorem select_capture {p : DelayPar} {c : ℚ} {x : Beh}
    -- the forcing tree feeding the data pin
    (comb root : Nat → Prop) (ρ : Nat → Nat) (gate : Nat → Gate) (srcT : Nat → Nat → Nat)
    (arcsT : Nat → Nat → List Arc) (ST : Nat → Nat) (val : Nat → Bool) (ps : Nat → List Nat)
    (L U : Nat → Nat → Nat) (a b : Nat → Nat)
    (hgT : ∀ w, comb w → (gate w).out = w ∧ CGateOK p c (gate w) (srcT w) (arcsT w) (ST w) x)
    (hLU : ∀ w, comb w → ∀ j, j < (gate w).k → ∀ D, SumAdm p c (arcsT w j) D → L w j ≤ D ∧ D ≤ U w j)
    (hF : ∀ w, comb w → ForcesP (gate w).k (gate w).init (asgOf srcT val w (ps w)) (val w) = true)
    (hps : ∀ w, comb w → ∀ j ∈ ps w, j < (gate w).k ∧
      (root (srcT w j) ∨ (comb (srcT w j) ∧ ρ (srcT w j) < ρ w)))
    (hwin : ∀ w, comb w → ∀ j ∈ ps w, a (srcT w j) + U w j ≤ a w ∧ b w ≤ b (srcT w j) + L w j)
    (hST : ∀ w, comb w → ST w ≤ a w)
    (hroot : ∀ r, root r → ∀ t, a r ≤ t → t ≤ b r → x r t = val r)
    -- the latch
    {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat} (hg : CGateOK p c g src arcs S x)
    {lo hi : Nat → Nat} (hb : CBands p c g.k arcs lo hi)
    {e d j : Nat} (he : e < g.k) (hd : d < g.k) (hj : j < g.k) (hed : e ≠ d) (hej : e ≠ j) (hdj : d ≠ j)
    (hfb : src j = g.out) (hloj : 1 ≤ lo j)
    (pe pd : Bool) (held : Nat → Bool) (ov : Nat → Bool)
    (hopen : ∀ v : Nat → Bool, (v e ^^ pe) = true →
      (∀ i, i < g.k → held i = true → v i = ov i) → g.init.testBit (addr g.k v) = (v d ^^ pd))
    (hclosed : ∀ v : Nat → Bool, (v e ^^ pe) = false →
      (∀ i, i < g.k → held i = true → v i = ov i) → g.init.testBit (addr g.k v) = v j)
    (τ E We Wd A H : Nat) (hH : ∀ i, i < g.k → hi i ≤ H)
    (hheld : ∀ i, i < g.k → held i = true → ∀ t, A ≤ t + H → x (src i) t = ov i)
    (hopenW : ∀ t, τ ≤ t + We → t < τ → (x (src e) t ^^ pe) = true)
    (hclosedW : ∀ t, τ ≤ t → t ≤ E → (x (src e) t ^^ pe) = false)
    (hAS : S ≤ A) (hAe : τ + hi e ≤ A + We) (hAd : τ + hi d ≤ A + Wd) (hloop : A + hi j ≤ τ + lo e)
    -- the select race, both sides
    (hm : comb (src d))
    (hsetup : a (src d) + Wd ≤ τ) (hhold : τ + hi e ≤ b (src d) + lo d + 1) :
    ∀ s, A ≤ s → s ≤ E + lo e → x g.out s = (val (src d) ^^ pd) := by
  have hT := force_tree comb root ρ gate srcT arcsT ST val ps L U a b hgT hLU hF hps hwin hST hroot
  refine latch_close_pin hg hb he hd hj hed hej hdj hfb hloj pe pd held ov hopen hclosed τ E We Wd A H _ hH
    hheld hopenW hclosedW ?_ hAS hAe hAd hloop
  intro t h1 h2
  rw [hT (src d) hm t (by omega) (by omega)]

end Formal.Cells.SelectCapture
