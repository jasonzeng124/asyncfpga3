import Formal.Net.TimedBridge

/-!
# Every corner from the two extreme corners (shard C, instance support)

**Problem, plainly.** `Spec.Behaves` lets each behaviour pick its own corner `c ∈ [0,1]`, so the timed net's integer
bounds (`TimedBridge.loC`/`hiC`, summed along routes) depend on `c`, and so do the skew obligations: infinitely many
checks. The exact (rational) window ends are affine in `c`, and the integer bounds lie inside them.

**Proved:** `sumLoC_ge`/`sumHiC_le` (the integer route bounds are within the rational sums `rlo`/`rhi`), `affine_01`
(an inequality between affine functions of `c` that holds at `c = 0` and `c = 1` holds on `[0,1]`), and
`skew_all_corners`: if `Σ rhi(route b) ≤ Σ rlo(route a) + Σ rlo(path)` (all rational sums) holds at both extreme
corners, then at every corner the integer form `sumHiC b ≤ sumLoC a + sumLoC path` holds, which is the shape of a
`TO` row whose separation is a sum of lower bounds along a path.

**Not shown here:** any instance.
-/

namespace Formal.Net.OccNet.Corner
open Formal.Target Formal.Net.OccNet.Bridge

def rlo (p : DelayPar) (c : ℚ) (es : List Arc) : ℚ := (es.map fun e => (1 - p.κ) * lerp e.fmin e.smin c / p.g).sum
def rhi (p : DelayPar) (c : ℚ) (es : List Arc) : ℚ := (es.map fun e => (1 + p.κ) * lerp e.fmax e.smax c * p.g).sum

theorem sumLoC_ge (p : DelayPar) (c : ℚ) : ∀ es : List Arc, rlo p c es ≤ (sumLoC p c es : ℚ)
  | [] => by simp [rlo, sumLoC]
  | e :: es => by
    have ih := sumLoC_ge p c es
    simp only [rlo, sumLoC, List.map_cons, List.sum_cons] at ih ⊢
    push_cast
    have h1 : (1 - p.κ) * lerp e.fmin e.smin c / p.g ≤ ((loC p c e : ℕ) : ℚ) := by
      unfold loC
      have := Int.le_ceil ((1 - p.κ) * lerp e.fmin e.smin c / p.g)
      have h2 : ((⌈(1 - p.κ) * lerp e.fmin e.smin c / p.g⌉.toNat : ℕ) : ℤ) ≥ ⌈(1 - p.κ) * lerp e.fmin e.smin c / p.g⌉ :=
        Int.self_le_toNat _
      have h3 : ((⌈(1 - p.κ) * lerp e.fmin e.smin c / p.g⌉ : ℤ) : ℚ) ≤
          (((⌈(1 - p.κ) * lerp e.fmin e.smin c / p.g⌉.toNat : ℕ) : ℤ) : ℚ) := by exact_mod_cast h2
      push_cast at h3
      linarith
    linarith

theorem sumHiC_le (p : DelayPar) (c : ℚ) (hpos : ∀ es : List Arc, ∀ e ∈ es, 0 ≤ (1 + p.κ) * lerp e.fmax e.smax c * p.g) :
    ∀ es : List Arc, (sumHiC p c es : ℚ) ≤ rhi p c es
  | [] => by simp [rhi, sumHiC]
  | e :: es => by
    have ih := sumHiC_le p c hpos es
    simp only [rhi, sumHiC, List.map_cons, List.sum_cons] at ih ⊢
    push_cast
    have h0 := hpos (e :: es) e (by simp)
    have h1 : ((hiC p c e : ℕ) : ℚ) ≤ (1 + p.κ) * lerp e.fmax e.smax c * p.g := by
      unfold hiC
      have hf := Int.floor_le ((1 + p.κ) * lerp e.fmax e.smax c * p.g)
      have hnn : 0 ≤ ⌊(1 + p.κ) * lerp e.fmax e.smax c * p.g⌋ := Int.floor_nonneg.mpr h0
      have h2 : ((⌊(1 + p.κ) * lerp e.fmax e.smax c * p.g⌋.toNat : ℕ) : ℤ) = ⌊(1 + p.κ) * lerp e.fmax e.smax c * p.g⌋ :=
        Int.toNat_of_nonneg hnn
      have h3 : (((⌊(1 + p.κ) * lerp e.fmax e.smax c * p.g⌋.toNat : ℕ) : ℤ) : ℚ) =
          ((⌊(1 + p.κ) * lerp e.fmax e.smax c * p.g⌋ : ℤ) : ℚ) := by rw [h2]
      push_cast at h3
      linarith
    linarith

theorem lerp_affine (a b : ℕ) (c : ℚ) : lerp a b c = (1 - c) * lerp a b 0 + c * lerp a b 1 := by
  unfold lerp; ring

theorem rlo_affine (p : DelayPar) (c : ℚ) : ∀ es : List Arc, rlo p c es = (1 - c) * rlo p 0 es + c * rlo p 1 es
  | [] => by simp [rlo]
  | e :: es => by
    have ih := rlo_affine p c es
    simp only [rlo, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, lerp_affine e.fmin e.smin c]
    ring

theorem rhi_affine (p : DelayPar) (c : ℚ) : ∀ es : List Arc, rhi p c es = (1 - c) * rhi p 0 es + c * rhi p 1 es
  | [] => by simp [rhi]
  | e :: es => by
    have ih := rhi_affine p c es
    simp only [rhi, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, lerp_affine e.fmax e.smax c]
    ring

/-- **Two corners give all.** -/
theorem affine_01 {f g : ℚ → ℚ} (hf : ∀ c, f c = (1 - c) * f 0 + c * f 1) (hg : ∀ c, g c = (1 - c) * g 0 + c * g 1)
    (h0 : f 0 ≤ g 0) (h1 : f 1 ≤ g 1) (c : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : f c ≤ g c := by
  rw [hf c, hg c]; nlinarith

/-- **A skew row at every corner from the two extreme corners.** -/
theorem skew_all_corners (p : DelayPar) (hk : 0 ≤ p.κ) (hg : 0 < p.g) (rb ra path : List Arc)
    (hord : ∀ e ∈ rb, e.fmax ≤ e.smax)
    (h0 : rhi p 0 rb ≤ rlo p 0 ra + rlo p 0 path) (h1 : rhi p 1 rb ≤ rlo p 1 ra + rlo p 1 path)
    (c : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    sumHiC p c rb ≤ sumLoC p c ra + sumLoC p c path := by
  have hpos : ∀ es : List Arc, ∀ e ∈ es, 0 ≤ (1 + p.κ) * lerp e.fmax e.smax c * p.g := by
    intro es e _
    unfold lerp
    have : (0 : ℚ) ≤ (1 - c) * e.fmax + c * e.smax := by
      have := (Nat.cast_nonneg e.fmax : (0 : ℚ) ≤ e.fmax)
      have := (Nat.cast_nonneg e.smax : (0 : ℚ) ≤ e.smax)
      nlinarith
    have : (0 : ℚ) ≤ 1 + p.κ := by linarith
    positivity
  have hA := affine_01 (f := fun c => rhi p c rb) (g := fun c => rlo p c ra + rlo p c path)
    (fun c => rhi_affine p c rb) (fun c => by rw [rlo_affine p c ra, rlo_affine p c path]; ring)
    h0 h1 c hc0 hc1
  have e1 := sumHiC_le p c hpos rb
  have e2 := sumLoC_ge p c ra
  have e3 := sumLoC_ge p c path
  have : ((sumHiC p c rb : ℕ) : ℚ) ≤ ((sumLoC p c ra + sumLoC p c path : ℕ) : ℚ) := by
    push_cast; linarith
  exact_mod_cast this

end Formal.Net.OccNet.Corner
