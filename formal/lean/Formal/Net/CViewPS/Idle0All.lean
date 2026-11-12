import Formal.Net.CViewPS.Idle0P1

/-!
# Zero pairs, for every guard and scatter (shard C)

**Problem, plainly.** `correct_n0_p1` is THE theorem's conclusion for zero pairs at `g = 1, κ = 0`.
The theorem's value is the set of `(g, κ)` for which it holds. **Proved** (`correct_n0_all`): for
every `p` with `0 ≤ κ < 1` and `0 < g`, every reset `R ≥ C·A1 + 87·C·M1 + 1` where
`C = ⌈(1+κ)·g⌉` (A1 = 15,600 ps, M1 = 3,881 ps), every behaviour of THE theorem's circuit at `p`
with an environment obeying `Env` for `n = some 0` satisfies `Correct`. Every upper delay bound
scales by at most `C` (`dmax_le`, `start_le`, ...), and every forcing pin keeps a fast delay of
at least 1 ps while `κ < 1` (`dmin_pos`). So for zero pairs the `(g, κ)` frontier is everything with
`κ < 1`, given a reset that long. (At `κ = 1` the lower window collapses to 0 and the island
argument needs a delay ≥ 1 ps.)
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop
  Formal.Timing.Island

def Cp (p : DelayPar) : Nat := (⌈(1 + p.κ) * p.g⌉).toNat

theorem dmax_le {p : DelayPar} (hp : Sane p) (e : Arc) : dmax p e ≤ Cp p * e.smax := by
  obtain ⟨hk0, hk1, hg⟩ := hp
  unfold dmax Cp
  have h1 : (1 + p.κ) * (e.smax : ℚ) * p.g ≤ ((⌈(1 + p.κ) * p.g⌉ : ℤ) : ℚ) * e.smax := by
    have := Int.le_ceil ((1 + p.κ) * p.g)
    have hs : (0 : ℚ) ≤ e.smax := by positivity
    nlinarith
  have h2 : ⌈(1 + p.κ) * (e.smax : ℚ) * p.g⌉ ≤ ⌈(1 + p.κ) * p.g⌉ * (e.smax : ℤ) := by
    apply Int.ceil_le.mpr; push_cast; exact h1
  have h3 : 0 ≤ ⌈(1 + p.κ) * p.g⌉ := Int.ceil_nonneg (by positivity)
  rw [Int.toNat_le]; push_cast; rw [Int.toNat_of_nonneg h3]; exact h2

theorem dmin_pos {p : DelayPar} (hp : Sane p) (hk : p.κ < 1) (e : Arc) (h : 1 ≤ e.fmin) : 1 ≤ dmin p e := by
  obtain ⟨hk0, hk1, hg⟩ := hp
  unfold dmin
  have hf : (1 : ℚ) ≤ e.fmin := by exact_mod_cast h
  have : 0 < (1 - p.κ) * (e.fmin : ℚ) / p.g := by
    apply div_pos _ hg; nlinarith
  have h2 : 0 < ⌈(1 - p.κ) * (e.fmin : ℚ) / p.g⌉ := Int.ceil_pos.mpr this
  omega

theorem rat_ceil_eq (q : ℚ) : Rat.ceil q = ⌈q⌉ := by
  rw [Rat.ceil_eq_neg_floor_neg]; rfl

theorem start_le {p : DelayPar} (hp : Sane p) (g : Gate) : g.start p ≤ Cp p * startN g := by
  unfold Gate.start startN
  induction g.arcs with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.foldr_cons]
    have h1 : (Rat.ceil ((1 + p.κ) * e.smax * p.g)).toNat ≤ Cp p * e.smax := by
      rw [rat_ceil_eq]; exact dmax_le hp e
    rw [← Nat.mul_max_mul_left]
    exact max_le_max h1 ih

theorem sumMax_le {p : DelayPar} (hp : Sane p) : ∀ es : List Arc, sumMax p es ≤ Cp p * sumMaxN es
  | [] => by simp [sumMax, sumMaxN]
  | e :: es => by
    have := sumMax_le hp es
    have h1 := dmax_le hp e
    simp only [sumMax, sumMaxN, List.map_cons, List.sum_cons] at this ⊢
    rw [Nat.mul_add]; omega

theorem sumMin_pos {p : DelayPar} (hp : Sane p) (hk : p.κ < 1) : ∀ es : List Arc, 1 ≤ sumMinN es → 1 ≤ sumMin p es
  | [] => by simp [sumMinN]
  | e :: es => by
    intro h
    simp only [sumMin, sumMinN, List.map_cons, List.sum_cons] at h ⊢
    by_cases he : 1 ≤ e.fmin
    · have := dmin_pos hp hk e he; omega
    · have := sumMin_pos hp hk es (by simp only [sumMinN]; omega)
      simp only [sumMin] at this; omega

theorem chainStart_le {p : DelayPar} (hp : Sane p) : ∀ cs : List Gate, chainStart p cs ≤ Cp p * chainStartN cs
  | [] => by simp [chainStart, chainStartN]
  | c :: cs => by
    have := chainStart_le hp cs
    have h1 := start_le hp c
    have h2 := dmax_le hp (arc0 c)
    simp only [chainStart, chainStartN]
    rw [Nat.mul_add, Nat.mul_add]; omega

theorem cStart_le {p : DelayPar} (hp : Sane p) (g : Gate) (pcs : List PinChain) :
    cStart p g pcs ≤ Cp p * cStartN g pcs := by
  unfold cStart cStartN
  rw [Nat.mul_add]
  have h1 := start_le hp g
  suffices h : ((List.range g.k).map fun i =>
      chainStart p (pcs.getD i ⟨0, []⟩).chain + dmax p (g.arcs.getD i default)).sum ≤
      Cp p * ((List.range g.k).map fun i =>
        chainStartN (pcs.getD i ⟨0, []⟩).chain + (g.arcs.getD i default).smax).sum by omega
  generalize List.range g.k = L
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    have := chainStart_le hp (pcs.getD i ⟨0, []⟩).chain
    have := dmax_le hp (g.arcs.getD i default)
    omega

/-- **`Correct` for zero pairs, every `g > 0`, `0 ≤ κ < 1`.** -/
theorem correct_n0_all {p : DelayPar} (hp : Sane p) (hk : p.κ < 1) (R su Δo : Nat)
    (hR : Cp p * A1 + 87 * (Cp p * M1) + 1 ≤ R) :
    ∀ (x : Beh) (va vb : Nat → Nat), Behaves p (circuit net boundary) x →
      Env x boundary R su Δo (some 0) va vb → Correct x boundary R Δo (some 0) va vb := by
  have mem : ∀ w, memI w = true → ∃ e ∈ islandList, e.1 = w := by
    intro w hw
    obtain ⟨e, he, h⟩ := List.any_eq_true.mp hw
    exact ⟨e, he, by simpa using h⟩
  apply correct_n0 hp R su Δo (Cp p * M1) (Cp p * A1)
  · intro w hw
    obtain ⟨e, he, rfl⟩ := mem w hw
    have := List.all_eq_true.mp p1_ok e he
    simp only [p1OK, Bool.and_eq_true, decide_eq_true_eq] at this
    exact le_trans (cStart_le hp _ _) (Nat.mul_le_mul_left _ this.1.1)
  · intro w hw i hi
    obtain ⟨e, he, rfl⟩ := mem w hw
    have := List.all_eq_true.mp p1_ok e he
    simp only [p1OK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at this
    exact le_trans (sumMax_le hp _) (Nat.mul_le_mul_left _ (this.1.2 i hi))
  · intro w hw j hj
    obtain ⟨e, he, rfl⟩ := mem w hw
    have := List.all_eq_true.mp p1_ok e he
    simp only [p1OK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    exact sumMin_pos hp hk _ (this.2 j hj)
  · intro r hr hm
    have := List.all_eq_true.mp isl_rst r hr
    simp only [hm, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    exact le_trans (sumMax_le hp _) (Nat.mul_le_mul_left _ this)
  · exact hR

end Formal.Net.CViewPS
