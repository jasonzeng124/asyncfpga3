import Formal.Target.SpecRunt
import Formal.Timing.SpecSettle

/-!
# Stretching a quiet interval: a behaviour stays a behaviour (shard C, 2026-11-07)

**Problem, plainly.** The Lean refutations of THE statement (C's `CexPS*`, `CexR*`, A's `CexRunt72`) are single runs
with reset length `R = 400 ns`. THE statement takes `R` as a parameter, and positive results need a reset at least
`⌈(1+κ)g⌉·353 ns` long (`CViewPS.correct_n0_all`), so a refutation at one `R` says nothing about longer resets.
In those runs the whole circuit is quiet well before the reset ends. Is the same run, with the quiet stretch made
`Δ` longer (everything after it shifted by `Δ`), still a behaviour?

**Proved.** With `σ b Δ t = t` for `t ≤ b`, `b` on `[b, b + Δ]`, `t - Δ` after, and `stretch x b Δ n t = x n (σ b Δ t)`:
`gateOKRuntOn_stretch`: if gate `g` satisfies `GateOKRuntOn L w p c g x`, every node of `x` is constant on `[a, b]`,
`g.start p ≤ b`, every admissible delay `d` of `g`'s arcs has `a + d ≤ b`, and `w ≤ b - a`, then
`GateOKRuntOn L w p c g (stretch x b Δ)`. The new read maps are `f' i t = f i (σ t) + (t - σ t)`: the read lag at `t`
is the old lag at `σ t`, and every narrow pulse of the stretched signal is a shifted narrow pulse of the old one.
`behavesRuntOn_stretch`: the same for every gate of a net.

**Not shown here.** The environment and arbiter clauses for a stretched run (they are stated per run).
-/

namespace Formal.Net.Stretch
open Formal.Target

/-- The time map: identity up to `b`, held at `b` on `[b, b + Δ]`, shifted by `Δ` after. -/
def σ (b Δ t : Nat) : Nat := if t ≤ b then t else if t ≤ b + Δ then b else t - Δ

/-- The stretched behaviour. -/
def stretch (x : Beh) (b Δ : Nat) : Beh := fun n t => x n (σ b Δ t)

theorem σ_le (b Δ t : Nat) : σ b Δ t ≤ t := by unfold σ; split_ifs <;> omega

theorem σ_mono (b Δ : Nat) : Monotone (σ b Δ) := by
  intro s t h; unfold σ; split_ifs <;> omega

theorem sub_σ_mono (b Δ : Nat) : Monotone (fun t => t - σ b Δ t) := by
  intro s t h; simp only; unfold σ; split_ifs <;> omega

theorem σ_of_le {b Δ t : Nat} (h : t ≤ b) : σ b Δ t = t := by unfold σ; simp [h]

theorem σ_ge_min (b Δ t : Nat) : min t b ≤ σ b Δ t := by unfold σ; split_ifs <;> omega

/-- Quiet: every node is constant on `[a, b]`. -/
def Quiet (x : Beh) (a b : Nat) : Prop := ∀ n t, a ≤ t → t ≤ b → x n t = x n b

/-- The stretched signal is the old one at `σ`. On `[a, b + Δ]` it is the old value at `b`. -/
theorem stretch_mid {x : Beh} {a b Δ : Nat} (hq : Quiet x a b) (n : Nat) {t : Nat} (h1 : a ≤ t) (h2 : t ≤ b + Δ) :
    stretch x b Δ n t = x n b := by
  unfold stretch σ
  split_ifs with h3
  · exact hq n t h1 h3
  · rfl

/-- Reading the stretched signal at `f' = u + (t - σ t)` gives the old value at `u`, for `a ≤ u ≤ σ t`. -/
theorem stretch_read {x : Beh} {a b Δ : Nat} (hq : Quiet x a b) (n : Nat) {t u : Nat} (hu : u ≤ σ b Δ t)
    (ha : t ≤ b ∨ a ≤ u) : stretch x b Δ n (u + (t - σ b Δ t)) = x n u := by
  by_cases ht : t ≤ b
  · rw [σ_of_le ht] at hu ⊢
    rw [show u + (t - t) = u by omega]
    unfold stretch; rw [σ_of_le (by omega)]
  · have ha' : a ≤ u := ha.resolve_left ht
    by_cases ht2 : t ≤ b + Δ
    · have hs : σ b Δ t = b := by unfold σ; simp [ht, ht2]
      rw [hs] at hu ⊢
      rw [stretch_mid hq n (by omega) (by omega), hq n u ha' hu]
    · have hs : σ b Δ t = t - Δ := by unfold σ; simp [ht, ht2]
      rw [hs] at hu ⊢
      by_cases hub : u ≤ b
      · rw [stretch_mid hq n (by omega) (by omega), hq n u ha' hub]
      · unfold stretch σ
        rw [if_neg (by omega), if_neg (by omega)]
        congr 1; omega

/-- A narrow pulse of the stretched signal that contains a point of `[a, b + Δ]` cannot exist when `w ≤ b - a`. -/
theorem no_narrow_mid {x : Beh} {a b Δ w : Nat} (hq : Quiet x a b) (hw : w ≤ b - a) (n : Nat) {α β u : Nat}
    (hp : Pulse (stretch x b Δ n) α β) (hn : β - α < w) (hu1 : α ≤ u) (hu2 : u < β) (hm1 : a ≤ u) (hm2 : u ≤ b + Δ) :
    False := by
  obtain ⟨hab, hc, hl, hr⟩ := hp
  -- the pulse is constant from α to β - 1 and contains u
  have hα : α ≤ a := by
    by_contra h
    have h1 := stretch_mid hq n (Δ := Δ) (t := α - 1) (by omega) (by omega)
    have h2 := stretch_mid hq n (Δ := Δ) (t := α) (by omega) (by omega)
    exact hl (by omega) (h1.trans h2.symm)
  have hβ : b + Δ < β := by
    by_contra h
    have h1 := stretch_mid hq n (Δ := Δ) (t := β) (by omega) (by omega)
    have h2 := stretch_mid hq n (Δ := Δ) (t := u) hm1 hm2
    have h3 := hc u hu1 hu2
    exact hr (h1.trans (h2.symm.trans h3))
  omega

/-- A narrow pulse of the stretched signal at or after `b + Δ` is a shifted narrow pulse of the old signal. -/
theorem pulse_shift {x : Beh} {b Δ : Nat} (n : Nat) {α β : Nat} (hp : Pulse (stretch x b Δ n) α β)
    (hα : b + Δ < α) : Pulse (x n) (α - Δ) (β - Δ) := by
  obtain ⟨hab, hc, hl, hr⟩ := hp
  have e : ∀ t, b + Δ ≤ t → stretch x b Δ n t = x n (t - Δ) := by
    intro t ht; unfold stretch σ
    by_cases h1 : t ≤ b
    · rw [if_pos h1]; congr 1; omega
    · by_cases h2 : t ≤ b + Δ
      · rw [if_neg h1, if_pos h2]; congr 1; omega
      · rw [if_neg h1, if_neg h2]
  refine ⟨by omega, fun t h1 h2 => ?_, fun _ => ?_, ?_⟩
  · have := hc (t + Δ) (by omega) (by omega)
    rw [e _ (by omega), e _ (by omega)] at this
    rwa [show t + Δ - Δ = t by omega] at this
  · have := hl (by omega)
    rw [e _ (by omega), e _ (by omega)] at this
    rwa [show α - 1 - Δ = α - Δ - 1 by omega] at this
  · have := hr
    rw [e _ (by omega), e _ (by omega)] at this
    exact this

/-- **The gate relation survives the stretch.** -/
theorem gateOKRuntOn_stretch {L : Gate → Bool} {w : Nat} {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh}
    {a b Δ : Nat} (hq : Quiet x a b) (hst : g.start p ≤ b)
    (hlag : ∀ i, i < g.k → ∀ d, Adm p c (g.arcs.getD i default) d → a + d ≤ b) (hw : w ≤ b - a)
    (h : GateOKRuntOn L w p c g x) : GateOKRuntOn L w p c g (stretch x b Δ) := by
  obtain ⟨f, hm, ht⟩ := h
  refine ⟨fun i t => f i (σ b Δ t) + (t - σ b Δ t), fun i hi => ?_, fun t h0 => ?_⟩
  · intro s t hst'
    exact Nat.add_le_add (hm i hi (σ_mono b Δ hst')) (sub_σ_mono b Δ hst')
  · have hσ : g.start p ≤ σ b Δ t := le_trans (le_min h0 hst) (σ_ge_min b Δ t)
    obtain ⟨hr, he⟩ := ht (σ b Δ t) hσ
    -- old reads at σ t are at least a once t > b
    have hfa : ∀ i, i < g.k → b < t → a ≤ f i (σ b Δ t) := by
      intro i hi hbt
      have hb := ht b hst
      have h1 := (hb.1 i hi).1
      have h2 := hlag i hi _ (hb.1 i hi).2.1
      have hmon := hm i hi (show b ≤ σ b Δ t by unfold σ; split_ifs <;> omega)
      omega
    have hrd : ∀ i, i < g.k → stretch x b Δ (g.ins.getD i 0) (f i (σ b Δ t) + (t - σ b Δ t)) =
        x (g.ins.getD i 0) (f i (σ b Δ t)) := by
      intro i hi
      apply stretch_read hq _ (hr i hi).1
      by_cases hbt : t ≤ b
      · exact Or.inl hbt
      · exact Or.inr (hfa i hi (by omega))
    refine ⟨fun i hi => ⟨?_, ?_, fun hL => ?_⟩, ?_⟩
    · show f i (σ b Δ t) + (t - σ b Δ t) ≤ t
      have := (hr i hi).1; have := σ_le b Δ t; omega
    · show Adm p c _ (t - (f i (σ b Δ t) + (t - σ b Δ t)))
      rw [show t - (f i (σ b Δ t) + (t - σ b Δ t)) = σ b Δ t - f i (σ b Δ t) by
        have := (hr i hi).1; have := σ_le b Δ t; omega]
      exact (hr i hi).2.1
    · show NoRuntRead w (stretch x b Δ (g.ins.getD i 0)) (f i (σ b Δ t) + (t - σ b Δ t))
      intro α β hp hn hin
      have hold := (hr i hi).2.2 hL
      set u := f i (σ b Δ t) with hu
      set u' := u + (t - σ b Δ t) with hu'
      by_cases hbt : t ≤ b
      · -- no shift: u' = u ≤ b
        have e1 : u' = u := by rw [hu', σ_of_le hbt]; omega
        have hub : u ≤ b := by have := (hr i hi).1; have := σ_le b Δ t; omega
        by_cases hβ : β ≤ b
        · -- the pulse lies where the stretch is the identity
          apply hold α β _ hn (by rw [← e1]; exact hin)
          obtain ⟨hab, hc, hl, hr'⟩ := hp
          have e : ∀ s, s ≤ b → stretch x b Δ (g.ins.getD i 0) s = x (g.ins.getD i 0) s := by
            intro s hs; unfold stretch; rw [σ_of_le hs]
          refine ⟨hab, fun s h1 h2 => ?_, fun h => ?_, ?_⟩
          · have := hc s h1 h2; rwa [e s (by omega), e α (by omega)] at this
          · have := hl h; rwa [e _ (by omega), e α (by omega)] at this
          · rwa [e β hβ, e α (by omega)] at hr'
        · -- the pulse reaches past b: it contains b, so it is the quiet run
          by_cases hua : a ≤ u
          · exact no_narrow_mid hq hw _ hp hn hin.1 hin.2 (by omega) (by omega)
          · -- u < a: the pulse [α, β) contains [u, b]; it cannot start after a, and it is wide
            obtain ⟨hab, hc, hl, hr'⟩ := hp
            have hb' : stretch x b Δ (g.ins.getD i 0) b = stretch x b Δ (g.ins.getD i 0) α := hc b (by omega) (by omega)
            have hβ2 : b + Δ < β := by
              by_contra hh
              have h1 := stretch_mid hq (g.ins.getD i 0) (Δ := Δ) (t := β) (by omega) (by omega)
              have h2 := stretch_mid hq (g.ins.getD i 0) (Δ := Δ) (t := b) (by omega) (by omega)
              exact hr' (h1.trans (h2.symm.trans hb'))
            omega
      · have hua : a ≤ u := hfa i hi (by omega)
        by_cases hm : u' ≤ b + Δ
        · exact no_narrow_mid hq hw _ hp hn hin.1 hin.2 (by omega) hm
        · -- u' > b + Δ: then t > b + Δ, σ t = t - Δ, u' = u + Δ, u > b
          have ht2 : ¬ t ≤ b + Δ := by
            intro h2
            have : σ b Δ t = b := by unfold σ; simp [hbt, h2]
            have := (hr i hi).1; omega
          have hs : σ b Δ t = t - Δ := by unfold σ; simp [hbt, ht2]
          have e1 : u' = u + Δ := by rw [hu', hs]; omega
          by_cases hα : b + Δ < α
          · have hp' := pulse_shift (g.ins.getD i 0) hp hα
            exact hold (α - Δ) (β - Δ) hp' (by omega) ⟨by omega, by omega⟩
          · have hab0 : a ≤ b := by
              have hb := ht b hst; have := hlag i hi _ (hb.1 i hi).2.1; omega
            exact no_narrow_mid (u := b + Δ) hq hw _ hp hn (by omega) (by omega) (by omega) le_rfl
    · show stretch x b Δ g.out t =
        g.init.testBit (addr g.k fun i => stretch x b Δ (g.ins.getD i 0) (f i (σ b Δ t) + (t - σ b Δ t)))
      have ha : (addr g.k fun i => stretch x b Δ (g.ins.getD i 0) (f i (σ b Δ t) + (t - σ b Δ t))) =
          addr g.k fun i => x (g.ins.getD i 0) (f i (σ b Δ t)) :=
        Formal.Timing.SpecSettle.addr_congr _ _ _ (fun i hi => hrd i hi)
      rw [ha, ← he]; rfl

/-- An admissible delay of a gate's arc is at most the gate's start (bands ordered: `fmax ≤ smax`). -/
theorem adm_le_start {p : DelayPar} {c : ℚ} {g : Gate} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hwf : ∀ e ∈ g.arcs, e.fmax ≤ e.smax) {e : Arc} (he : e ∈ g.arcs) {d : Nat} (h : Adm p c e d) :
    d ≤ g.start p := by
  have hd : (d : ℚ) ≤ (1 + p.κ) * lerp e.fmax e.smax c * p.g := h.2
  have hl0 : (0 : ℚ) ≤ lerp e.fmax e.smax c := by
    unfold lerp
    have h1 : (0 : ℚ) ≤ 1 - c := by linarith
    have := mul_nonneg h1 (Nat.cast_nonneg (α := ℚ) e.fmax)
    have := mul_nonneg hc0 (Nat.cast_nonneg (α := ℚ) e.smax)
    linarith
  have hls : lerp e.fmax e.smax c ≤ (e.smax : ℚ) := by
    unfold lerp
    have h1 : (e.fmax : ℚ) ≤ e.smax := by exact_mod_cast hwf e he
    nlinarith
  by_cases hk : 0 ≤ (1 + p.κ) * p.g
  swap
  · have : (1 + p.κ) * lerp e.fmax e.smax c * p.g ≤ 0 := by
      have : (1 + p.κ) * lerp e.fmax e.smax c * p.g = ((1 + p.κ) * p.g) * lerp e.fmax e.smax c := by ring
      rw [this]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hl0
    have hd0 : (d : ℚ) ≤ 0 := le_trans hd this
    have : d = 0 := by exact_mod_cast le_antisymm hd0 (by positivity)
    omega
  have hle : (d : ℚ) ≤ (1 + p.κ) * e.smax * p.g := by
    calc (d : ℚ) ≤ (1 + p.κ) * lerp e.fmax e.smax c * p.g := hd
      _ = ((1 + p.κ) * p.g) * lerp e.fmax e.smax c := by ring
      _ ≤ ((1 + p.κ) * p.g) * e.smax := mul_le_mul_of_nonneg_left hls hk
      _ = (1 + p.κ) * e.smax * p.g := by ring
  have h1 : d ≤ (Rat.ceil ((1 + p.κ) * e.smax * p.g)).toNat := by
    rw [show Rat.ceil ((1 + p.κ) * e.smax * p.g) = ⌈(1 + p.κ) * (e.smax : ℚ) * p.g⌉ by
      rw [Rat.ceil_eq_neg_floor_neg]; rfl]
    have hc := Int.le_ceil ((1 + p.κ) * (e.smax : ℚ) * p.g)
    have h2 : ((d : ℤ) : ℚ) ≤ ((⌈(1 + p.κ) * (e.smax : ℚ) * p.g⌉ : ℤ) : ℚ) := by push_cast; linarith
    have h3 : (d : ℤ) ≤ ⌈(1 + p.κ) * (e.smax : ℚ) * p.g⌉ := by exact_mod_cast h2
    omega
  unfold Gate.start
  have : ∀ l : List Arc, e ∈ l → (Rat.ceil ((1 + p.κ) * e.smax * p.g)).toNat ≤
      (l.map fun e => (Rat.ceil ((1 + p.κ) * e.smax * p.g)).toNat).foldr max 0 := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons e' l ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp hl with h | h
      · subst h; exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)
  exact le_trans h1 (this _ he)

/-- **Every gate of a well-formed net survives the stretch**, if the circuit is quiet on `[a, b]` for at least every
gate's start (`a + start ≤ b`) and at least `w`. -/
theorem behavesRuntOn_stretch {L : Gate → Bool} {w : Nat} {p : DelayPar} {N : Net} {x : Beh} {a b Δ : Nat}
    (hwf : N.WF) (hq : Quiet x a b) (hS : ∀ g ∈ N.gates, a + g.start p ≤ b) (hw : w ≤ b - a)
    (h : BehavesRuntOn L w p N x) : BehavesRuntOn L w p N (stretch x b Δ) := by
  obtain ⟨c, hc0, hc1, hg⟩ := h
  refine ⟨c, hc0, hc1, fun g hgm => ?_⟩
  obtain ⟨hlen, hlenA, -, -, -, hband⟩ := hwf.1 g hgm
  have hS' := hS g hgm
  apply gateOKRuntOn_stretch hq (by omega) _ hw (hg g hgm)
  intro i hi d hd
  have he : g.arcs.getD i default ∈ g.arcs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have := adm_le_start hc0 hc1 (fun e he => (hband e he).2.2.2) he hd
  omega

/-- `σ` hits every time between `σ t1` and `σ t2`. -/
theorem σ_onto (b Δ t1 t2 s : Nat) (h12 : t1 ≤ t2) (h1 : σ b Δ t1 ≤ s) (h2 : s ≤ σ b Δ t2) :
    ∃ t, t1 ≤ t ∧ t ≤ t2 ∧ σ b Δ t = s := by
  by_cases hs : s ≤ b
  · by_cases ht1 : t1 ≤ b
    · refine ⟨s, by rw [σ_of_le ht1] at h1; exact h1, ?_, σ_of_le hs⟩
      by_contra hc
      have : σ b Δ t2 = t2 := σ_of_le (by omega)
      omega
    · -- σ t1 ≥ b, so s = b
      have : b ≤ σ b Δ t1 := by unfold σ; split_ifs <;> omega
      refine ⟨t1, le_rfl, h12, ?_⟩
      unfold σ at h1 ⊢; split_ifs at h1 ⊢ <;> omega
  · refine ⟨max t1 (s + Δ), le_max_left _ _, ?_, ?_⟩
    · unfold σ at h2; split_ifs at h2 <;> omega
    · unfold σ at h1 ⊢; split_ifs at h1 ⊢ <;> omega

/-- **H_ARB survives the stretch** when the quiet stretch is longer than `T`. -/
theorem arbOK_stretch {T : Nat} {A : List ArbNodes} {x : Beh} {a b Δ : Nat} (hq : Quiet x a b) (haT : a + T ≤ b)
    (h : ArbOK T A x) : ArbOK T A (stretch x b Δ) := by
  intro arb harb t1 t2 hin t ht1 ht2
  -- the old inputs are constant on [σ t1, σ t2]
  have hold : ∀ n ∈ arb.ins, ConstOn (x n) (σ b Δ t1) (σ b Δ t2) := by
    intro n hn s hs1 hs2
    obtain ⟨u, hu1, hu2, hu⟩ := σ_onto b Δ t1 t2 s (by omega) hs1 hs2
    have := hin n hn u hu1 hu2
    unfold stretch at this; rw [hu] at this; exact this
  show x arb.q (σ b Δ t) = x arb.q (σ b Δ (t1 + T))
  by_cases hcase : σ b Δ t1 + T ≤ σ b Δ (t1 + T)
  · have hq2 := h arb harb _ _ hold
    rw [hq2 (σ b Δ t) (le_trans hcase (σ_mono b Δ ht1)) (σ_mono b Δ ht2),
      hq2 (σ b Δ (t1 + T)) hcase (σ_mono b Δ (by omega))]
  · -- the window [t1, t1 + T] meets the held stretch: σ t1 ≤ b ≤ σ (t1 + T)
    have hs1 : σ b Δ t1 ≤ b := by unfold σ at hcase ⊢; split_ifs at hcase ⊢ <;> omega
    have hsT : b ≤ σ b Δ (t1 + T) := by unfold σ at hcase ⊢; split_ifs at hcase ⊢ <;> omega
    set s0 := min (σ b Δ t1) a
    have hs2 : b ≤ σ b Δ t2 := le_trans hsT (σ_mono b Δ (by omega))
    have hwide : ∀ n ∈ arb.ins, ConstOn (x n) s0 (σ b Δ t2) := by
      intro n hn s h1 h2
      have hc := hold n hn
      by_cases hsa : σ b Δ t1 ≤ a
      · have e0 : s0 = σ b Δ t1 := min_eq_left hsa
        rw [e0] at h1 ⊢; exact hc s h1 h2
      · have e0 : s0 = a := min_eq_right (by omega)
        rw [e0] at h1 ⊢
        by_cases hsb : s ≤ b
        · rw [hq n s h1 hsb, hq n a le_rfl (by omega)]
        · rw [hc s (by omega) h2, ← hc b (by omega) hs2, hq n b (by omega) le_rfl, hq n a le_rfl (by omega)]
    have hq3 := h arb harb _ _ hwide
    have hs0T : s0 + T ≤ b := by have : s0 ≤ a := min_le_right _ _; omega
    rw [hq3 (σ b Δ t) (le_trans hs0T (le_trans hsT (σ_mono b Δ ht1))) (σ_mono b Δ ht2),
      hq3 (σ b Δ (t1 + T)) (le_trans hs0T hsT) (σ_mono b Δ (by omega))]

end Formal.Net.Stretch
