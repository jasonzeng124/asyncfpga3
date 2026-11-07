import Formal.Cells.FiniteNet
import Formal.Cells.AssumeGuaranteeMuxNet

/-!
# Probe Bfin2 (shard B): time-truncated cell lemmas for C-elements, steers, mux joins and ORs

Note: `formal/notes/B-finite-net.md`. `FiniteNet` gives the time-indexed rule (`ag_trunc`)
and the truncated lemmas of a `Win` LUT (`tnode`), a wire (`twire`) and B's link (`tlink`).
This file gives the same "pins clean on `[0, T)` ⇒ node clean on `[0, T + lo)`" lemma for
the other gate-modelled classes, including the two OR cells (`uack`, `uor`) that Bnet's
end-ordered segment rule cannot carry (`AssumeGuaranteeMuxOr.Wit.or_not_causal`).

## Assumed / proved / NOT covered

**Proved:**
* `seg_find`: a step signal whose existing edges increase covers every instant.
* `tcelX`: a C-element LUT (any pins, `CelLaw`, B's `CelG`), truncated, from a pointwise
  excitation condition on `[0, T)` (Bmux2's `celX_segK` form). `tcelG`: from the pins'
  truncated step shapes (edge sets per pin; the node's edge `j` exists iff every pin's
  does), e.g. the real `bd_c2`/`bd_c3`/`bd_c4` (forks N ≤ 4, joins N = 2).
* `tgated`: the gated request `r ∧ (s == b)` of a steer branch / mux join, truncated, from
  the request's truncated shape, H_SEL_STABLE and the token enumeration `κ`; edge `j` of
  the gate exists iff request edge `sN κ j` does. `tsteer`: the REAL `bd_steer` `u` LUT.
  `tmuxj`: the REAL `uj0`/`uj1` (via Bmux2's `uj0_cel`/`uj1_cel`: `G2` of the input request
  and the gated control).
* `tor_ex`: the OR `a₁ ∨ a₀` of two branch acknowledges, truncated (merged edges Bmux2's
  `oe`, token counts `cnt`), from the two branches' truncated shapes, the token enumeration
  per branch, and ONE edge-time hypothesis H_ORD (the merged edges increase, i.e. the two
  branches interleave in token order); `tuack`, `tuor`: the REAL `bd_steer` `uack` and
  `bd_mux` `uor` LUTs. In the time-indexed rule the OR's low phase reads the idle branch
  only up to `T`, so the obstruction of `or_not_causal` does not arise, and a branch that
  never fires again (a finite run) is simply constant: no H_LATER is needed.

**Assumed (named):** the B gate models (`CelG`, `Win` + H_NO_REVERT), H_PWR, H_RST,
H_RST_LONG, H_LAT; the departure bounds H_SND per existing edge; H_SEL_STABLE and `κ`;
for the OR, H_ORD and H_DOWN (edges of the merged sequence exist in order); the floors
`R ≤ c j` / `hi ≤ c j + lo` (edge-time inequalities, as before).

**NOT covered:** Bmux2's mux acknowledges `uxa`/`uya` (`muxa_segK`, `z_ack` carries every
output token) and the source `bd_src` (`src_segK`, power-up rise) have no truncated form
here. Core Lean only.
-/

namespace Formal.Cells.FiniteNet
open Formal.Cells
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_before)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.FiniteRuns (fe)
open Formal.Cells.LutFbBridge2 (CelLaw CelG gc gc_even gc_odd G2 law2 pv2 gate)
open Formal.Cells.AssumeGuaranteeEnds (sN sN_even sN_odd)
open Formal.Cells.AssumeGuaranteeMuxOr (cnt cnt_succ_eq cnt_succ_ne cnt_mono cnt_kappa oe
  oe_even oe_odd)
open Formal.Net.Ops.Gen (genF steerF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. Finding the segment of an instant -/

/-- Edges that exist increase ⇒ every instant lies before the first edge or in a segment. -/
theorem seg_find {L : Nat → Prop} {γ : Nat → Nat} (hd : ∀ j, L (j + 1) → L j)
    (hm : ∀ j, L (j + 1) → γ j < γ (j + 1)) (s : Nat) :
    (¬ L 0 ∨ s < γ 0) ∨ ∃ j, L j ∧ γ j ≤ s ∧ (L (j + 1) → s < γ (j + 1)) := by
  have hge : ∀ j, L j → j ≤ γ j := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ j ih => intro h; have := ih (hd j h); have := hm j h; omega
  have Q : ∀ j, (∃ j, L j ∧ γ j ≤ s ∧ (L (j + 1) → s < γ (j + 1))) ∨ (L j ∧ γ j ≤ s) ∨
      (¬ L 0 ∨ s < γ 0) := by
    intro j
    induction j with
    | zero =>
      by_cases h : L 0 ∧ γ 0 ≤ s
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ?_)
        by_cases h0 : L 0
        · exact Or.inr (by apply Classical.byContradiction; intro hc; exact h ⟨h0, by omega⟩)
        · exact Or.inl h0
    | succ j ih =>
      rcases ih with h | h | h
      · exact Or.inl h
      · by_cases h' : L (j + 1) ∧ γ (j + 1) ≤ s
        · exact Or.inr (Or.inl h')
        · exact Or.inl ⟨j, h.1, h.2, fun hl => by
            apply Classical.byContradiction; intro hc; exact h' ⟨hl, by omega⟩⟩
      · exact Or.inr (Or.inr h)
  rcases Q (s + 1) with h | h | h
  · exact Or.inr h
  · have := hge _ h.1; omega
  · exact Or.inl h

theorem mono_ex {L : Nat → Prop} {γ : Nat → Nat} (hd : ∀ j, L (j + 1) → L j)
    (hm : ∀ j, L (j + 1) → γ j < γ (j + 1)) : ∀ i j, i ≤ j → L j → γ i ≤ γ j := by
  intro i j h hj
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have := ih (by omega) (hd j hj); have := hm j hj; omega
    · have : i = j + 1 := by omega
      subst this; exact Nat.le_refl _

theorem down_ex {L : Nat → Prop} (hd : ∀ j, L (j + 1) → L j) : ∀ i j, i ≤ j → L j → L i := by
  intro i j h hj
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact hj
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · exact ih (by omega) (hd j hj)
    · have : i = j + 1 := by omega
      subst this; exact hj

/-! ## 2. A C-element, truncated -/

section celx
variable {ι : Type} {G : (ι → Bool) → Bool → Bool → Bool} {p : Nat → ι → Bool}
  {rst O qp : Nat → Bool} {lo hi wl wh R E T : Nat} {c : Nat → Nat} {Ln : Nat → Prop}

/-- **C-element, truncated, from the excitation condition on `[0, T)`.** -/
theorem tcelX (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R)
    (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false)
    (hcR : ∀ j, Ln j → R ≤ c j)
    (H_EX0 : ∀ s, s < T → R ≤ s → (¬ Ln 0 ∨ s < c 0) → ∃ i, p s i = false)
    (H_EXJ : ∀ j s, s < T → Ln j → c j ≤ s → (Ln (j + 1) → s < c (j + 1)) →
      (∀ i, p s i = Vph j) ∨ ((∃ i, p s i = Vph j) ∧ nt O lo hi (c j) (Vph j) + E ≤ s)) :
    GPhT O (fe O lo hi c) Ln (T + lo) := by
  have hlh := win_le C.H_LUT_WIN
  have hlo := C.H_LUT_POS
  have hfb : ∀ s, hi + wh ≤ s → ∃ s', s' + lo + wl ≤ s ∧ s ≤ s' + hi + wh ∧
      qp s = G (p s') (qp s') (rst s') := by
    intro s hs
    obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
    obtain ⟨s', q1, q2, q3⟩ := C.H_LUT_WIN u (by omega)
    exact ⟨s', by omega, by omega, by rw [e, q3]⟩
  have hwl : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := C.H_FB wh (Nat.le_refl _); omega
  have hx : GPhT (fun t => G (p t) (qp t) (rst t)) c Ln T := by
    refine ⟨fun s => ?_, fun j s => ?_⟩
    · induction s using Nat.strongRecOn with
      | _ s ih =>
        intro hs h
        show G (p s) (qp s) (rst s) = false
        by_cases hR : s < R
        · rw [H_RST s]; simp only [hR, decide_true]; exact L.rst _ _
        · have hr : rst s = false := by rw [H_RST]; simp; omega
          obtain ⟨s', q1, q2, q3⟩ := hfb s (by omega)
          have hq : qp s = false := by
            rw [q3]; refine ih s' (by omega) (by omega) ?_
            rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (by omega)
          rw [hr, hq]; exact L.hold _ _ (H_EX0 s hs (by omega) h)
    · induction s using Nat.strongRecOn with
      | _ s ih =>
        intro hs hj h1 h2
        show G (p s) (qp s) (rst s) = Vph j
        have hR := hcR j hj
        have hr : rst s = false := by rw [H_RST]; simp; omega
        rw [hr]
        rcases H_EXJ j s hs hj h1 h2 with hall | ⟨⟨i2, hi2⟩, hlate⟩
        · exact L.all _ _ _ hall
        · have hl := nt_lo O (c j) (Vph j) hlh (hi := hi)
          obtain ⟨s', q1, q2, q3⟩ := hfb s (by omega)
          have hq : qp s = Vph j := by
            rw [q3]; exact ih s' (by omega) (by omega) hj (by omega) (fun h => by
              have := h2 h; omega)
          rw [hq]; exact L.hold _ _ ⟨i2, hi2⟩
  exact tnode C.H_LUT_WIN C.H_NO_REVERT hx (fun j hj => by have := hcR j hj; omega) H_PWR

/-- **C-element, truncated, from its pins' truncated shapes** (`celG_segK`'s finite form):
pin `i` clean on `[0, T)` with edges `ρ i` and edge set `Lp i`; the node's phase starts `c`
are the last arrivals (`H_ARR`, `H_LAST`); its edge `j` exists iff every pin's does
(`H_CNT`); H_SND for existing edges. -/
theorem tcelG (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R)
    (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false)
    {ρ : ι → Nat → Nat} {Lp : ι → Nat → Prop}
    (H_ARR : ∀ i j, ρ i j ≤ c j) (H_LAST : ∀ j s, s < c j → ∃ i, s < ρ i j)
    (H_CNT : ∀ j, Ln j ↔ ∀ i, Lp i j)
    (hcR : ∀ j, Ln j → R ≤ c j)
    (H_SND : ∀ i j, Ln j → Lp i (j + 1) → nt O lo hi (c j) (Vph j) + E ≤ ρ i (j + 1))
    (hp : ∀ i, GPhT (fun t => p t i) (ρ i) (Lp i) T) :
    GPhT O (fe O lo hi c) Ln (T + lo) := by
  refine tcelX L C H_RST H_RST_LONG H_LAT H_PWR hcR (fun s hs _ h => ?_)
    (fun j s hs hj h1 h2 => ?_)
  · by_cases h0 : Ln 0
    · rcases h with h | h
      · exact absurd h0 h
      · obtain ⟨i, hi⟩ := H_LAST 0 s h
        exact ⟨i, (hp i).pre s hs (Or.inr hi)⟩
    · have : ¬ ∀ i, Lp i 0 := fun h' => h0 ((H_CNT 0).2 h')
      rw [Classical.not_forall] at this
      obtain ⟨i, hi⟩ := this
      exact ⟨i, (hp i).pre s hs (Or.inl hi)⟩
  · have hpj : ∀ i, Lp i j := (H_CNT j).1 hj
    have still : ∀ i, (Lp i (j + 1) → s < ρ i (j + 1)) → p s i = Vph j := fun i h =>
      (hp i).ph j s hs (hpj i) (Nat.le_trans (H_ARR i j) h1) h
    by_cases hd : ∀ i, Lp i (j + 1) → s < ρ i (j + 1)
    · exact Or.inl (fun i => still i (hd i))
    · rw [Classical.not_forall] at hd
      obtain ⟨i1, hi1⟩ := hd
      have hl1 : Lp i1 (j + 1) := Classical.byContradiction fun h => hi1 (fun h' => absurd h' h)
      have hge : ρ i1 (j + 1) ≤ s := Classical.byContradiction fun h => hi1 (fun _ => by omega)
      have hsnd := H_SND i1 j hj hl1
      refine Or.inr ⟨?_, by omega⟩
      by_cases hn : Ln (j + 1)
      · obtain ⟨i2, hi2⟩ := H_LAST (j + 1) s (h2 hn)
        exact ⟨i2, still i2 (fun _ => hi2)⟩
      · have : ¬ ∀ i, Lp i (j + 1) := fun h' => hn ((H_CNT (j + 1)).2 h')
        rw [Classical.not_forall] at this
        obtain ⟨i2, hi2⟩ := this
        exact ⟨i2, still i2 (fun h => absurd h hi2)⟩

end celx

/-! ## 3. A gated request (steer branch, mux join control), truncated -/

/-- **The gated request `r ∧ (s == b)`, truncated.** The request `r` is clean on `[0, T)`
(edges `γ`, set `Lγ`, existing edges increasing and in order); H_SEL_STABLE (while `r` is
high in token `n`, `s` is `σ n`); `κ` enumerates the tokens with `σ n = b`. Then the gate
is clean on `[0, T)` with edges `gc κ γ` and edge `j` existing iff request edge `sN κ j`
does. -/
theorem tgated {r s : Nat → Bool} {γ : Nat → Nat} {Lγ : Nat → Prop} {σ : Nat → Bool}
    {κ : Nat → Nat} {b : Bool} {T : Nat}
    (hd : ∀ j, Lγ (j + 1) → Lγ j) (hγ : ∀ j, Lγ (j + 1) → γ j < γ (j + 1))
    (H_SEL_STABLE : ∀ n t, Lγ (2 * n) → γ (2 * n) ≤ t → (Lγ (2 * n + 1) → t < γ (2 * n + 1)) →
      s t = σ n)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκb : ∀ m, σ (κ m) = b)
    (hκall : ∀ n, σ n = b → ∃ m, κ m = n)
    (hr : GPhT r γ Lγ T) :
    GPhT (fun t => r t && (s t == b)) (gc κ γ) (fun j => Lγ (sN κ j)) T := by
  have km := LutFbBridge2.mono_of_succ hκ
  have gm := mono_ex hd hγ
  have dn := down_ex hd
  -- where `r` is high: in token `n`'s high phase
  have rv : ∀ t, t < T → r t = true → ∃ n, Lγ (2 * n) ∧ γ (2 * n) ≤ t ∧
      (Lγ (2 * n + 1) → t < γ (2 * n + 1)) := by
    intro t ht h
    rcases seg_find hd hγ t with h0 | ⟨j, hj, h1, h2⟩
    · rw [hr.pre t ht h0] at h; cases h
    · have := hr.ph j t ht hj h1 h2
      rw [h] at this
      have hj2 : j % 2 = 0 := AssumeGuaranteeMux.vph_true_even this.symm
      exact ⟨j / 2, by rw [show 2 * (j / 2) = j by omega]; exact hj,
        by rw [show 2 * (j / 2) = j by omega]; exact h1,
        by rw [show 2 * (j / 2) + 1 = j + 1 by omega]; exact h2⟩
  -- a token not steered to `b` keeps the gate low
  have off : ∀ t, t < T → (∀ n, Lγ (2 * n) → γ (2 * n) ≤ t →
      (Lγ (2 * n + 1) → t < γ (2 * n + 1)) → σ n ≠ b) → (r t && (s t == b)) = false := by
    intro t ht hn
    cases hrt : r t
    · rfl
    · obtain ⟨n, a1, a2, a3⟩ := rv t ht hrt
      rw [H_SEL_STABLE n t a1 a2 a3, beq_eq_false_iff_ne.mpr (hn n a1 a2 a3)]; rfl
  refine ⟨fun t ht h => ?_, fun j t ht hj h1 h2 => ?_⟩
  · refine off t ht (fun n a1 a2 a3 hb => ?_)
    obtain ⟨m, rfl⟩ := hκall n hb
    have k0 := km 0 m (Nat.zero_le _)
    have e0 : sN κ 0 = 2 * κ 0 := by unfold sN; simp
    rw [e0] at h
    have g0 : gc κ γ 0 = γ (2 * κ 0) := by unfold gc; simp
    rw [g0] at h
    have l0 := dn (2 * κ 0) (2 * κ m) (by omega) a1
    rcases h with h | h
    · exact h l0
    · have := gm (2 * κ 0) (2 * κ m) (by omega) a1; omega
  · obtain ⟨m, rfl | rfl⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
    · -- high phase of the `m`-th `b`-token
      simp only [sN_even] at hj
      rw [gc_even] at h1
      have h2' : Lγ (2 * κ m + 1) → t < γ (2 * κ m + 1) := fun h => by
        have := h2 (by rw [sN_odd]; exact h); rwa [gc_odd] at this
      have hr1 : r t = true := by
        rw [hr.ph (2 * κ m) t ht hj h1 h2']; exact PipeTimed.Vph_even _
      rw [hr1, H_SEL_STABLE (κ m) t hj h1 h2', hκb, PipeTimed.Vph_even]; cases b <;> rfl
    · -- low phase between the `m`-th and the `(m+1)`-th `b`-token
      simp only [sN_odd] at hj
      rw [gc_odd] at h1
      have h2' : Lγ (2 * κ (m + 1)) → t < γ (2 * κ (m + 1)) := fun h => by
        have := h2 (by rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, sN_even]; exact h)
        rwa [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, gc_even] at this
      show (r t && (s t == b)) = Vph (2 * m + 1)
      rw [PipeTimed.Vph_odd]
      refine off t ht (fun n a1 a2 a3 hb => ?_)
      obtain ⟨m', rfl⟩ := hκall n hb
      rcases Nat.lt_or_ge m m' with h | h
      · have := km (m + 1) m' h
        by_cases hl : Lγ (2 * κ (m + 1))
        · have := gm (2 * κ (m + 1)) (2 * κ m') (by omega) a1
          have := h2' hl; omega
        · exact hl (dn _ _ (by omega) a1)
      · have := km m' m h
        have hl : Lγ (2 * κ m' + 1) := dn _ _ (by omega) hj
        have := a3 hl
        have := gm (2 * κ m' + 1) (2 * κ m + 1) (by omega) hj
        omega

/-- **Steer branch `b`, truncated** (the REAL `bd_steer` `u` LUT, O5/O6; `Win` +
H_NO_REVERT, no feedback, no reset). -/
theorem tsteer (b : Bool) {req s O : Nat → Bool} {lo hi T : Nat} {γ κ : Nat → Nat}
    {Lγ : Nat → Prop} {σ : Nat → Bool}
    (H_LUT_WIN : Win lo hi (fun t => steerF b (req t, s t)) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => steerF b (req t, s t)) O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (hd : ∀ j, Lγ (j + 1) → Lγ j) (hγ : ∀ j, Lγ (j + 1) → γ j < γ (j + 1))
    (H_SEL_STABLE : ∀ n t, Lγ (2 * n) → γ (2 * n) ≤ t → (Lγ (2 * n + 1) → t < γ (2 * n + 1)) →
      s t = σ n)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκb : ∀ m, σ (κ m) = b)
    (hκall : ∀ n, σ n = b → ∃ m, κ m = n)
    (H_FLOOR : ∀ j, Lγ (sN κ j) → hi ≤ gc κ γ j + lo)
    (hr : GPhT req γ Lγ T) :
    GPhT O (fe O lo hi (gc κ γ)) (fun j => Lγ (sN κ j)) (T + lo) := by
  have ex : (fun t => steerF b (req t, s t)) = fun t => req t && (s t == b) :=
    funext fun t => LutFbBridge2.steerF_gate b (req t) (s t)
  rw [ex] at H_LUT_WIN H_NO_REVERT
  exact tnode H_LUT_WIN H_NO_REVERT (tgated hd hγ H_SEL_STABLE hκ hκb hκall hr) H_FLOOR H_PWR

/-- **A mux join, truncated** (`uj0`, `b = false`; `uj1`, `b = true`; B's `CelG` of `G2` on
the input request `x` and the gated control, which the REAL LUTs are: `uj0_cel`,
`uj1_cel`). -/
theorem tmuxj {b : Bool} {x cr s rst O qp : Nat → Bool} {lo hi wl wh R E T : Nat}
    {ρ γ κ c : Nat → Nat} {σ : Nat → Bool} {Lx Lγ Ln : Nat → Prop}
    (C : CelG G2 (pv2 x (gate b cr s)) rst O qp lo hi wl wh)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R)
    (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false)
    (hd : ∀ j, Lγ (j + 1) → Lγ j) (hγ : ∀ j, Lγ (j + 1) → γ j < γ (j + 1))
    (H_SEL_STABLE : ∀ n t, Lγ (2 * n) → γ (2 * n) ≤ t → (Lγ (2 * n + 1) → t < γ (2 * n + 1)) →
      s t = σ n)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκb : ∀ m, σ (κ m) = b)
    (hκall : ∀ n, σ n = b → ∃ m, κ m = n)
    (H_C : ∀ j, c j = max (ρ j) (gc κ γ j))
    (H_CNT : ∀ j, Ln j ↔ Lx j ∧ Lγ (sN κ j))
    (hcR : ∀ j, Ln j → R ≤ c j)
    (H_SND : ∀ j, Ln j → (Lx (j + 1) → nt O lo hi (c j) (Vph j) + E ≤ ρ (j + 1)) ∧
      (Lγ (sN κ (j + 1)) → nt O lo hi (c j) (Vph j) + E ≤ gc κ γ (j + 1)))
    (hx : GPhT x ρ Lx T) (hc : GPhT cr γ Lγ T) :
    GPhT O (fe O lo hi c) Ln (T + lo) := by
  have hg := tgated hd hγ H_SEL_STABLE hκ hκb hκall hc (b := b)
  let ρ2 : Fin 2 → Nat → Nat := fun i => if i.val = 0 then ρ else gc κ γ
  let L2 : Fin 2 → Nat → Prop := fun i => if i.val = 0 then Lx else fun j => Lγ (sN κ j)
  have i01 : ∀ i : Fin 2, i = 0 ∨ i = 1 := fun i => by
    match i with
    | ⟨0, _⟩ => exact Or.inl rfl
    | ⟨1, _⟩ => exact Or.inr rfl
  refine tcelG (ρ := ρ2) (Lp := L2) law2 C H_RST H_RST_LONG H_LAT H_PWR (fun i j => ?_)
    (fun j s h => ?_) (fun j => ?_) hcR (fun i j hj hl => ?_) (fun i => ?_)
  · rw [H_C]; rcases i01 i with rfl | rfl
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  · rw [H_C] at h
    by_cases h1 : s < ρ j
    · exact ⟨0, h1⟩
    · exact ⟨1, by show s < gc κ γ j; omega⟩
  · rw [H_CNT]
    constructor
    · intro ⟨a, b'⟩ i; rcases i01 i with rfl | rfl
      · exact a
      · exact b'
    · intro h; exact ⟨h 0, h 1⟩
  · rcases i01 i with rfl | rfl
    · exact (H_SND j hj).1 hl
    · exact (H_SND j hj).2 hl
  · rcases i01 i with rfl | rfl
    · exact hx
    · exact hg

/-! ## 4. The acknowledge / request OR, truncated -/

section or
variable {σ : Nat → Bool} {a : Bool → Nat → Bool} {α : Bool → Nat → Nat}
  {La : Bool → Nat → Prop} {κ : Bool → Nat → Nat} {T : Nat}

/-- The OR's merged edge `k` exists iff its token's edge exists on the token's branch. -/
def Lor (σ : Nat → Bool) (La : Bool → Nat → Prop) (k : Nat) : Prop :=
  La (σ (k / 2)) (2 * cnt σ (σ (k / 2)) (k / 2) + k % 2)

theorem lor_even (n : Nat) : Lor σ La (2 * n) ↔ La (σ n) (2 * cnt σ (σ n) n) := by
  unfold Lor; rw [show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega]; simp
theorem lor_odd (n : Nat) : Lor σ La (2 * n + 1) ↔ La (σ n) (2 * cnt σ (σ n) n + 1) := by
  unfold Lor; rw [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]

/-- **The OR `a₁ ∨ a₀` of two branch acknowledges, truncated.** The branches are clean on
`[0, T)` (edges `α b`, sets `La b`); token `n` is carried by branch `σ n`, and `κ b`
enumerates branch `b`'s tokens; H_DOWN and H_ORD: the merged edges `oe` exist in order and
increase (the two branches interleave in token order, an edge-time hypothesis). Then the OR
is clean on `[0, T)` with edges `oe` and edge set `Lor`. A branch that never fires again
is constant: no later token is needed. -/
theorem tor_ex
    (hκ : ∀ b m, κ b m < κ b (m + 1)) (hκb : ∀ b m, σ (κ b m) = b)
    (hκall : ∀ b n, σ n = b → ∃ m, κ b m = n)
    (H_DOWN : ∀ k, Lor σ La (k + 1) → Lor σ La k)
    (H_ORD : ∀ k, Lor σ La (k + 1) → oe σ α k < oe σ α (k + 1))
    (ha : ∀ b, GPhT (a b) (α b) (La b) T) :
    GPhT (fun t => a true t || a false t) (oe σ α) (Lor σ La) T := by
  have om := mono_ex H_DOWN H_ORD
  have dn := down_ex H_DOWN
  have ck : ∀ b m, cnt σ b (κ b m) = m := fun b =>
    cnt_kappa (hκ b) (hκb b) (hκall b)
  -- branch `b`'s edge `2m + r` is the merged edge of its `m`-th token
  have ea : ∀ b m r, r < 2 → α b (2 * m + r) = oe σ α (2 * κ b m + r) := by
    intro b m r hr
    unfold oe
    rw [show (2 * κ b m + r) / 2 = κ b m by omega, show (2 * κ b m + r) % 2 = r by omega,
      hκb b m, ck b m]
  have la : ∀ b m r, r < 2 → (La b (2 * m + r) ↔ Lor σ La (2 * κ b m + r)) := by
    intro b m r hr
    unfold Lor
    rw [show (2 * κ b m + r) / 2 = κ b m by omega, show (2 * κ b m + r) % 2 = r by omega,
      hκb b m, ck b m]
  -- tokens before / after `n` on branch `b`
  have before : ∀ b m n, m < cnt σ b n → κ b m < n := by
    intro b m n h
    apply Classical.byContradiction; intro hc
    have := cnt_mono σ b (show n ≤ κ b m by omega); rw [ck] at this; omega
  have after : ∀ b m n, cnt σ b n ≤ m → n ≤ κ b m := by
    intro b m n h
    apply Classical.byContradiction; intro hc
    have := cnt_mono σ b (show κ b m + 1 ≤ n by omega)
    rw [cnt_succ_eq (hκb b m), ck] at this; omega
  have kinj : ∀ b m n, σ n ≠ b → κ b m ≠ n := fun b m n h e => h (e ▸ hκb b m)
  -- a branch is low in the gap of merged edges `[oe (2n+1), oe (2n+2))`, or before `oe 0`
  have low : ∀ b t, t < T → ∀ n, (∀ m, n ≤ κ b m → σ (κ b m) = b →
      (La b (2 * m) → t < α b (2 * m))) →
      (∀ m, κ b m < n → La b (2 * m + 1) ∧ α b (2 * m + 1) ≤ t) →
      a b t = false := by
    intro b t ht n hA hB
    by_cases hc : cnt σ b n = 0
    · refine (ha b).pre t ht ?_
      by_cases h0 : La b 0
      · exact Or.inr (by
          have := hA 0 (after b 0 n (by omega)) (hκb b 0) (by simpa using h0)
          simpa using this)
      · exact Or.inl h0
    · obtain ⟨d, hd⟩ : ∃ d, cnt σ b n = d + 1 := ⟨cnt σ b n - 1, by omega⟩
      obtain ⟨l1, l2⟩ := hB d (before b d n (by omega))
      have := (ha b).ph (2 * d + 1) t ht l1 l2 (fun h => by
        have := hA (d + 1) (after b (d + 1) n (by omega)) (hκb b _)
          (by rw [show 2 * (d + 1) = 2 * d + 1 + 1 by omega]; exact h)
        rw [show 2 * (d + 1) = 2 * d + 1 + 1 by omega] at this; exact this)
      rw [this]; exact PipeTimed.Vph_odd d
  refine ⟨fun t ht h => ?_, fun k t ht hk h1 h2 => ?_⟩
  · -- before the first merged edge both branches are low
    have hb : ∀ b, a b t = false := fun b => low b t ht 0 (fun m _ _ hl => by
        have l := (la b m 0 (by omega)).1 (by simpa using hl)
        have l0 := dn 0 _ (Nat.zero_le _) l
        rcases h with h | h
        · exact absurd l0 h
        · rw [show 2 * m = 2 * m + 0 by omega, ea b m 0 (by omega)]
          have := om 0 _ (Nat.zero_le _) l; omega)
      (fun m h => absurd h (Nat.not_lt_zero _))
    show (a true t || a false t) = false
    rw [hb true, hb false]; rfl
  · obtain ⟨n, rfl | rfl⟩ : ∃ n, k = 2 * n ∨ k = 2 * n + 1 := ⟨k / 2, by omega⟩
    · -- high phase of token `n`: its branch is high
      have hl := (lor_even (σ := σ) (La := La) n).1 hk
      have e1 := oe_even σ α n
      have hv : a (σ n) t = true := by
        rw [(ha (σ n)).ph (2 * cnt σ (σ n) n) t ht hl (by omega) (fun h => by
          have := h2 ((lor_odd n).2 h); rw [oe_odd] at this; exact this)]
        exact PipeTimed.Vph_even _
      show (a true t || a false t) = Vph (2 * n)
      rw [PipeTimed.Vph_even]
      cases hs : σ n
      · rw [hs] at hv; rw [hv]; cases a true t <;> rfl
      · rw [hs] at hv; rw [hv]; rfl
    · -- low phase between tokens `n` and `n + 1`: both branches are low
      have hl := (lor_odd (σ := σ) (La := La) n).1 hk
      have e1 := oe_odd σ α n
      have upper : ∀ b m, n < κ b m → La b (2 * m) → t < α b (2 * m) := by
        intro b m hm hl'
        have l := (la b m 0 (by omega)).1 (by simpa using hl')
        have l2 := dn (2 * n + 1 + 1) _ (by omega) l
        have := h2 l2
        have := om (2 * n + 1 + 1) _ (by omega) l
        rw [show 2 * m = 2 * m + 0 by omega, ea b m 0 (by omega)]; omega
      have lower : ∀ b m, κ b m ≤ n → La b (2 * m + 1) ∧ α b (2 * m + 1) ≤ t := by
        intro b m hm
        have l := dn (2 * κ b m + 1) _ (by omega) hk
        refine ⟨(la b m 1 (by omega)).2 l, ?_⟩
        have := om (2 * κ b m + 1) _ (by omega) hk
        rw [ea b m 1 (by omega)]; omega
      have hb : ∀ b, a b t = false := by
        intro b
        refine low b t ht (n + 1) (fun m hm _ hl' => upper b m (by omega) hl')
          (fun m hm => lower b m (by omega))
      show (a true t || a false t) = Vph (2 * n + 1)
      rw [hb true, hb false, PipeTimed.Vph_odd]; rfl

end or

/-- **The REAL steer acknowledge OR `uack`, truncated.** -/
theorem tuack {σ : Nat → Bool} {a : Bool → Nat → Bool} {α : Bool → Nat → Nat}
    {La : Bool → Nat → Prop} {κ : Bool → Nat → Nat} {O : Nat → Bool} {lo hi T : Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_steer "uack" .O ["ack0", "ack1"]
      [a false t, a true t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_steer "uack" .O ["ack0", "ack1"]
      [a false t, a true t]) O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_FLOOR : ∀ k, Lor σ La k → hi ≤ oe σ α k + lo)
    (hκ : ∀ b m, κ b m < κ b (m + 1)) (hκb : ∀ b m, σ (κ b m) = b)
    (hκall : ∀ b n, σ n = b → ∃ m, κ b m = n)
    (H_DOWN : ∀ k, Lor σ La (k + 1) → Lor σ La k)
    (H_ORD : ∀ k, Lor σ La (k + 1) → oe σ α k < oe σ α (k + 1))
    (ha : ∀ b, GPhT (a b) (α b) (La b) T) :
    GPhT O (fe O lo hi (oe σ α)) (Lor σ La) (T + lo) := by
  have ex : (fun t => genF bd_steer "uack" .O ["ack0", "ack1"] [a false t, a true t]) =
      fun t => a true t || a false t := funext fun t => AssumeGuaranteeMuxOr.uack_gate _ _
  rw [ex] at H_LUT_WIN H_NO_REVERT
  exact tnode H_LUT_WIN H_NO_REVERT (tor_ex hκ hκb hκall H_DOWN H_ORD ha) H_FLOOR H_PWR

/-- **The REAL mux request OR `uor`, truncated.** -/
theorem tuor {σ : Nat → Bool} {a : Bool → Nat → Bool} {α : Bool → Nat → Nat}
    {La : Bool → Nat → Prop} {κ : Bool → Nat → Nat} {O : Nat → Bool} {lo hi T : Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_mux_W2 "uor" .O ["j0", "j1"] [a false t, a true t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_mux_W2 "uor" .O ["j0", "j1"]
      [a false t, a true t]) O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_FLOOR : ∀ k, Lor σ La k → hi ≤ oe σ α k + lo)
    (hκ : ∀ b m, κ b m < κ b (m + 1)) (hκb : ∀ b m, σ (κ b m) = b)
    (hκall : ∀ b n, σ n = b → ∃ m, κ b m = n)
    (H_DOWN : ∀ k, Lor σ La (k + 1) → Lor σ La k)
    (H_ORD : ∀ k, Lor σ La (k + 1) → oe σ α k < oe σ α (k + 1))
    (ha : ∀ b, GPhT (a b) (α b) (La b) T) :
    GPhT O (fe O lo hi (oe σ α)) (Lor σ La) (T + lo) := by
  have ex : (fun t => genF bd_mux_W2 "uor" .O ["j0", "j1"] [a false t, a true t]) =
      fun t => a true t || a false t := funext fun t => AssumeGuaranteeMuxOr.uor_gate _ _
  rw [ex] at H_LUT_WIN H_NO_REVERT
  exact tnode H_LUT_WIN H_NO_REVERT (tor_ex hκ hκb hκall H_DOWN H_ORD ha) H_FLOOR H_PWR

/-! ## 5. Non-vacuity of the truncated OR on a finite run -/

namespace WitOr

/-- Token 0 on branch `false` (high on `[2, 4)`), token 1 on branch `true` (high on
`[6, 8)`), then nothing: after token 1 branch `false` is idle FOREVER (Bmux2's H_LATER
fails for token 1), and during token 0's low phase the idle branch rises later. -/
def σw (n : Nat) : Bool := n % 2 == 1
def κw (b : Bool) (m : Nat) : Nat := 2 * m + (if b then 1 else 0)
def aw (b : Bool) (t : Nat) : Bool := if b then decide (6 ≤ t ∧ t < 8) else decide (2 ≤ t ∧ t < 4)
def αw (b : Bool) (j : Nat) : Nat := (if b then 6 else 2) + 2 * j
def Law (_ : Bool) (j : Nat) : Prop := j < 2

theorem cnt2 (b : Bool) : ∀ n, 2 ≤ n → 1 ≤ cnt σw b n := by
  intro n hn
  have h2 : cnt σw b 2 = 1 := by cases b <;> decide
  have := cnt_mono σw b hn; omega

theorem lor_w (k : Nat) : Lor σw Law k ↔ k < 4 := by
  unfold Lor Law
  by_cases hk : k < 4
  · have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide
  · have := cnt2 (σw (k / 2)) (k / 2) (by omega); omega

theorem oe_w (k : Nat) (hk : k < 4) : oe σw αw k = 2 + 2 * k := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide

theorem aw_ph (b : Bool) (T : Nat) : GPhT (aw b) (αw b) (Law b) T := by
  refine ⟨fun s _ h => ?_, fun j s _ hj h1 h2 => ?_⟩
  · have : s < αw b 0 := by
      rcases h with h | h
      · exact absurd (by unfold Law; omega) h
      · exact h
    cases b <;> simp [aw, αw] at this ⊢ <;> omega
  · unfold Law at hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · have h2' := h2 (by unfold Law; omega)
      cases b <;> simp [aw, αw, Vph, LinkTimed.Vph] at h1 h2' ⊢ <;> omega
    · cases b <;> simp [aw, αw, Vph, LinkTimed.Vph] at h1 ⊢ <;> omega

/-- **`tor_ex` has a witness on a finite run**: every hypothesis holds; the OR is clean
(high exactly on `[2, 4)` and `[6, 8)`, four edges, then quiet). -/
theorem tor_witness :
    (∀ b m, κw b m < κw b (m + 1)) ∧ (∀ b m, σw (κw b m) = b) ∧
    (∀ b n, σw n = b → ∃ m, κw b m = n) ∧
    (∀ k, Lor σw Law (k + 1) → Lor σw Law k) ∧
    (∀ k, Lor σw Law (k + 1) → oe σw αw k < oe σw αw (k + 1)) ∧
    (∀ b T, GPhT (aw b) (αw b) (Law b) T) ∧
    (∀ T, GPhT (fun t => aw true t || aw false t) (oe σw αw) (Lor σw Law) T) := by
  have hκ : ∀ b m, κw b m < κw b (m + 1) := fun b m => by cases b <;> simp [κw] <;> omega
  have hκb : ∀ b m, σw (κw b m) = b := fun b m => by
    cases b <;> simp [σw, κw] <;> omega
  have hκall : ∀ b n, σw n = b → ∃ m, κw b m = n := fun b n h => by
    refine ⟨n / 2, ?_⟩
    cases b <;> simp [σw, κw] at h ⊢ <;> omega
  have hD : ∀ k, Lor σw Law (k + 1) → Lor σw Law k := fun k h => by
    rw [lor_w] at h ⊢; omega
  have hO : ∀ k, Lor σw Law (k + 1) → oe σw αw k < oe σw αw (k + 1) := fun k h => by
    rw [lor_w] at h; rw [oe_w k (by omega), oe_w (k + 1) h]; omega
  exact ⟨hκ, hκb, hκall, hD, hO, aw_ph, fun T => tor_ex hκ hκb hκall hD hO (fun b => aw_ph b T)⟩

end WitOr

end Formal.Cells.FiniteNet
