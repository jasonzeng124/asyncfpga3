import Formal.Cells.UnionUp

/-!
# Formal.Cells.CovUp — a pin cover timed by an UPPER bound from the claim's anchor (shard B, 2026-11-09)

## Problem, plainly
A data-gate claim `c` (value `c.val` on `[τ(c.A) + c.a, τ(c.B) + c.b)`) is proved from its pins' covers; C's
`TimedX.CovTime` asks, per covered pin, a LOWER separation from the cover's start event to the claim's start event
(`Sep(w.A → c.A) = d`, `hi + w.a ≤ c.a + d`). So `c.A` must come after every cover's start. On THE target, pair
(12,18), the D cone of the register bank latched by SLICE_X30Y76.A6 contains SLICE_X28Y67.A6, whose two covers start
at the loads of two different registers (SLICE_X24Y77.A6(0), SLICE_X28Y65.A6(0)) that are causally unordered: no
single later anchor exists except the bank's own opening, and anchoring there makes the offsets grow along the
carry chain until the latch's re-open step fails (JOURNAL-B 2026-11-09 11:3x). The sound alternative: anchor the
claim at a COMMON ANCESTOR e0 of both loads and time each cover by an upper bound, `Up(e0 → w.A) = u`,
`hi + w.a + u ≤ c.a`. (Negative claim offsets, which a builder experiment used, are NOT allowed by C's `GateProof` /
`claim_stepR`: they need `0 ≤ c.a`, and the induction is causal.)

## Proved (core Lean, no Mathlib)
* `CovTimeU`: per pin, the start side by C's `Sep` form or by the new `Up` form (`1 ≤ hi + w.a` so the bound is
  used strictly in the past), the end side as in `CovTime`; `covTimeU_of_covTime`.
* `win_transferU`, `claim_stepU`: C's `win_transferR` / `claim_stepR` with `CovTimeU`, given `UpSoundT` one tick
  behind (what the induction step has).
* `GateProofU` (C's `GateProof` with `CovTimeU`), `gateProofU_of_gateProof`.

The AO main theorems with `GateProofU` claims are in `CovUpMain` (`timedA_follows_cu`, `timedA_live_cu`).

## Not shown
Any instance; the Boolean checker for `CovTimeU`.
-/

namespace Formal.Cells.CovUp
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR
  Formal.Net.OccNet.TimedU Formal.Cells.UnionUp

variable {α : Type} [DecidableEq α]

/-- Per covered pin: the cover's window contains the pin's read times. Start side by a separation (C's form) or by
an upper bound from the claim's anchor; end side by a separation. -/
def CovTimeU (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat) (c w : Claim α)
    (hiZ loZ : Nat) : Prop :=
  (match w.A with
    | none => True
    | some e' => (∃ e, c.A = some e ∧ ∃ d, Sep e'.1 e'.2 e.1 e.2 = some d ∧ (hiZ : Int) + w.a ≤ c.a + d) ∨
        (∃ e, c.A = some e ∧ ∃ u, Up e e' = some u ∧ 1 ≤ (hiZ : Int) + w.a ∧ (hiZ : Int) + w.a + u ≤ c.a)) ∧
  (match w.B with
    | none => True
    | some e' => ∃ e, c.B = some e ∧ ∃ d, Sep e.1 e.2 e'.1 e'.2 = some d ∧ c.b ≤ loZ + w.b + d)

omit [DecidableEq α] in
theorem covTimeU_of_covTime {Sep : α → Nat → α → Nat → Option Nat} {Up : α × Nat → α × Nat → Option Nat}
    {c w : Claim α} {hi lo : Nat} (h : CovTime Sep c w hi lo) : CovTimeU Sep Up c w hi lo := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  cases hwA : w.A with
  | none => trivial
  | some e' => rw [hwA] at h1; exact Or.inl h1

section lem
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {cl : List (Claim α)}
  {Sep : α → Nat → α → Nat → Option Nat} {Up : α × Nat → α × Nat → Option Nat}

theorem win_transferU (t : Nat) (hSS : SepSound x t0 Sep (t + 1)) (hUS : UpSoundT x t0 Up t)
    (c w : Claim α) (hi lo ρ' : Nat) (ha : 0 ≤ c.a) (hρ1 : t + 1 ≤ ρ' + hi) (hρ2 : ρ' + lo ≤ t + 1)
    (hct : CovTimeU Sep Up c w hi lo)
    (hA : match c.A with | none => True | some e => hbI x t0 e (((t + 1 : Nat) : Int) - c.a))
    (hBn : match c.B with | none => True | some e => ¬ hbI x t0 e (((t + 1 : Nat) : Int) - c.b)) :
    (match w.A with | none => True | some e => hbI x t0 e ((ρ' : Int) - w.a)) ∧
    (match w.B with | none => True | some e => ¬ hbI x t0 e ((ρ' : Int) - w.b)) := by
  obtain ⟨hcA, hcB⟩ := hct
  refine ⟨?_, ?_⟩
  · cases hwA : w.A with
    | none => trivial
    | some e' =>
      rw [hwA] at hcA
      rcases hcA with ⟨e, he, d, hd, hle⟩ | ⟨e, he, u, hU, h1, hle⟩
      · rw [he] at hA
        have := hSS e.1 e'.1 e.2 e'.2 d hd _ (by omega) hA
        exact hbI_mono this (by omega)
      · rw [he] at hA
        obtain ⟨h0, hc⟩ := hA
        have hτ := hUS e e' u (((t + 1 : Nat) : Int) - c.a).toNat hU hc (by omega)
        refine ⟨by omega, ?_⟩
        have : ((ρ' : Int) - w.a).toNat ≥ (((t + 1 : Nat) : Int) - c.a).toNat + u := by omega
        exact Nat.lt_of_lt_of_le hτ (cnt_mono e'.1 _ _ this)
  · cases hwB : w.B with
    | none => trivial
    | some e' =>
      rw [hwB] at hcB
      obtain ⟨e, he, d, hd, hle⟩ := hcB
      rw [he] at hBn
      intro hE
      have hpos := hE.1
      have := hSS e'.1 e.1 e'.2 e.2 d hd _ (by omega) hE
      exact hBn (hbI_mono this (by omega))

/-- **One step for a data-gate claim, covers timed by `CovTimeU`** (C's `claim_stepR`, proof copied). -/
theorem claim_stepU (hb : TBehX N dat envEn x r t0 H) (t : Nat) (ht : t0 ≤ t) (hSS : SepSound x t0 Sep (t + 1))
    (hUS : UpSoundT x t0 Up t)
    (hC : ∀ c ∈ cl, ∀ s, s ≤ t → Holds x t0 H c s)
    (c : Claim α) (hgz : N.gate c.z = true) (ha : 0 ≤ c.a) (cov : α → Cov)
    (hval : ValOK N (fun w => x w t0) cl c cov)
    (hcov : ∀ u ∈ N.pins c.z, ∀ w, covWin (fun w => x w t0) cl u (cov u) = some w →
      CovTimeU Sep Up c w (N.hi c.z u) (N.lo c.z u))
    (hkind : ∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧
      (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u)) :
    Holds x t0 H c (t + 1) := by
  intro _ hA hBn
  rw [hb.geq c.z (t + 1) hgz (by omega)]
  apply hval
  intro u hu w hw
  obtain ⟨r1, r2, r3, r4⟩ := hb.rd c.z u (t + 1) hgz hu (by omega)
  have hlo := hb.lo1 c.z u hgz hu
  obtain ⟨wA, wB⟩ := win_transferU t hSS hUS c w (N.hi c.z u) (N.lo c.z u) (r c.z u (t + 1))
    ha (by omega) (by omega) (hcov u hu w hw) hA hBn
  obtain ⟨hk1, hk2⟩ := hkind u hu
  cases hc : cov u with
  | X => rw [hc] at hw; simp [covWin] at hw
  | cl i =>
    rw [hc] at hw
    simp only [covWin] at hw
    have hwz := hk2 i w hc hw
    have hwm : w ∈ cl := List.mem_of_getElem? hw
    have := hC w hwm (r c.z u (t + 1)) (by omega) (by omega) wA wB
    rw [hwz] at this; exact this
  | ex k =>
    rw [hc] at hw
    simp only [covWin, Option.some.injEq] at hw
    subst hw
    have hdu := hk1 k hc
    simp only at wA wB
    have hcnt : cnt x t0 u (r c.z u (t + 1)) = k := by
      have hle : cnt x t0 u (r c.z u (t + 1)) ≤ k := by
        rcases Nat.lt_or_ge k (cnt x t0 u (r c.z u (t + 1))) with h | h
        · exact absurd ⟨by omega, by simpa using h⟩ wB
        · exact h
      by_cases hk0 : k = 0
      · omega
      · simp only [hk0, if_false] at wA
        have := wA.2; simp at this; omega
    rw [x_eq_st u H (fun s' h1 h2 => hb.quiet u s' hdu h1 h2) _ r4]
    simp only [st, hcnt]

end lem

/-- C's `GateProof` with `CovTimeU`. -/
def GateProofU (N : TNet α) (dat : α → Bool) (Sep : α → Nat → α → Nat → Option Nat)
    (Up : α × Nat → α × Nat → Option Nat) (s0 : α → Bool) (cl : List (Claim α)) (c : Claim α) : Prop :=
  N.gate c.z = true ∧ 0 ≤ c.a ∧ ∃ cov : α → Cov, ValOK N s0 cl c cov ∧
    (∀ u ∈ N.pins c.z, ∀ w, covWin s0 cl u (cov u) = some w → CovTimeU Sep Up c w (N.hi c.z u) (N.lo c.z u)) ∧
    (∀ u ∈ N.pins c.z, (∀ k, cov u = .ex k → dat u = false) ∧ (∀ i w, cov u = .cl i → cl[i]? = some w → w.z = u))

theorem gateProofU_of_gateProof {N : TNet α} {dat : α → Bool} {Sep : α → Nat → α → Nat → Option Nat}
    {Up : α × Nat → α × Nat → Option Nat} {s0 : α → Bool} {cl : List (Claim α)} {c : Claim α}
    (h : GateProof N dat Sep s0 cl c) : GateProofU N dat Sep Up s0 cl c := by
  obtain ⟨hg, ha, cov, hv, hc, hk⟩ := h
  exact ⟨hg, ha, cov, hv, fun u hu w hw => covTimeU_of_covTime (hc u hu w hw), hk⟩

end Formal.Cells.CovUp
