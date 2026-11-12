import Formal.Cells.RingPhysWit

/-!
# Probe Bring (shard B), part 4: a live 5-stage ring with TWO tokens (`2t + 1 = 5`)

Non-vacuity of the `t = 2` case of `RingPhys.ring_k_tokens` at its tight point: C's
`kState 2` on `N = 5` (stages 0 and 2 are `bd_c2n_set`, stages 1, 3, 4 are `bd_c2n`;
`D = 4`), the same delays as `RingPhysWit` (`Win 1 3` LUTs with actual delay 1, all wires
and feedback 1, reset 4). Every node has period 20 (`τ i j = o i + 10 j`,
`o = 11, 9, 7, 5, 13`). All hypotheses hold, H_LAT with equality. With `ring_frozen_D`
(`N = 4`, two tokens: `D = N`, frozen for every trace) this brackets the physical
two-token threshold exactly at C's `2t + 1`.
-/

namespace Formal.Cells.RingPhys.Wit2
open Formal.Cells Formal.Net Formal.Cells.RingPhys
open Formal.Cells.WinFifo (Win)
open Formal.Cells.WinFifoCausal (nt nt_eq Stage cph τs NoRevertI noRevertI_shift)
open Formal.Cells.PipeTimed (Vph ex)
open Formal.Cells.PipeTimed.Wit (rstW)
open Formal.Cells.LutFbBridge2Env (ε ash)
open Formal.Net.Ring (prv nxt)
open Formal.Cells.RingPhys.Wit (win_shift rstW_per)

/-- Square wave of period 20: low before `o`, then high 10, low 10, ... -/
def sq20 (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 20 < 10)

theorem sq20_shift (o d t : Nat) : sq20 (o + d) (t + d) = sq20 o t := by
  unfold sq20
  have e : t + d - (o + d) = t - o := by omega
  rw [e]
  by_cases h : o ≤ t
  · simp [h, show o + d ≤ t + d by omega]
  · simp [h, show ¬ (o + d ≤ t + d) by omega]

theorem sq20_pre (o t : Nat) (h : t < o) : sq20 o t = false := by unfold sq20; simp; omega

theorem sq20_phase (o j t : Nat) (h1 : o + 10 * j ≤ t) (h2 : t < o + 10 * (j + 1)) :
    sq20 o t = Vph j := by
  unfold sq20 Vph LinkTimed.Vph
  by_cases hj : j % 2 = 0
  · have : (t - o) % 20 < 10 := by omega
    simp [hj, this, show o ≤ t by omega]
  · have : ¬ ((t - o) % 20 < 10) := by omega
    simp [hj, this]

theorem sq20_per (o s : Nat) (h : o ≤ s) : sq20 o (s + 20) = sq20 o s := by
  unfold sq20
  have e : (s + 20 - o) % 20 = (s - o) % 20 := by omega
  rw [e]; simp [h, show o ≤ s + 20 by omega]

/-- The reset pattern: stage 0 holds the token. -/
def bW : Nat → Bool := Ring.kState 2

/-- First edge of each node. -/
def oW : Nat → Nat
  | 0 => 11
  | 1 => 9
  | 2 => 7
  | 3 => 5
  | _ => 13

/-- Node `i`, delayed by `d`. -/
def Od (i d : Nat) (t : Nat) : Bool := cond (bW i) (!sq20 (oW i + d) t) (sq20 (oW i + d) t)

theorem Od_shift (i t : Nat) : Od i 1 (t + 1) = Od i 0 t := by
  unfold Od; rw [sq20_shift (oW i) 1 t, Nat.add_zero]

theorem Od_per (i d s : Nat) (h : oW i + d ≤ s) : Od i d (s + 20) = Od i d s := by
  unfold Od; rw [sq20_per _ _ h]

theorem oW_le (i : Nat) : oW i ≤ 13 := by unfold oW; split <;> omega

theorem eq_of_per {f g : Nat → Bool} (h0 : ∀ s, s < 40 → f s = g s)
    (hf : ∀ s, 20 ≤ s → f (s + 20) = f s) (hg : ∀ s, 20 ≤ s → g (s + 20) = g s) :
    ∀ s, f s = g s := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    by_cases h : s < 40
    · exact h0 s h
    · have e : s = (s - 20) + 20 := by omega
      rw [e, hf _ (by omega), hg _ (by omega)]; exact ih _ (by omega)

theorem rstW_per20 (s : Nat) (h : 4 ≤ s) : rstW (s + 20) = rstW s := by
  unfold rstW; simp; omega

/-! ## The five excitations (real INITs) are the nodes, one tick early -/

theorem exs (a b c : Nat) (h0 : ∀ s, s < 40 →
    exS (Od a 1) (Od b 1) (Od c 1) rstW s = Od c 0 (s + 1)) :
    ∀ s, exS (Od a 1) (Od b 1) (Od c 1) rstW s = Od c 0 (s + 1) := by
  refine eq_of_per h0 (fun s hs => ?_) (fun s hs => ?_)
  · unfold exS
    rw [Od_per a 1 s (by have := oW_le a; omega), Od_per b 1 s (by have := oW_le b; omega),
      Od_per c 1 s (by have := oW_le c; omega), rstW_per20 s (by omega)]
  · rw [show s + 20 + 1 = (s + 1) + 20 by omega, Od_per c 0 (s + 1) (by have := oW_le c; omega)]

theorem exr (a b c : Nat) (h0 : ∀ s, s < 40 →
    ex (Od a 1) (Od b 1) (Od c 1) rstW s = Od c 0 (s + 1)) :
    ∀ s, ex (Od a 1) (Od b 1) (Od c 1) rstW s = Od c 0 (s + 1) := by
  refine eq_of_per h0 (fun s hs => ?_) (fun s hs => ?_)
  · unfold ex
    rw [Od_per a 1 s (by have := oW_le a; omega), Od_per b 1 s (by have := oW_le b; omega),
      Od_per c 1 s (by have := oW_le c; omega), rstW_per20 s (by omega)]
  · rw [show s + 20 + 1 = (s + 1) + 20 by omega, Od_per c 0 (s + 1) (by have := oW_le c; omega)]

theorem ex0 : ∀ s, exS (Od 4 1) (Od 1 1) (Od 0 1) rstW s = Od 0 0 (s + 1) := exs 4 1 0 (by decide)
theorem ex1 : ∀ s, ex (Od 0 1) (Od 2 1) (Od 1 1) rstW s = Od 1 0 (s + 1) := exr 0 2 1 (by decide)
theorem ex2 : ∀ s, exS (Od 1 1) (Od 3 1) (Od 2 1) rstW s = Od 2 0 (s + 1) := exs 1 3 2 (by decide)
theorem ex3 : ∀ s, ex (Od 2 1) (Od 4 1) (Od 3 1) rstW s = Od 3 0 (s + 1) := exr 2 4 3 (by decide)
theorem ex4 : ∀ s, ex (Od 3 1) (Od 0 1) (Od 4 1) rstW s = Od 4 0 (s + 1) := exr 3 0 4 (by decide)

theorem fb_Od (i : Nat) : CElemTiming.WinDelay 1 1 (Od i 0) (Od i 1) :=
  CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun t => Od_shift i t)

theorem wire_Od (i : Nat) : WireB (bW i) 1 1 (Od i 0) (Od i 1) := by
  have hx : ∀ t, 1 ≤ t → Od i 1 t = Od i 0 (t - 1) := fun t ht => by
    rw [← Od_shift i (t - 1), Nat.sub_add_cancel ht]
  refine ⟨fb_Od i, noRevertI_shift hx, Nat.le_refl 1, fun t ht => ?_⟩
  have : t = 0 := by omega
  subst this
  unfold Od; rw [sq20_pre _ 0 (by omega)]; cases bW i <;> rfl

/-! ## The ring data -/

def wD : RingData where
  N := 5
  R := 4
  b := bW
  O i := Od i 0
  req i := Od (prv 5 i) 1
  ack i := Od (nxt 5 i) 1
  qp i := Od i 1
  rst := rstW
  lo _ := 1
  hi _ := 3
  fl _ := 1
  fh _ := 1
  wl _ := 1
  wh _ := 1
  vl _ := 1
  vh _ := 1
  τ i j := oW i + 10 * j

theorem i5 (i : Nat) (h : i < 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega

theorem w_stage (i : Nat) (h : i < 5) :
    StageB (wD.b i) (wD.req i) (wD.ack i) wD.rst (wD.O i) (wD.qp i) 1 3 1 1 := by
  rcases i5 i h with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hW, hN⟩ := win_shift ex0
    exact (⟨hW, hN, fb_Od 0, by decide⟩ : SetStage _ _ _ _ _ 1 3 1 1)
  · obtain ⟨hW, hN⟩ := win_shift ex1
    exact (⟨hW, hN, fb_Od 1, by decide⟩ : Stage _ _ _ _ _ 1 3 1 1)
  · obtain ⟨hW, hN⟩ := win_shift ex2
    exact (⟨hW, hN, fb_Od 2, by decide⟩ : SetStage _ _ _ _ _ 1 3 1 1)
  · obtain ⟨hW, hN⟩ := win_shift ex3
    exact (⟨hW, hN, fb_Od 3, by decide⟩ : Stage _ _ _ _ _ 1 3 1 1)
  · obtain ⟨hW, hN⟩ := win_shift ex4
    exact (⟨hW, hN, fb_Od 4, by decide⟩ : Stage _ _ _ _ _ 1 3 1 1)

theorem On_eq (i : Nat) : wD.On i = sq20 (oW i) := by
  funext t; show cond (bW i) (!Od i 0 t) (Od i 0 t) = _
  unfold Od; rw [Nat.add_zero]; cases bW i <;> simp

theorem εF_eq (i j : Nat) : wD.εF i j = oW (prv 5 i) + 1 + 10 * j := by
  show nt (xr (bW (prv 5 i)) (Od (prv 5 i) 1)) 1 1 (oW (prv 5 i) + 10 * j) (Vph j) = _
  rw [nt_eq _ (Nat.le_refl 1) (by
    show cond (bW (prv 5 i)) (!Od (prv 5 i) 1 _) (Od (prv 5 i) 1 _) = _
    unfold Od
    rw [sq20_phase (oW (prv 5 i) + 1) j _ (by omega) (by omega)]
    cases bW (prv 5 i) <;> simp)]
  omega

theorem εB_eq (i j : Nat) : wD.εB i j = oW (nxt 5 i) + 1 + 10 * j := by
  show nt (xr (bW (nxt 5 i)) (Od (nxt 5 i) 1)) 1 1 (oW (nxt 5 i) + 10 * j) (Vph j) = _
  rw [nt_eq _ (Nat.le_refl 1) (by
    show cond (bW (nxt 5 i)) (!Od (nxt 5 i) 1 _) (Od (nxt 5 i) 1 _) = _
    unfold Od
    rw [sq20_phase (oW (nxt 5 i) + 1) j _ (by omega) (by omega)]
    cases bW (nxt 5 i) <;> simp)]
  omega

theorem tk0 : wD.tk 0 = true := by decide
theorem tk1 : wD.tk 1 = true := by decide
theorem tk2 : wD.tk 2 = true := by decide
theorem tk3 : wD.tk 3 = true := by decide
theorem tk4 : wD.tk 4 = false := by decide

theorem nt_sq (o c j : Nat) (h : c + 1 = o + 10 * j) : nt (sq20 o) 1 3 c (Vph j) = c + 1 :=
  nt_eq _ (by decide) (sq20_phase o j _ (by omega) (by omega))

theorem cph0 (j : Nat) : cph (wD.ρR 0) (wD.αR 0) j = 10 + 10 * j := by
  have hρ : wD.ρR 0 = ash 4 (wD.εF 0) := by unfold RingData.ρR; rw [tk0]; rfl
  have hα : wD.αR 0 = wD.εB 0 := by
    unfold RingData.αR; rw [show nxt wD.N 0 = 1 from rfl, tk1]; rfl
  unfold cph; rw [hρ, hα, εB_eq]
  cases j with
  | zero => rfl
  | succ j' =>
    show max (wD.εF 0 j') _ = _
    rw [εF_eq]; show max (oW 4 + 1 + 10 * j') (oW 1 + 1 + 10 * (j' + 1)) = _
    simp only [oW]; omega

theorem cph1 (j : Nat) : cph (wD.ρR 1) (wD.αR 1) j = 8 + 10 * j := by
  have hρ : wD.ρR 1 = ash 4 (wD.εF 1) := by unfold RingData.ρR; rw [tk1]; rfl
  have hα : wD.αR 1 = wD.εB 1 := by
    unfold RingData.αR; rw [show nxt wD.N 1 = 2 from rfl, tk2]; rfl
  unfold cph; rw [hρ, hα, εB_eq]
  cases j with
  | zero => rfl
  | succ j' =>
    show max (wD.εF 1 j') _ = _
    rw [εF_eq]; show max (oW 0 + 1 + 10 * j') (oW 2 + 1 + 10 * (j' + 1)) = _
    simp only [oW]; omega

theorem cph2 (j : Nat) : cph (wD.ρR 2) (wD.αR 2) j = 6 + 10 * j := by
  have hρ : wD.ρR 2 = ash 4 (wD.εF 2) := by unfold RingData.ρR; rw [tk2]; rfl
  have hα : wD.αR 2 = wD.εB 2 := by
    unfold RingData.αR; rw [show nxt wD.N 2 = 3 from rfl, tk3]; rfl
  unfold cph; rw [hρ, hα, εB_eq]
  cases j with
  | zero => rfl
  | succ j' =>
    show max (wD.εF 2 j') _ = _
    rw [εF_eq]; show max (oW 1 + 1 + 10 * j') (oW 3 + 1 + 10 * (j' + 1)) = _
    simp only [oW]; omega

theorem cph3 (j : Nat) : cph (wD.ρR 3) (wD.αR 3) j = 4 + 10 * j := by
  have hρ : wD.ρR 3 = ash 4 (wD.εF 3) := by unfold RingData.ρR; rw [tk3]; rfl
  have hα : wD.αR 3 = ash 4 (wD.εB 3) := by
    unfold RingData.αR; rw [show nxt wD.N 3 = 4 from rfl, tk4]; rfl
  unfold cph; rw [hρ, hα]
  cases j with
  | zero => rfl
  | succ j' =>
    show max (wD.εF 3 j') (wD.εB 3 j') = _
    rw [εF_eq, εB_eq]; show max (oW 2 + 1 + 10 * j') (oW 4 + 1 + 10 * j') = _
    simp only [oW]; omega

theorem cph4 (j : Nat) : cph (wD.ρR 4) (wD.αR 4) j = 12 + 10 * j := by
  have hρ : wD.ρR 4 = wD.εF 4 := by unfold RingData.ρR; rw [tk4]; rfl
  have hα : wD.αR 4 = wD.εB 4 := by
    unfold RingData.αR; rw [show nxt wD.N 4 = 0 from rfl, tk0]; rfl
  unfold cph; rw [hρ, hα, εF_eq, εB_eq]
  show max (oW 3 + 1 + 10 * j) (oW 0 + 1 + 10 * j) = _
  simp only [oW]; omega

theorem w_times (i : Nat) (h : i < 5) (j : Nat) :
    wD.τ i j = τs (wD.On i) (wD.lo i) (wD.hi i) (wD.ρR i) (wD.αR i) j := by
  rw [On_eq]
  show oW i + 10 * j = nt (sq20 (oW i)) 1 3 (cph (wD.ρR i) (wD.αR i) j) (Vph j)
  rcases i5 i h with rfl | rfl | rfl | rfl | rfl
  · rw [cph0, nt_sq _ _ _ (by simp only [oW]; omega)]; simp only [oW]; omega
  · rw [cph1, nt_sq _ _ _ (by simp only [oW]; omega)]; simp only [oW]; omega
  · rw [cph2, nt_sq _ _ _ (by simp only [oW]; omega)]; simp only [oW]; omega
  · rw [cph3, nt_sq _ _ _ (by simp only [oW]; omega)]; simp only [oW]; omega
  · rw [cph4, nt_sq _ _ _ (by simp only [oW]; omega)]; simp only [oW]; omega

theorem wit_ring : PRing wD where
  H_RST _ := rfl
  H_STAGE i h := w_stage i h
  H_PWR i h t ht := by
    show Od i 0 t = bW i
    have : t < oW i := by have : t < 3 := ht; unfold oW; split <;> omega
    unfold Od; rw [Nat.add_zero, sq20_pre _ _ this]; cases bW i <;> rfl
  H_LUT_POS _ _ := Nat.le_refl 1
  H_WF i _ := wire_Od (prv 5 i)
  H_WB i _ := wire_Od (nxt 5 i)
  H_TIMES := w_times
  H_TOK := ⟨0, by decide, tk0⟩

theorem wit_ringT : PRingT wD where
  H_RST_LONG _ _ := by show 3 + 1 ≤ 4; decide
  H_LAT _ _ := by show 3 + 1 ≤ 1 + min (1 + 1 + 1) (1 + 1 + 1); decide
  H_WIRE_R _ _ := by show 1 ≤ 4 ∧ 1 ≤ 4; decide
  H_RT _ _ := by show 1 ≤ 1 + 1 + 1 + 1 ∧ 1 ≤ 1 + 1 + 1 + 1; decide

/-- The reset pattern carries two loop tokens (`D = 4`, C's `D_kState`). -/
theorem wit_D0 : Ring.D 5 bW = 2 * 2 := Ring.D_kState (by decide) (by decide)

/-- **Two tokens circulate on `2·2 + 1 = 5` stages** (nonzero delays, at least two laps:
every node toggles at its first four edges, from `ring_toggles`); `D = 4` at every tick,
and every sampled state is C-reachable from `kState 2`. -/
theorem wit2_laps :
    (∀ i, i < 5 → ∀ j, j < 4 → wD.O i (wD.τ i j) ≠ wD.O i (wD.τ i j - 1)) ∧
    (∀ t, Ring.D 5 (st wD t) = 4) ∧ (∀ t, Ring.Reach 5 (Ring.kState 2) (st wD t)) :=
  ⟨fun i hi j _ => (ring_toggles wit_ring wit_ringT i hi j).2,
   fun t => (ring_tokens wit_ring wit_ringT t).trans wit_D0,
   fun t => ring_reach wit_ring wit_ringT t⟩

/-- **The other side of the two-token threshold**: on 4 stages, two tokens (`kState 2`,
`D = 4 = N`) give a frozen ring for EVERY trace (any delays), and no data satisfies the
hypotheses (`ring_k_tokens`). -/
theorem two_tokens_four_frozen : Ring.D 4 (Ring.kState 2) = 4 ∧
    ∀ D : RingData, D.N = 4 → D.b = Ring.kState 2 → ¬ (PRing D ∧ PRingT D) := by
  have hD : Ring.D 4 (Ring.kState 2) = 4 := Ring.D_kState (k := 2) (n := 4) (by decide) (by decide)
  refine ⟨hD, fun D hN hb ⟨C, T⟩ => ?_⟩
  have := ring_k_tokens C T 2 (by rw [hN, hb, hD])
  omega

end Formal.Cells.RingPhys.Wit2
