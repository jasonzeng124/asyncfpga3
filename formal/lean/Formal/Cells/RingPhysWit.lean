import Formal.Cells.RingPhys

/-!
# Probe Bring (shard B), part 3: a live 3-stage ring with one `_set` stage

Non-vacuity of `RingPhys.ring_nodes` / `ring_cond` / `ring_reach` / `ring_reset_live`:
C's `resetState 1` on `N = 3` (stage 0 is `bd_c2n_set`, stages 1, 2 are `bd_c2n`), every
gate its real INIT through a `Win 1 3` LUT channel (a band two ticks wide) with an actual
delay of 1 tick, every feedback wire and every inter-stage wire 1 tick, reset 4 ticks.

The run: events every 2 ticks in the order node 1 rises (5), node 0 falls (7), node 2 rises
(9), node 1 falls (11), node 0 rises (13), node 2 falls (15), ...; each node has period 12
(`τ i j = o i + 6 j` with `o = 7, 5, 9`). All hypotheses hold; H_LAT is met with EQUALITY
(`hi + fh = 4 = lo + min Es Ea`). The token makes infinitely many laps; `wit_laps` lists
the first two laps (four toggles per node), derived from `ring_toggles`, not evaluated.

Proved: `wit_ring`, `wit_ringT`, `wit_tau`, `wit_lat_eq`, `wit_laps`, `wit_reach` (every
sampled state of the run is reachable in C's `Ring` from `resetState 1`), `wit_D`
(`D = 2` at every tick), `ring2_no_run` (no 2-stage data satisfies the hypotheses). Core
Lean only.
-/

namespace Formal.Cells.RingPhys.Wit
open Formal.Cells Formal.Net Formal.Cells.RingPhys
open Formal.Cells.WinFifo (Win)
open Formal.Cells.WinFifoCausal (nt nt_eq Stage cph τs NoRevertI noRevertI_shift)
open Formal.Cells.PipeTimed (Vph ex)
open Formal.Cells.PipeTimed.Wit (rstW)
open Formal.Cells.LutFbBridge2Env (ε ash)
open Formal.Net.Ring (prv nxt)

/-- Square wave of period 12: low before `o`, then high 6, low 6, ... -/
def sq12 (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 12 < 6)

theorem sq12_shift (o d t : Nat) : sq12 (o + d) (t + d) = sq12 o t := by
  unfold sq12
  have e : t + d - (o + d) = t - o := by omega
  rw [e]
  by_cases h : o ≤ t
  · simp [h, show o + d ≤ t + d by omega]
  · simp [h, show ¬ (o + d ≤ t + d) by omega]

theorem sq12_pre (o t : Nat) (h : t < o) : sq12 o t = false := by unfold sq12; simp; omega

theorem sq12_phase (o j t : Nat) (h1 : o + 6 * j ≤ t) (h2 : t < o + 6 * (j + 1)) :
    sq12 o t = Vph j := by
  unfold sq12 Vph LinkTimed.Vph
  by_cases hj : j % 2 = 0
  · have : (t - o) % 12 < 6 := by omega
    simp [hj, this, show o ≤ t by omega]
  · have : ¬ ((t - o) % 12 < 6) := by omega
    simp [hj, this]

theorem sq12_per (o s : Nat) (h : o ≤ s) : sq12 o (s + 12) = sq12 o s := by
  unfold sq12
  have e : (s + 12 - o) % 12 = (s - o) % 12 := by omega
  rw [e]; simp [h, show o ≤ s + 12 by omega]

/-- The reset pattern: stage 0 holds the token. -/
def bW : Nat → Bool := Ring.resetState 1

/-- First edge of each node. -/
def oW : Nat → Nat
  | 0 => 7
  | 1 => 5
  | _ => 9

/-- Node `i`, delayed by `d`. -/
def Od (i d : Nat) (t : Nat) : Bool := cond (bW i) (!sq12 (oW i + d) t) (sq12 (oW i + d) t)

theorem Od_shift (i t : Nat) : Od i 1 (t + 1) = Od i 0 t := by
  unfold Od; rw [sq12_shift (oW i) 1 t, Nat.add_zero]

theorem Od_per (i d s : Nat) (h : oW i + d ≤ s) : Od i d (s + 12) = Od i d s := by
  unfold Od; rw [sq12_per _ _ h]

theorem rstW_per (s : Nat) (h : 4 ≤ s) : rstW (s + 12) = rstW s := by
  unfold rstW; simp; omega

/-- Two traces that agree below 24 and are both 12-periodic from 12 on agree everywhere. -/
theorem eq_of_per {f g : Nat → Bool} (h0 : ∀ s, s < 24 → f s = g s)
    (hf : ∀ s, 12 ≤ s → f (s + 12) = f s) (hg : ∀ s, 12 ≤ s → g (s + 12) = g s) :
    ∀ s, f s = g s := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    by_cases h : s < 24
    · exact h0 s h
    · have e : s = (s - 12) + 12 := by omega
      rw [e, hf _ (by omega), hg _ (by omega)]; exact ih _ (by omega)

theorem oW_le (i : Nat) : oW i ≤ 9 := by unfold oW; split <;> omega

/-! ## The three excitations (real INITs) are the nodes, one tick early -/

theorem ex0 : ∀ s, exS (Od 2 1) (Od 1 1) (Od 0 1) rstW s = Od 0 0 (s + 1) := by
  refine eq_of_per (by decide) (fun s hs => ?_) (fun s hs => ?_)
  · unfold exS
    rw [Od_per 2 1 s (by have := oW_le 2; omega), Od_per 1 1 s (by have := oW_le 1; omega),
      Od_per 0 1 s (by have := oW_le 0; omega), rstW_per s (by omega)]
  · rw [show s + 12 + 1 = (s + 1) + 12 by omega, Od_per 0 0 (s + 1) (by have := oW_le 0; omega)]

theorem ex1 : ∀ s, ex (Od 0 1) (Od 2 1) (Od 1 1) rstW s = Od 1 0 (s + 1) := by
  refine eq_of_per (by decide) (fun s hs => ?_) (fun s hs => ?_)
  · unfold ex
    rw [Od_per 0 1 s (by have := oW_le 0; omega), Od_per 2 1 s (by have := oW_le 2; omega),
      Od_per 1 1 s (by have := oW_le 1; omega), rstW_per s (by omega)]
  · rw [show s + 12 + 1 = (s + 1) + 12 by omega, Od_per 1 0 (s + 1) (by have := oW_le 1; omega)]

theorem ex2 : ∀ s, ex (Od 1 1) (Od 0 1) (Od 2 1) rstW s = Od 2 0 (s + 1) := by
  refine eq_of_per (by decide) (fun s hs => ?_) (fun s hs => ?_)
  · unfold ex
    rw [Od_per 1 1 s (by have := oW_le 1; omega), Od_per 0 1 s (by have := oW_le 0; omega),
      Od_per 2 1 s (by have := oW_le 2; omega), rstW_per s (by omega)]
  · rw [show s + 12 + 1 = (s + 1) + 12 by omega, Od_per 2 0 (s + 1) (by have := oW_le 2; omega)]

theorem win_shift {x O : Nat → Bool} (h : ∀ s, x s = O (s + 1)) :
    Win 1 3 x O ∧ NoRevertI 1 3 x O := by
  have hx : ∀ t, 1 ≤ t → O t = x (t - 1) := fun t ht => by
    rw [h (t - 1), Nat.sub_add_cancel ht]
  exact ⟨fun t ht => ⟨t - 1, by omega, by omega, hx t (by omega)⟩, noRevertI_shift hx⟩

theorem fb_Od (i : Nat) : CElemTiming.WinDelay 1 1 (Od i 0) (Od i 1) :=
  CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun t => Od_shift i t)

theorem wire_Od (i : Nat) : WireB (bW i) 1 1 (Od i 0) (Od i 1) := by
  have hx : ∀ t, 1 ≤ t → Od i 1 t = Od i 0 (t - 1) := fun t ht => by
    rw [← Od_shift i (t - 1), Nat.sub_add_cancel ht]
  refine ⟨fb_Od i, noRevertI_shift hx, Nat.le_refl 1, fun t ht => ?_⟩
  have : t = 0 := by omega
  subst this
  unfold Od; rw [sq12_pre _ 0 (by omega)]; cases bW i <;> rfl

/-! ## The ring data -/

def wD : RingData where
  N := 3
  R := 4
  b := bW
  O i := Od i 0
  req i := Od (prv 3 i) 1
  ack i := Od (nxt 3 i) 1
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
  τ i j := oW i + 6 * j

theorem i3 (i : Nat) (h : i < 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega

theorem w_stage (i : Nat) (h : i < 3) :
    StageB (wD.b i) (wD.req i) (wD.ack i) wD.rst (wD.O i) (wD.qp i) 1 3 1 1 := by
  rcases i3 i h with rfl | rfl | rfl
  · obtain ⟨hW, hN⟩ := win_shift ex0
    exact (⟨hW, hN, fb_Od 0, by decide⟩ : SetStage _ _ _ _ _ 1 3 1 1)
  · obtain ⟨hW, hN⟩ := win_shift ex1
    exact (⟨hW, hN, fb_Od 1, by decide⟩ : Stage _ _ _ _ _ 1 3 1 1)
  · obtain ⟨hW, hN⟩ := win_shift ex2
    exact (⟨hW, hN, fb_Od 2, by decide⟩ : Stage _ _ _ _ _ 1 3 1 1)

/-- The normalised node is the square wave. -/
theorem On_eq (i : Nat) : wD.On i = sq12 (oW i) := by
  funext t; show cond (bW i) (!Od i 0 t) (Od i 0 t) = _
  unfold Od; rw [Nat.add_zero]; cases bW i <;> simp

theorem εF_eq (i j : Nat) : wD.εF i j = oW (prv 3 i) + 1 + 6 * j := by
  show nt (xr (bW (prv 3 i)) (Od (prv 3 i) 1)) 1 1 (oW (prv 3 i) + 6 * j) (Vph j) = _
  rw [nt_eq _ (Nat.le_refl 1) (by
    show cond (bW (prv 3 i)) (!Od (prv 3 i) 1 _) (Od (prv 3 i) 1 _) = _
    unfold Od
    rw [sq12_phase (oW (prv 3 i) + 1) j _ (by omega) (by omega)]
    cases bW (prv 3 i) <;> simp)]
  omega

theorem εB_eq (i j : Nat) : wD.εB i j = oW (nxt 3 i) + 1 + 6 * j := by
  show nt (xr (bW (nxt 3 i)) (Od (nxt 3 i) 1)) 1 1 (oW (nxt 3 i) + 6 * j) (Vph j) = _
  rw [nt_eq _ (Nat.le_refl 1) (by
    show cond (bW (nxt 3 i)) (!Od (nxt 3 i) 1 _) (Od (nxt 3 i) 1 _) = _
    unfold Od
    rw [sq12_phase (oW (nxt 3 i) + 1) j _ (by omega) (by omega)]
    cases bW (nxt 3 i) <;> simp)]
  omega

theorem tk0 : wD.tk 0 = true := by decide
theorem tk1 : wD.tk 1 = true := by decide
theorem tk2 : wD.tk 2 = false := by decide

theorem nt_sq (o c j : Nat) (h : c + 1 = o + 6 * j) : nt (sq12 o) 1 3 c (Vph j) = c + 1 :=
  nt_eq _ (by decide) (sq12_phase o j _ (by omega) (by omega))

theorem ρ0 (j : Nat) : wD.ρR 0 j = ash 4 (wD.εF 0) j := by unfold RingData.ρR; rw [tk0]; rfl
theorem α0 (j : Nat) : wD.αR 0 j = wD.εB 0 j := by
  unfold RingData.αR; rw [show nxt wD.N 0 = 1 from rfl, tk1]; rfl
theorem ρ1 (j : Nat) : wD.ρR 1 j = ash 4 (wD.εF 1) j := by unfold RingData.ρR; rw [tk1]; rfl
theorem α1 (j : Nat) : wD.αR 1 j = ash 4 (wD.εB 1) j := by
  unfold RingData.αR; rw [show nxt wD.N 1 = 2 from rfl, tk2]; rfl
theorem ρ2 (j : Nat) : wD.ρR 2 j = wD.εF 2 j := by unfold RingData.ρR; rw [tk2]; rfl
theorem α2 (j : Nat) : wD.αR 2 j = wD.εB 2 j := by
  unfold RingData.αR; rw [show nxt wD.N 2 = 0 from rfl, tk0]; rfl

theorem cph0 (j : Nat) : cph (wD.ρR 0) (wD.αR 0) j = 6 + 6 * j := by
  unfold cph; rw [ρ0, α0, εB_eq]
  cases j with
  | zero => rfl
  | succ j' =>
    show max (wD.εF 0 j') _ = _
    rw [εF_eq]; show max (oW 2 + 1 + 6 * j') (oW 1 + 1 + 6 * (j' + 1)) = _
    simp only [oW]; omega

theorem cph1 (j : Nat) : cph (wD.ρR 1) (wD.αR 1) j = 4 + 6 * j := by
  unfold cph; rw [ρ1, α1]
  cases j with
  | zero => rfl
  | succ j' =>
    show max (wD.εF 1 j') (wD.εB 1 j') = _
    rw [εF_eq, εB_eq]; show max (oW 0 + 1 + 6 * j') (oW 2 + 1 + 6 * j') = _
    simp only [oW]; omega

theorem cph2 (j : Nat) : cph (wD.ρR 2) (wD.αR 2) j = 8 + 6 * j := by
  unfold cph; rw [ρ2, α2, εF_eq, εB_eq]
  show max (oW 1 + 1 + 6 * j) (oW 0 + 1 + 6 * j) = _
  simp only [oW]; omega

theorem w_times (i : Nat) (h : i < 3) (j : Nat) :
    wD.τ i j = τs (wD.On i) (wD.lo i) (wD.hi i) (wD.ρR i) (wD.αR i) j := by
  rw [On_eq]
  show oW i + 6 * j = nt (sq12 (oW i)) 1 3 (cph (wD.ρR i) (wD.αR i) j) (Vph j)
  rcases i3 i h with rfl | rfl | rfl
  · rw [cph0, nt_sq _ _ _ (by simp only [oW]; omega)]; simp only [oW]; omega
  · rw [cph1, nt_sq _ _ _ (by simp only [oW]; omega)]; simp only [oW]; omega
  · rw [cph2, nt_sq _ _ _ (by simp only [oW]; omega)]; simp only [oW]; omega

theorem wit_ring : PRing wD where
  H_RST _ := rfl
  H_STAGE i h := w_stage i h
  H_PWR i h t ht := by
    show Od i 0 t = bW i
    have : t < oW i := by have : t < 3 := ht; unfold oW; split <;> omega
    unfold Od; rw [Nat.add_zero, sq12_pre _ _ this]; cases bW i <;> rfl
  H_LUT_POS _ _ := Nat.le_refl 1
  H_WF i _ := wire_Od (prv 3 i)
  H_WB i _ := wire_Od (nxt 3 i)
  H_TIMES := w_times
  H_TOK := ⟨0, by decide, tk0⟩

theorem wit_ringT : PRingT wD where
  H_RST_LONG _ _ := by show 3 + 1 ≤ 4; decide
  H_LAT _ _ := by show 3 + 1 ≤ 1 + min (1 + 1 + 1) (1 + 1 + 1); decide
  H_WIRE_R _ _ := by show 1 ≤ 4 ∧ 1 ≤ 4; decide
  H_RT _ _ := by show 1 ≤ 1 + 1 + 1 + 1 ∧ 1 ≤ 1 + 1 + 1 + 1; decide

/-- The edge times of the run. -/
theorem wit_tau : ∀ j, wD.τ 0 j = 7 + 6 * j ∧ wD.τ 1 j = 5 + 6 * j ∧ wD.τ 2 j = 9 + 6 * j :=
  fun _ => ⟨rfl, rfl, rfl⟩

/-- H_LAT met with equality at every stage (`hi + fh = lo + min Es Ea = 4`). -/
theorem wit_lat_eq : ∀ i, wD.hi i + wD.fh i = wD.lo i + min (wD.Es i) (wD.Ea i) :=
  fun _ => rfl

/-- **Two laps (at least) with nonzero delays**: every node toggles at each of its first
four edges (two rises and two falls: the token passes every stage twice), from the
general theorem `ring_toggles`; and the hypotheses give `N ≥ 3` and `D = 2` at every
tick (`ring_reset_live`). -/
theorem wit_laps :
    (∀ i, i < 3 → ∀ j, j < 4 → wD.O i (wD.τ i j) ≠ wD.O i (wD.τ i j - 1)) ∧
    3 ≤ wD.N ∧ (∀ t, Ring.D wD.N (st wD t) = 2) := by
  refine ⟨fun i hi j _ => (ring_toggles wit_ring wit_ringT i hi j).2, ?_⟩
  obtain ⟨a, _, c⟩ := ring_reset_live wit_ring wit_ringT 1 (by decide) (by decide) rfl
  exact ⟨a, c⟩

/-- Every sampled state of the run is reachable in C's `Ring` from `resetState 1`. -/
theorem wit_reach (t : Nat) : Ring.Reach 3 (Ring.resetState 1) (st wD t) :=
  ring_reach wit_ring wit_ringT t

/-- **(4), the hypotheses side**: no 2-stage ring data satisfies the gate relations and
the timing rows (`ring_cond`); with `ring2_dead`, every 2-stage ring is frozen. -/
theorem ring2_no_run (D : RingData) (h : D.N = 2) : ¬ (PRing D ∧ PRingT D) := by
  intro ⟨C, T⟩; have := (ring_cond C T).1; omega

end Formal.Cells.RingPhys.Wit
