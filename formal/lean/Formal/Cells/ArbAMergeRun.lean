import Formal.Cells.ArbAMerge

/-!
# Probe Barb4 (part 1): the remaining epoch windows of the held `bd_arbiter`

Probe Barb3 (`ArbAMerge`) proved C's `OpsCM.AMerge` step fields for the held `bd_arbiter`
on the two HANDOVER windows (`E1`, `E2`). This file adds the windows for every other epoch
of a run, in the same form (exact traces on a window `[L, Hz)`, nothing assumed before `L`
but A0's last edge; C's six step fields `CF` at every 1 ps tick of `[L + M + dz, Hz - 1)`).
Core Lean; imports `ArbAMerge` (hence 7h, 7j, `ArbMultiToken`).

* `Anc`, `srv_lb`: the server anchor (A0's last edge, or the reset past) and the generic
  H_SERVER_MIN lower bound used by every window.
* `q1_win`, `g2_win0`, `A2_win0`, `A1_win0`, `g1_q1`, `R0_q1`: windows where q does not move.
* **WG** (grant from idle, client 1; a waiter may arrive once client 1 is ahead at ustate):
  `wg_q`, `wg_g1`, `wg_R0`, `wg_A1`, `wg_TA2`, `wg_excl`, **`wg_fields`**. No race.
* **WR** (client 1 releases with nobody waiting, may re-request at any `u > t0`: the solo
  client and the same client winning twice; `u ≥ Hz` = release to idle): `wr_*`,
  **`wr_fields`**. New race **RA1** (H_CEL_LOOP, `TF + wfa1 ≤ GU + wg1`: ua1's fall must come
  round its own feedback before the re-request's grant reaches ua1); **`cex_RA1`**: at slack
  −1 C's `xa` fails (A1 re-rises while A0 is low).
* **WX** (grant from idle to client 2, q flips; client 1 may follow): `wx_*`, **`wx_fields`**
  under **H_SEP** (`SepX`: client 1's request separated from client 2's by more than the loop
  at ustate, R0 and g1). **`cex_SEP`**: H_SEP's loop clause missed by 1 ps ⇒ q runt ⇒ C's
  H_ARB2 fails. `HSep`, **`race_fields`**: the idle-race epoch (WG ∨ WX) under H_SEP.
* **Hold** (`Md`, `InSt`, `Fix`, `hold_st`, **`hold_fields`**): a settled mode with constant
  inputs persists; every field holds.

**Assumed:** 7h's gate model `Run` (real INITs, rise-fast OR channel, routed delay per pin,
H_SERVER_MIN on R0), H_M (`MB`), the z line `ZLine` with H_DZ, each window's input pattern
(requests and the server's A0 edges as free parameters), and the named races and tick rows
(`RowsG`, `RowsR`, `RowsX`, RA1, RT2a, `SepX`, the four-phase client `TF < u`).
**Proved:** the exact traces, grant exclusion and C's step fields on each window; the slack
−1 counter lemmas `cex_RA1`, `cex_SEP`. **NOT covered:** the mirrors for client 2 alone
(client 2 releasing with nobody waiting, idle with q = 0, client 1 granted from q = 0); a
waiter arriving while the holder is releasing (between `t0` and the re-request); the tick
rows and SepX's R/G clauses have no counter lemma; the server reads R0, not z (as in
`ArbAMerge`). The concrete counter-run for H_SEP is `ArbAMergeRunWit.sep_cex_run`.
-/

namespace Formal.Cells.ArbAMergeRun
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2
open Formal.Cells.ArbMultiToken (MB Dw Dw_MB Dw_rt CArb)
open Formal.Cells.ArbAMerge

/-! ## Common tools -/

/-- The server anchor of a window whose A0 starts at value `c` at time `a`: either A0 was
in the other phase just before `a` (its last edge is at `a`), or (only for A0 low) A0 and
R0 have been low for ever before `a` (the reset past). -/
def Anc (s : Sigs) (c : Bool) (a : Int) : Prop :=
  s.A0 (a - 1) = !c ∨ (c = false ∧ ∀ t, t < a → s.R0 t = false)

/-- **The server lower bound, generic**: if A0 sits at `c` on `[a, T)` and flips at `T`,
and R0 sits at `c` on `[a, Rt)`, then H_SERVER_MIN gives `Rt + smin ≤ T`. -/
theorem srv_lb {D : Dl} {s : Sigs} (R : Run D s) {c : Bool} {a T Rt : Int} (hanc : Anc s c a)
    (haT : a < T) (hA0 : ∀ t, a ≤ t → t < T → s.A0 t = c) (hT : s.A0 T = !c)
    (hR0 : ∀ t, a ≤ t → t < Rt → t ≤ T → s.R0 t = c) : Rt + D.smin ≤ T := by
  have e0 : s.A0 (T - 1) = c := hA0 (T - 1) (by omega) (by omega)
  obtain ⟨v, hv, hR, hc⟩ := R.H_SRV T (by rw [hT, e0]; cases c <;> simp)
  rw [hT] at hR
  have hva : a ≤ v := by
    by_cases h : a ≤ v
    · exact h
    · rcases hanc with h1 | ⟨h1, h2⟩
      · have := hc (a - 1) (by omega) (by omega)
        rw [h1, e0] at this; cases c <;> simp at this
      · subst h1; rw [h2 v (by omega)] at hR; simp at hR
  by_cases h : Rt + D.smin ≤ T
  · exact h
  · have := hR0 v hva (by omega) (by have := D.H_NONNEG; omega); rw [hR] at this
    cases c <;> simp at this

theorem FS_q1 : ∀ r1 r2 a0 : Bool, FS r1 r2 true a0 = (a0 || r1 || !r2) := by decide
theorem FR_q1 : ∀ r1 r2 : Bool, FR r1 r2 true = r1 := by decide
theorem FG1_q1 : ∀ r1 r2 : Bool, FG1 r1 r2 true = r1 := by decide
theorem FG2_q1 : ∀ r1 r2 : Bool, FG2 r1 r2 true = false := by decide
theorem CE_g0 : ∀ a fb : Bool, CE false a fb = (a && fb) := by decide

section q1
variable {D : Dl} {M : Int} {s : Sigs}

/-- **q stays 1** on a window where every view of ustate that sees r2 high with A0 low
also sees r1 high (client 1 is never overtaken at ustate). -/
theorem q1_win (R : Run D s) (hM : MB D M) {L Hz : Int}
    (hq0 : ∀ t, L ≤ t → t < L + M → s.q t = true)
    (hsee : ∀ t, L + M ≤ t → t < Hz → s.r2 (t - D.wr2s - D.qr) = true →
      s.A0 (t - D.wa0s - D.qr) = false → s.r1 (t - D.wr1s - D.qr) = true) :
    ∀ t, L ≤ t → t < Hz → s.q t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS; have := hM.q
  refine int_ind_w (fun t => t < Hz → s.q t = true) L (L + M)
    (fun t h1 h2 _ => hq0 t h1 h2) ?_
  intro t ht ih hz
  have hfb := ih (t - D.wfb - D.qr) (by omega) (by omega) (by omega)
  rw [R.H_q t, hfb, FS_q1]
  by_cases h2 : s.r2 (t - D.wr2s - D.qr) = true
  · by_cases h0 : s.A0 (t - D.wa0s - D.qr) = false
    · simp [hsee t ht hz h2 h0]
    · simp at h0; simp [h0]
  · simp at h2; simp [h2]

theorem g2_win0 (R : Run D s) (hM : MB D M) {L Hz : Int}
    (hq : ∀ t, L ≤ t → t < Hz → s.q t = true)
    (hg0 : ∀ t, L ≤ t → t < L + M → s.g2 t = false) :
    ∀ t, L ≤ t → t < Hz → s.g2 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.g2
  intro t h1 h2
  by_cases hc : t < L + M
  · exact hg0 t h1 hc
  rw [R.H_g2 t, hq _ (by omega) (by omega), hq (t - D.wq - D.g2f) (by omega) (by omega),
    FG2_q1, FG2_q1]; rfl

theorem A2_win0 (R : Run D s) (hM : MB D M) {L Hz : Int}
    (hg : ∀ t, L ≤ t → t < Hz → s.g2 t = false)
    (ha0 : ∀ t, L ≤ t → t < L + M → s.A2 t = false) :
    ∀ t, L ≤ t → t < Hz → s.A2 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS; have := hM.A2
  refine int_ind_w (fun t => t < Hz → s.A2 t = false) L (L + M)
    (fun t h1 h2 _ => ha0 t h1 h2) ?_
  intro t ht ih hz
  rw [R.H_A2 t, hg _ (by omega) (by omega), hg (t - D.wg2 - D.c2f) (by omega) (by omega),
    CE_g0, CE_g0, ih (t - D.wfa2 - D.c2r) (by omega) (by omega) (by omega),
    ih (t - D.wfa2 - D.c2f) (by omega) (by omega) (by omega)]
  simp

theorem g1_q1 (R : Run D s) (hM : MB D M) {L Hz : Int}
    (hq : ∀ t, L ≤ t → t < Hz → s.q t = true) (t : Int) (h1 : L + M ≤ t) (h2 : t < Hz) :
    s.g1 t = (s.r1 (t - D.wr1g - D.g1r1) || s.r1 (t - D.wr1g - D.g1f1)) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.g1
  rw [R.H_g1 t, hq _ (by omega) (by omega), hq (t - D.wq - D.g1fq) (by omega) (by omega),
    FG1_q1, FG1_q1]

theorem R0_q1 (R : Run D s) (hM : MB D M) {L Hz : Int}
    (hq : ∀ t, L ≤ t → t < Hz → s.q t = true) (t : Int) (h1 : L + M ≤ t) (h2 : t < Hz) :
    s.R0 t = (s.r1 (t - D.wr1s - D.Rr1) || s.r1 (t - D.wr1s - D.Rf1)) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0
  rw [R.H_R0 t, hq _ (by omega) (by omega), hq (t - D.wfb - D.Rfq) (by omega) (by omega),
    FR_q1, FR_q1]

end q1

/-! ## Epoch WG: grant from idle (client 1), a waiter may arrive later

Idle settled state (q = 1, everything else low) on `[L, L + M)`; client 1 requests at
`u`; client 2 may request at `v` (any time, `v ≥ Hz` = never) provided its request reaches
ustate no earlier than client 1's (`sep`, the ordered case of H_SEP); the server raises A0
at `TA2` (free, `TA2 ≥ Hz` = not yet). q never moves, so there is no race. -/

structure WG (D : Dl) (M : Int) (s : Sigs) (a L u TA2 v Hz : Int) : Prop where
  ord : a ≤ L ∧ L + M ≤ u ∧ u < TA2 ∧ 1 ≤ M
  r1 : ∀ t, L ≤ t → t < Hz → s.r1 t = decide (u ≤ t)
  r2 : ∀ t, L ≤ t → t < Hz → s.r2 t = decide (v ≤ t)
  sep : u + D.wr1s ≤ v + D.wr2s
  A0 : ∀ t, a ≤ t → t < Hz → s.A0 t = decide (TA2 ≤ t)
  anc : Anc s false a
  R0a : ∀ t, a ≤ t → t < L + M → s.R0 t = false
  q0 : ∀ t, L ≤ t → t < L + M → s.q t = true
  g10 : ∀ t, L ≤ t → t < L + M → s.g1 t = false
  g20 : ∀ t, L ≤ t → t < L + M → s.g2 t = false
  A10 : ∀ t, L ≤ t → t < L + M → s.A1 t = false
  A20 : ∀ t, L ≤ t → t < L + M → s.A2 t = false

/-- g1's rise after a request at `u` (I0 rise arc). -/
def GU (D : Dl) (u : Int) : Int := u + D.wr1g + D.g1r1
/-- R0's rise after a request at `u` with q = 1 (I0 rise arc). -/
def RU (D : Dl) (u : Int) : Int := u + D.wr1s + D.Rr1
/-- A1's rise: g1 and A0 both seen high (rise arc). -/
def TU (D : Dl) (u TA2 : Int) : Int := max (GU D u + D.wg1) (TA2 + D.wa01) + D.c1r

/-- Tick rows of WG (run form): `g1p` H_TICK_CAUSAL, `a1` H_GRANT_IN_A0_LOW (g1 rises no
later than the earliest server re-rise), `zrise` H_ZR, `y1` H_ACK_IN_PHASE, `dz` H_DZ. -/
structure RowsG (D : Dl) (dz u TA2 : Int) : Prop where
  g1p : u < GU D u
  a1 : GU D u ≤ RU D u + D.smin
  zrise : GU D u < RU D u + dz
  y1 : GU D u < TU D u TA2 ∧ TA2 < TU D u TA2
  dz : 0 ≤ dz ∧ dz ≤ D.smin

section wg
variable {D : Dl} {M : Int} {s : Sigs} {a L u TA2 v Hz : Int}

theorem wg_q (R : Run D s) (hM : MB D M) (S : WG D M s a L u TA2 v Hz) :
    ∀ t, L ≤ t → t < Hz → s.q t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.q; have := S.ord; have := S.sep
  refine q1_win R hM S.q0 ?_
  intro t h1 h2 hr2 _
  rw [S.r2 _ (by omega) (by omega)] at hr2
  rw [S.r1 _ (by omega) (by omega)]; simp at hr2 ⊢; omega

theorem wg_g2 (R : Run D s) (hM : MB D M) (S : WG D M s a L u TA2 v Hz) :
    ∀ t, L ≤ t → t < Hz → s.g2 t = false := g2_win0 R hM (wg_q R hM S) S.g20

theorem wg_A2 (R : Run D s) (hM : MB D M) (S : WG D M s a L u TA2 v Hz) :
    ∀ t, L ≤ t → t < Hz → s.A2 t = false := A2_win0 R hM (wg_g2 R hM S) S.A20

theorem wg_g1 (R : Run D s) (hM : MB D M) (S : WG D M s a L u TA2 v Hz) (t : Int)
    (h1 : L ≤ t) (h2 : t < Hz) : s.g1 t = decide (GU D u ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.g1; have := S.ord
  by_cases hc : t < L + M
  · rw [S.g10 t h1 hc]; unfold GU; symm; simp; omega
  rw [g1_q1 R hM (wg_q R hM S) t (by omega) h2, S.r1 _ (by omega) (by omega),
    S.r1 _ (by omega) (by omega)]
  unfold GU; rw [Bool.eq_iff_iff]; simp; omega

theorem wg_R0 (R : Run D s) (hM : MB D M) (S : WG D M s a L u TA2 v Hz) (t : Int)
    (h1 : a ≤ t) (h2 : t < Hz) : s.R0 t = decide (RU D u ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0; have := S.ord
  by_cases hc : t < L + M
  · rw [S.R0a t h1 hc]; unfold RU; symm; simp; omega
  rw [R0_q1 R hM (wg_q R hM S) t (by omega) h2, S.r1 _ (by omega) (by omega),
    S.r1 _ (by omega) (by omega)]
  unfold RU; rw [Bool.eq_iff_iff]; simp; omega

theorem wg_TA2 (R : Run D s) (hM : MB D M) (S : WG D M s a L u TA2 v Hz) (hz : TA2 < Hz) :
    RU D u + D.smin ≤ TA2 := by
  have := S.ord
  refine srv_lb R S.anc (by omega) (fun t h1 h2 => ?_) ?_ (fun t h1 h2 h3 => ?_)
  · rw [S.A0 t h1 (by omega)]; simp; omega
  · rw [S.A0 TA2 (by omega) hz]; simp
  · rw [wg_R0 R hM S t h1 (by omega)]; simp; omega

theorem wg_A1 (R : Run D s) (hM : MB D M) (S : WG D M s a L u TA2 v Hz) :
    ∀ t, L ≤ t → t < Hz → s.A1 t = decide (TU D u TA2 ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A1
  refine int_ind_w (fun t => t < Hz → s.A1 t = decide (TU D u TA2 ≤ t)) L (L + M)
    (fun t h1 h2 _ => by
      rw [S.A10 t h1 h2]; symm; unfold TU GU; simp; omega) ?_
  intro t ht ih hz
  have g := fun d (h : 0 ≤ d) (h' : d ≤ D.c1f) => wg_g1 R hM S (t - D.wg1 - d) (by omega) (by omega)
  have a0 := fun d (h : 0 ≤ d) (h' : d ≤ D.c1f) => S.A0 (t - D.wa01 - d) (by omega) (by omega)
  have f := fun d (h : D.c1r ≤ d) (h' : d ≤ D.c1f) =>
    ih (t - D.wfa1 - d) (by omega) (by omega) (by omega)
  rw [R.H_A1 t, CE_eq, CE_eq, g _ (by omega) (Int.le_refl _), g _ (by omega) (by omega),
    a0 _ (by omega) (Int.le_refl _), a0 _ (by omega) (by omega),
    f _ (Int.le_refl _) (by omega), f _ (by omega) (Int.le_refl _)]
  unfold TU at *; unfold GU at *
  rw [Bool.eq_iff_iff]; simp; omega

theorem wg_excl (R : Run D s) (hM : MB D M) (S : WG D M s a L u TA2 v Hz) :
    ∀ t, L ≤ t → t < Hz → (s.g1 t && s.g2 t) = false := by
  intro t h1 h2; rw [wg_g2 R hM S t h1 h2]; simp

/-- **C's step fields on a grant-from-idle window** (client 1; a waiter may arrive with
`sep`). Assumed: the gate model, H_M, `WG`, the z line, `RowsG`. Proved: H_ARB1, H_ARB2,
zr, H_AMERGE_RTZ, xa, ya at every tick of `[L + M + dz, Hz - 1)`. No race condition. -/
theorem wg_fields (R : Run D s) (hM : MB D M) (S : WG D M s a L u TA2 v Hz)
    {z : Int → Bool} {dz : Int} (Z : ZLine s z dz) (K : RowsG D dz u TA2) :
    ∀ t, L + M + dz ≤ t → t + 1 < Hz → CF s z t := by
  have := S.ord; have := K.dz; have := K.g1p; have := K.a1; have := K.zrise; have := K.y1
  have := D.H_NONNEG
  have hT : TA2 < Hz → RU D u + D.smin ≤ TA2 := wg_TA2 R hM S
  have hT' : RU D u + D.smin ≤ TA2 ∨ Hz ≤ TA2 := by
    by_cases h : TA2 < Hz
    · exact Or.inl (hT h)
    · exact Or.inr (by omega)
  intro t h1 h2
  have g1t := wg_g1 R hM S t (by omega) (by omega)
  have g1u := wg_g1 R hM S (t + 1) (by omega) (by omega)
  have g2t := wg_g2 R hM S t (by omega) (by omega)
  have g2u := wg_g2 R hM S (t + 1) (by omega) (by omega)
  have a1t := wg_A1 R hM S t (by omega) (by omega)
  have a1u := wg_A1 R hM S (t + 1) (by omega) (by omega)
  have a2t := wg_A2 R hM S t (by omega) (by omega)
  have a2u := wg_A2 R hM S (t + 1) (by omega) (by omega)
  have zt := Z t
  have zu := Z (t + 1)
  rw [wg_R0 R hM S (t - dz) (by omega) (by omega)] at zt
  rw [wg_R0 R hM S (t + 1 - dz) (by omega) (by omega)] at zu
  have r1t := S.r1 t (by omega) (by omega)
  have a0t := S.A0 t (by omega) (by omega)
  unfold CF CArb
  rw [g1t, g1u, g2t, g2u, a1t, a1u, a2t, a2u, zt, zu, r1t, a0t]
  have e1 : TU D u TA2 ≥ TA2 + D.wa01 + D.c1r := by unfold TU; omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ne_eq, ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.or_false] <;> (try simp) <;> omega

end wg

/-! ## Epoch WR: client 1 releases with no waiter; it may re-request (solo, same client again)

Client 1 holds (settled H1 with r2 low) on `[L, L + M)`, drops r1 at `t0`, and may
re-request at any `u > t0` (`u ≥ Hz` = never: release to idle); the server drops A0 at
`TA` and may re-raise it at `TA2`; client 2 may request at `v` once client 1's re-request
is ahead of it at ustate (`sep`). q never moves. The new race is **RA1** (H_CEL_LOOP):
ua1's own fall must have come round its feedback pin before the re-request's grant reaches
ua1 (`TF + wfa1 ≤ GU + wg1`); its mirror for A0 is RT2a (`TF + wfa1 ≤ TA2 + wa01`). -/

structure WR (D : Dl) (M : Int) (s : Sigs) (a L t0 TA TA2 u v Hz : Int) : Prop where
  ord : a ≤ L ∧ L + M ≤ t0 ∧ t0 < TA ∧ TA < TA2 ∧ TA < Hz ∧ t0 < u ∧ 1 ≤ M
  r1 : ∀ t, L ≤ t → t < Hz → s.r1 t = (decide (t < t0) || decide (u ≤ t))
  r2 : ∀ t, L ≤ t → t < Hz → s.r2 t = decide (v ≤ t)
  sep : u + D.wr1s ≤ v + D.wr2s
  A0 : ∀ t, a ≤ t → t < Hz → s.A0 t = (decide (t < TA) || decide (TA2 ≤ t))
  A0p : s.A0 (a - 1) = false
  R0a : ∀ t, a ≤ t → t < L + M → s.R0 t = true
  q0 : ∀ t, L ≤ t → t < L + M → s.q t = true
  g10 : ∀ t, L ≤ t → t < L + M → s.g1 t = true
  g20 : ∀ t, L ≤ t → t < L + M → s.g2 t = false
  A10 : ∀ t, L ≤ t → t < L + M → s.A1 t = true
  A20 : ∀ t, L ≤ t → t < L + M → s.A2 t = false

/-- g1's fall after the release at `t0` (I0 fall arc). -/
def GF (D : Dl) (t0 : Int) : Int := t0 + D.wr1g + D.g1f1
/-- A1's fall: g1 and A0 both seen low (fall arc). -/
def TF (D : Dl) (t0 TA : Int) : Int := max (GF D t0 + D.wg1) (TA + D.wa01) + D.c1f

/-- Tick rows of WR (run form; names as in `Rows1`). -/
structure RowsR (D : Dl) (dz t0 TA TA2 u : Int) : Prop where
  g1p : u < GU D u
  a1 : GU D u ≤ RU D u + D.smin
  zf : GF D t0 < TR D t0 + dz
  zrise : GU D u < RU D u + dz
  x1 : GF D t0 < TF D t0 TA ∧ TA < TF D t0 TA
  y1 : GU D u < TU D u TA2 ∧ TA2 < TU D u TA2
  dz : 0 ≤ dz ∧ dz ≤ D.smin

section wr
variable {D : Dl} {M : Int} {s : Sigs} {a L t0 TA TA2 u v Hz : Int}

theorem wr_q (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz) :
    ∀ t, L ≤ t → t < Hz → s.q t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.q; have := S.ord; have := S.sep
  refine q1_win R hM S.q0 ?_
  intro t h1 h2 hr2 _
  rw [S.r2 _ (by omega) (by omega)] at hr2
  rw [S.r1 _ (by omega) (by omega)]; simp at hr2 ⊢; omega

theorem wr_g2 (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz) :
    ∀ t, L ≤ t → t < Hz → s.g2 t = false := g2_win0 R hM (wr_q R hM S) S.g20

theorem wr_A2 (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz) :
    ∀ t, L ≤ t → t < Hz → s.A2 t = false := A2_win0 R hM (wr_g2 R hM S) S.A20

theorem wr_g1 (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz) (t : Int)
    (h1 : L ≤ t) (h2 : t < Hz) : s.g1 t = (decide (t < GF D t0) || decide (GU D u ≤ t)) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.g1; have := S.ord
  by_cases hc : t < L + M
  · rw [S.g10 t h1 hc]; unfold GU GF; symm; simp; omega
  rw [g1_q1 R hM (wr_q R hM S) t (by omega) h2, S.r1 _ (by omega) (by omega),
    S.r1 _ (by omega) (by omega)]
  unfold GU GF; rw [Bool.eq_iff_iff]; simp; omega

theorem wr_R0 (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz) (t : Int)
    (h1 : a ≤ t) (h2 : t < Hz) : s.R0 t = (decide (t < TR D t0) || decide (RU D u ≤ t)) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0; have := S.ord
  by_cases hc : t < L + M
  · rw [S.R0a t h1 hc]; unfold RU TR; symm; simp; omega
  rw [R0_q1 R hM (wr_q R hM S) t (by omega) h2, S.r1 _ (by omega) (by omega),
    S.r1 _ (by omega) (by omega)]
  unfold RU TR; rw [Bool.eq_iff_iff]; simp; omega

theorem wr_TA (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz) :
    TR D t0 + D.smin ≤ TA := by
  have := S.ord
  refine srv_lb R (c := true) (Or.inl (by rw [S.A0p]; rfl)) (by omega) (fun t h1 h2 => ?_) ?_
    (fun t h1 h2 h3 => ?_)
  · rw [S.A0 t h1 (by omega)]; simp; omega
  · rw [S.A0 TA (by omega) (by omega)]; simp; omega
  · rw [wr_R0 R hM S t h1 (by omega)]; simp; omega

theorem wr_TA2 (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz) (hz : TA2 < Hz) :
    RU D u + D.smin ≤ TA2 := by
  have := S.ord; have hT := wr_TA R hM S; have := D.H_NONNEG
  refine srv_lb R (c := false) (a := TA) (Or.inl ?_) (by omega) (fun t h1 h2 => ?_) ?_
    (fun t h1 h2 h3 => ?_)
  · rw [S.A0 (TA - 1) (by omega) (by omega)]; simp; omega
  · rw [S.A0 t (by omega) (by omega)]; simp; omega
  · rw [S.A0 TA2 (by omega) hz]; simp
  · rw [wr_R0 R hM S t (by omega) (by omega)]; simp; omega

/-- A1 is high before `TF` (no race needed). -/
theorem wr_A1_hi (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz) :
    ∀ t, L ≤ t → t < TF D t0 TA → t < Hz → s.A1 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A1
  refine int_ind_w (fun t => t < TF D t0 TA → t < Hz → s.A1 t = true) L (L + M)
    (fun t h1 h2 _ _ => S.A10 t h1 h2) ?_
  intro t ht ih hb hz
  unfold TF at hb
  rw [R.H_A1 t, CE_eq, CE_eq,
    ih (t - D.wfa1 - D.c1f) (by omega) (by omega) (by unfold TF; omega) (by omega)]
  simp only [Bool.and_true, Bool.or_eq_true]
  right
  by_cases hg : t - D.wg1 - D.c1f < GF D t0
  · rw [wr_g1 R hM S _ (by omega) (by omega)]; simp [hg]
  · rw [S.A0 _ (by omega) (by omega)]; simp; omega

/-- **A1's exact trace on WR**, given the four-phase client (`TF < u`), RA1 and RT2a. -/
theorem wr_A1 (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz)
    (hC : TF D t0 TA < u) (H_RA1 : TF D t0 TA + D.wfa1 ≤ GU D u + D.wg1)
    (H_RT2a : TF D t0 TA + D.wfa1 ≤ TA2 + D.wa01) :
    ∀ t, L ≤ t → t < Hz → s.A1 t = (decide (t < TF D t0 TA) || decide (TU D u TA2 ≤ t)) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A1
  refine int_ind_w (fun t => t < Hz → s.A1 t = (decide (t < TF D t0 TA) || decide (TU D u TA2 ≤ t)))
    L (L + M) (fun t h1 h2 _ => by
      rw [S.A10 t h1 h2]; symm; unfold TU TF GU GF at *; simp; omega) ?_
  intro t ht ih hz
  have g := fun d (h : 0 ≤ d) (h' : d ≤ D.c1f) => wr_g1 R hM S (t - D.wg1 - d) (by omega) (by omega)
  have a0 := fun d (h : 0 ≤ d) (h' : d ≤ D.c1f) => S.A0 (t - D.wa01 - d) (by omega) (by omega)
  have f := fun d (h : D.c1r ≤ d) (h' : d ≤ D.c1f) =>
    ih (t - D.wfa1 - d) (by omega) (by omega) (by omega)
  rw [R.H_A1 t, CE_eq, CE_eq, g _ (by omega) (Int.le_refl _), g _ (by omega) (by omega),
    a0 _ (by omega) (Int.le_refl _), a0 _ (by omega) (by omega),
    f _ (Int.le_refl _) (by omega), f _ (by omega) (Int.le_refl _)]
  unfold TU TF GU GF at *
  rw [Bool.eq_iff_iff]; simp; omega

theorem wr_excl (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz) :
    ∀ t, L ≤ t → t < Hz → (s.g1 t && s.g2 t) = false := by
  intro t h1 h2; rw [wr_g2 R hM S t h1 h2]; simp

/-- **C's step fields on a release window with optional (early) re-request** (client 1,
no waiter at the release). Assumed: the gate model, H_M, `WR`, the four-phase client
(`TF < u`), RA1, RT2a, the z line, `RowsR`. Proved: H_ARB1, H_ARB2, zr, H_AMERGE_RTZ, xa, ya
at every tick of `[L + M + dz, Hz - 1)`. -/
theorem wr_fields (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz)
    (hC : TF D t0 TA < u) (H_RA1 : TF D t0 TA + D.wfa1 ≤ GU D u + D.wg1)
    (H_RT2a : TF D t0 TA + D.wfa1 ≤ TA2 + D.wa01)
    {z : Int → Bool} {dz : Int} (Z : ZLine s z dz) (K : RowsR D dz t0 TA TA2 u) :
    ∀ t, L + M + dz ≤ t → t + 1 < Hz → CF s z t := by
  have := S.ord; have := K.dz; have := K.g1p; have := K.a1; have := K.zrise; have := K.y1
  have := K.zf; have := K.x1
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  have hTA := wr_TA R hM S
  have hT' : RU D u + D.smin ≤ TA2 ∨ Hz ≤ TA2 := by
    by_cases h : TA2 < Hz
    · exact Or.inl (wr_TA2 R hM S h)
    · exact Or.inr (by omega)
  intro t h1 h2
  have g1t := wr_g1 R hM S t (by omega) (by omega)
  have g1u := wr_g1 R hM S (t + 1) (by omega) (by omega)
  have g2t := wr_g2 R hM S t (by omega) (by omega)
  have g2u := wr_g2 R hM S (t + 1) (by omega) (by omega)
  have a1t := wr_A1 R hM S hC H_RA1 H_RT2a t (by omega) (by omega)
  have a1u := wr_A1 R hM S hC H_RA1 H_RT2a (t + 1) (by omega) (by omega)
  have a2t := wr_A2 R hM S t (by omega) (by omega)
  have a2u := wr_A2 R hM S (t + 1) (by omega) (by omega)
  have zt := Z t
  have zu := Z (t + 1)
  rw [wr_R0 R hM S (t - dz) (by omega) (by omega)] at zt
  rw [wr_R0 R hM S (t + 1 - dz) (by omega) (by omega)] at zu
  have r1t := S.r1 t (by omega) (by omega)
  have a0t := S.A0 t (by omega) (by omega)
  unfold CF CArb
  rw [g1t, g1u, g2t, g2u, a1t, a1u, a2t, a2u, zt, zu, r1t, a0t]
  have e1 : TU D u TA2 ≥ TA2 + D.wa01 + D.c1r := by unfold TU; omega
  have e2 : TF D t0 TA ≥ GF D t0 + D.wg1 + D.c1f ∧ TF D t0 TA ≥ TA + D.wa01 + D.c1f := by
    unfold TF; omega
  have e3 : GU D u - u ≤ GF D t0 - t0 := by unfold GU GF; omega
  unfold TR at *; unfold RU at *
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ne_eq, ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.or_false] <;> (try simp) <;> omega

/-- **Race RA1 at slack −1 ⇒ C's `xa` fails**: the re-request's grant reaches ua1 one tick
before ua1's fall has come round its feedback pin; the C-element sees (g1 = 1, fb = 1) and
re-raises A1 while A0 is still low. Side condition: A0 has not re-risen by then
(`GU + wg1 + c1r ≤ TA2`). -/
theorem cex_RA1 (R : Run D s) (hM : MB D M) (S : WR D M s a L t0 TA TA2 u v Hz)
    (hC : TF D t0 TA < u) (hslack : TF D t0 TA + D.wfa1 = GU D u + D.wg1 + 1)
    (hA : GU D u + D.wg1 + D.c1r ≤ TA2) (hz : GU D u + D.wg1 + D.c1r < Hz) :
    ∃ t, L ≤ t ∧ t < Hz ∧ s.A1 t = false ∧ s.A1 (t + 1) = true ∧ s.A0 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A1
  have hTA := wr_TA R hM S
  have e2 : TF D t0 TA ≥ GF D t0 + D.wg1 + D.c1f ∧ TF D t0 TA ≥ TA + D.wa01 + D.c1f := by
    unfold TF; omega
  have hGU : u ≤ GU D u := by unfold GU; omega
  have hL : L + M ≤ TF D t0 TA := by unfold GF at e2; omega
  have lo : s.A1 (TF D t0 TA) = false := by
    have view : ∀ d, D.c1r ≤ d → d ≤ D.c1f →
        CE (s.g1 (TF D t0 TA - D.wg1 - d)) (s.A0 (TF D t0 TA - D.wa01 - d))
          (s.A1 (TF D t0 TA - D.wfa1 - d)) = false := by
      intro d h1 h2
      rw [wr_g1 R hM S _ (by omega) (by omega), S.A0 _ (by omega) (by omega), CE_eq]
      have : ¬ (TF D t0 TA - D.wg1 - d < GF D t0) := by omega
      have : ¬ (GU D u ≤ TF D t0 TA - D.wg1 - d) := by omega
      have : ¬ (TF D t0 TA - D.wa01 - d < TA) := by omega
      have : ¬ (TA2 ≤ TF D t0 TA - D.wa01 - d) := by omega
      simp [*]
    rw [R.H_A1, view _ (Int.le_refl _) (by omega), view _ (by omega) (Int.le_refl _)]; rfl
  have hi : s.A1 (GU D u + D.wg1 + D.c1r) = true := by
    rw [R.H_A1, show GU D u + D.wg1 + D.c1r - D.wg1 - D.c1r = GU D u by omega,
      show GU D u + D.wg1 + D.c1r - D.wfa1 - D.c1r = TF D t0 TA - 1 by omega,
      wr_g1 R hM S _ (by omega) (by omega),
      wr_A1_hi R hM S _ (by omega) (by omega) (by omega), CE_eq]
    simp
  obtain ⟨t, h1, h2, h3, h4⟩ := rise_tick s.A1 _ _ (by omega) lo hi
  refine ⟨t, by omega, by omega, h3, h4, ?_⟩
  rw [S.A0 t (by omega) (by omega)]; simp; omega

end wr

/-! ## Epoch WX: grant from idle to client 2 (q flips), client 1 may follow: the idle race

Idle settled state (q = 1) on `[L, L + M)`; client 2 requests at `v`, so q must fall
(`QX = v + wr2s + qf`); client 1 may request at `u` (`u ≥ Hz` = never). If client 1's
request reaches ustate while q's fall is still in flight round ustate's loop, the binary
model shows the runt of `ArbBinary` / `ArbInvolution` inside the held arbiter (`cex_SEP`,
`sep_cex_run`). **H_SEP** (`SepX`): client 1's request is separated from client 2's by
more than the loop, at each of the three LUTs that read both (Q: ustate's loop, R: R0,
G: g1). The ordered case (client 1 ahead at ustate) is epoch WG; `race_fields` packages
both cases. -/

structure WX (D : Dl) (M : Int) (s : Sigs) (a L v TA2 u Hz : Int) : Prop where
  ord : a ≤ L ∧ L + M ≤ v ∧ L + M ≤ u ∧ v < TA2 ∧ 1 ≤ M
  r1 : ∀ t, L ≤ t → t < Hz → s.r1 t = decide (u ≤ t)
  r2 : ∀ t, L ≤ t → t < Hz → s.r2 t = decide (v ≤ t)
  A0 : ∀ t, a ≤ t → t < Hz → s.A0 t = decide (TA2 ≤ t)
  anc : Anc s false a
  R0a : ∀ t, a ≤ t → t < L + M → s.R0 t = false
  q0 : ∀ t, L ≤ t → t < L + M → s.q t = true
  g10 : ∀ t, L ≤ t → t < L + M → s.g1 t = false
  g20 : ∀ t, L ≤ t → t < L + M → s.g2 t = false
  A10 : ∀ t, L ≤ t → t < L + M → s.A1 t = false
  A20 : ∀ t, L ≤ t → t < L + M → s.A2 t = false

/-- q's fall after client 2's request (O6 fall arc). -/
def QX (D : Dl) (v : Int) : Int := v + D.wr2s + D.qf
/-- g2's rise: r2 and q-low both seen (flat O6 rise arc). -/
def GX (D : Dl) (v : Int) : Int := max (v + D.wr2g) (QX D v + D.wq) + D.g2r
/-- R0's rise: r2 and q-low both seen through their rise arcs. -/
def RX (D : Dl) (v : Int) : Int := max (v + D.wr2s + D.Rr2) (QX D v + D.wfb + D.Rrq)
/-- A2's rise. -/
def TX (D : Dl) (v TA2 : Int) : Int := max (GX D v + D.wg2) (TA2 + D.wa02) + D.c2r

/-- **H_SEP** (idle race, client 2 first): client 1's request `u` is separated from client
2's `v` by more than the loop, at each LUT that reads both:
* `q` (ustate's loop): `QX + wfb ≤ u + wr1s`;
* `r` (R0): `RX ≤ u + wr1s + Rr1` (the fall-arc view is then implied);
* `g` (g1, per-pin arcs, one inequality per view). -/
structure SepX (D : Dl) (v u : Int) : Prop where
  q : QX D v + D.wfb ≤ u + D.wr1s
  r : RX D v ≤ u + D.wr1s + D.Rr1
  g : QX D v + D.wq + D.g1rq ≤ u + D.wr1g + D.g1r1 ∧ QX D v + D.wq + D.g1fq ≤ u + D.wr1g + D.g1f1

structure RowsX (D : Dl) (dz v TA2 : Int) : Prop where
  g2p : v < GX D v
  a1 : GX D v ≤ RX D v + D.smin
  zrise : GX D v < RX D v + dz
  y1 : GX D v < TX D v TA2 ∧ TA2 < TX D v TA2
  dz : 0 ≤ dz ∧ dz ≤ D.smin

theorem CE_g0' : ∀ a fb : Bool, CE false a fb = (a && fb) := CE_g0

section wx
variable {D : Dl} {M : Int} {s : Sigs} {a L v TA2 u Hz : Int}

theorem A1_win0 (R : Run D s) (hM : MB D M) {L Hz : Int}
    (hg : ∀ t, L ≤ t → t < Hz → s.g1 t = false)
    (ha0 : ∀ t, L ≤ t → t < L + M → s.A1 t = false) :
    ∀ t, L ≤ t → t < Hz → s.A1 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS; have := hM.A1
  refine int_ind_w (fun t => t < Hz → s.A1 t = false) L (L + M)
    (fun t h1 h2 _ => ha0 t h1 h2) ?_
  intro t ht ih hz
  rw [R.H_A1 t, hg _ (by omega) (by omega), hg (t - D.wg1 - D.c1f) (by omega) (by omega),
    CE_g0, CE_g0, ih (t - D.wfa1 - D.c1r) (by omega) (by omega) (by omega),
    ih (t - D.wfa1 - D.c1f) (by omega) (by omega) (by omega)]
  simp

/-- q is high until `QX` (no race needed: with r2 unseen, ustate keeps or sets q). -/
theorem wx_q_hi (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz) :
    ∀ t, L ≤ t → t < QX D v → t < Hz → s.q t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q
  refine int_ind_w (fun t => t < QX D v → t < Hz → s.q t = true) L (L + M)
    (fun t h1 h2 _ _ => S.q0 t h1 h2) ?_
  intro t ht ih hb hz
  unfold QX at hb
  rw [R.H_q t, S.r2 (t - D.wr2s - D.qf) (by omega) (by omega),
    ih (t - D.wfb - D.qf) (by omega) (by omega) (by unfold QX; omega) (by omega), FS_q1]
  have : ¬ (v ≤ t - D.wr2s - D.qf) := by omega
  simp [this]

theorem wx_TA2_R (R : Run D s) (S : WX D M s a L v TA2 u Hz) (hz : TA2 < Hz) (Rt : Int)
    (hR : ∀ t, a ≤ t → t < Rt → t ≤ TA2 → s.R0 t = false) : Rt + D.smin ≤ TA2 := by
  have := S.ord
  refine srv_lb R S.anc (by omega) (fun t h1 h2 => ?_) ?_ hR
  · rw [S.A0 t h1 (by omega)]; simp; omega
  · rw [S.A0 TA2 (by omega) hz]; simp

theorem wx_q (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz) (H : SepX D v u)
    (hHQ : TA2 < Hz → QX D v + D.wfb ≤ TA2 + D.wa0s) :
    ∀ t, L ≤ t → t < Hz → s.q t = decide (t < QX D v) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q; have := H.q
  have hH : QX D v + D.wfb ≤ TA2 + D.wa0s ∨ Hz ≤ TA2 := by
    by_cases h : TA2 < Hz
    · exact Or.inl (hHQ h)
    · exact Or.inr (by omega)
  refine int_ind_w (fun t => t < Hz → s.q t = decide (t < QX D v)) L (L + M)
    (fun t h1 h2 _ => by rw [S.q0 t h1 h2]; unfold QX; symm; simp; omega) ?_
  intro t ht ih hz
  by_cases hb : t < QX D v
  · rw [wx_q_hi R hM S t (by omega) hb hz]; simp [hb]
  · have view : ∀ d, D.qr ≤ d → d ≤ D.qf →
        FS (s.r1 (t - D.wr1s - d)) (s.r2 (t - D.wr2s - d)) (s.q (t - D.wfb - d))
          (s.A0 (t - D.wa0s - d)) = false := by
      intro d hd1 hd2
      unfold QX at hb
      rw [S.r2 _ (by omega) (by omega), S.r1 _ (by omega) (by omega),
        S.A0 _ (by omega) (by omega), ih _ (by omega) (by omega) (by omega), FS_bool]
      unfold QX at *
      have : v ≤ t - D.wr2s - d := by omega
      simp only [this, decide_true]
      by_cases h1 : TA2 ≤ t - D.wa0s - d
      · have : ¬ (t - D.wfb - d < v + D.wr2s + D.qf) := by omega
        simp [h1, this]
      · by_cases h2 : u ≤ t - D.wr1s - d
        · have : ¬ (t - D.wfb - d < v + D.wr2s + D.qf) := by omega
          simp [h1, h2, this]
        · simp [h1, h2]
    rw [R.H_q t, view _ (Int.le_refl _) (by omega), view _ (by omega) (Int.le_refl _)]
    simp [hb]

theorem wx_g1 (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz) (H : SepX D v u)
    (hq : ∀ t, L ≤ t → t < Hz → s.q t = decide (t < QX D v)) :
    ∀ t, L ≤ t → t < Hz → s.g1 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.g1; have := S.ord; have := H.g
  intro t h1 h2
  by_cases hc : t < L + M
  · exact S.g10 t h1 hc
  rw [R.H_g1 t, FG1_eq, FG1_eq, S.r1 _ (by omega) (by omega), S.r1 (t - D.wr1g - D.g1f1)
    (by omega) (by omega), hq _ (by omega) (by omega), hq (t - D.wq - D.g1fq) (by omega) (by omega)]
  rw [Bool.eq_iff_iff]; simp; omega

theorem wx_g2 (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz)
    (hq : ∀ t, L ≤ t → t < Hz → s.q t = decide (t < QX D v)) :
    ∀ t, L ≤ t → t < Hz → s.g2 t = decide (GX D v ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.g2; have := S.ord
  intro t h1 h2
  by_cases hc : t < L + M
  · rw [S.g20 t h1 hc]; unfold GX QX; symm; simp; omega
  rw [R.H_g2 t, FG2_eq, FG2_eq, S.r2 _ (by omega) (by omega), S.r2 (t - D.wr2g - D.g2f)
    (by omega) (by omega), hq _ (by omega) (by omega), hq (t - D.wq - D.g2f) (by omega) (by omega)]
  unfold GX; rw [Bool.eq_iff_iff]; simp; omega

theorem wx_R0 (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz) (H : SepX D v u)
    (hq : ∀ t, L ≤ t → t < Hz → s.q t = decide (t < QX D v)) :
    ∀ t, a ≤ t → t < Hz → s.R0 t = decide (RX D v ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0; have := S.ord; have := H.r
  intro t h1 h2
  by_cases hc : t < L + M
  · rw [S.R0a t h1 hc]; unfold RX QX; symm; simp; omega
  rw [R.H_R0 t, FR_eq, FR_eq, S.r1 _ (by omega) (by omega), S.r1 (t - D.wr1s - D.Rf1)
    (by omega) (by omega), S.r2 _ (by omega) (by omega), S.r2 (t - D.wr2s - D.Rf2)
    (by omega) (by omega), hq _ (by omega) (by omega), hq (t - D.wfb - D.Rfq) (by omega) (by omega)]
  unfold RX at *; rw [Bool.eq_iff_iff]; simp; omega

theorem wx_A2 (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz)
    (hg : ∀ t, L ≤ t → t < Hz → s.g2 t = decide (GX D v ≤ t)) :
    ∀ t, L ≤ t → t < Hz → s.A2 t = decide (TX D v TA2 ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A2
  refine int_ind_w (fun t => t < Hz → s.A2 t = decide (TX D v TA2 ≤ t)) L (L + M)
    (fun t h1 h2 _ => by
      rw [S.A20 t h1 h2]; symm; unfold TX GX; simp; omega) ?_
  intro t ht ih hz
  have g := fun d (h : 0 ≤ d) (h' : d ≤ D.c2f) => hg (t - D.wg2 - d) (by omega) (by omega)
  have a0 := fun d (h : 0 ≤ d) (h' : d ≤ D.c2f) => S.A0 (t - D.wa02 - d) (by omega) (by omega)
  have f := fun d (h : D.c2r ≤ d) (h' : d ≤ D.c2f) =>
    ih (t - D.wfa2 - d) (by omega) (by omega) (by omega)
  rw [R.H_A2 t, CE_eq, CE_eq, g _ (by omega) (Int.le_refl _), g _ (by omega) (by omega),
    a0 _ (by omega) (Int.le_refl _), a0 _ (by omega) (by omega),
    f _ (Int.le_refl _) (by omega), f _ (by omega) (Int.le_refl _)]
  unfold TX at *
  rw [Bool.eq_iff_iff]; simp; omega

/-- R0 is low before `RX` (only q's high phase and race R are used). -/
theorem wx_R0_lo (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz) (H : SepX D v u) :
    ∀ t, a ≤ t → t < RX D v → t < Hz → s.R0 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0; have := S.ord; have := H.r
  intro t h1 h2 h3
  by_cases hc : t < L + M
  · exact S.R0a t h1 hc
  have hr : t - D.wfb - D.Rrq < QX D v ∨ t - D.wr2s - D.Rr2 < v := by unfold RX at h2; omega
  rw [R.H_R0 t, FR_eq, FR_eq, S.r1 _ (by omega) (by omega), S.r1 (t - D.wr1s - D.Rf1)
    (by omega) (by omega), S.r2 _ (by omega) (by omega), S.r2 (t - D.wr2s - D.Rf2)
    (by omega) (by omega)]
  have e1 : ¬ (u ≤ t - D.wr1s - D.Rr1) := by omega
  have e2 : ¬ (u ≤ t - D.wr1s - D.Rf1) := by omega
  simp only [e1, e2, decide_false, Bool.false_and, Bool.false_or]
  rcases hr with hr | hr
  · rw [wx_q_hi R hM S _ (by omega) hr (by omega),
      wx_q_hi R hM S (t - D.wfb - D.Rfq) (by omega) (by omega) (by omega)]; simp
  · have : ¬ (v ≤ t - D.wr2s - D.Rr2) := by omega
    have : ¬ (v ≤ t - D.wr2s - D.Rf2) := by omega
    simp [*]

/-- Everything WX derives, in one bundle (q, g1, g2, R0, A1, A2 exact; the server bound). -/
theorem wx_all (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz) (H : SepX D v u) :
    (∀ t, L ≤ t → t < Hz → s.q t = decide (t < QX D v)) ∧
    (∀ t, L ≤ t → t < Hz → s.g1 t = false) ∧
    (∀ t, L ≤ t → t < Hz → s.g2 t = decide (GX D v ≤ t)) ∧
    (∀ t, a ≤ t → t < Hz → s.R0 t = decide (RX D v ≤ t)) ∧
    (∀ t, L ≤ t → t < Hz → s.A1 t = false) ∧
    (∀ t, L ≤ t → t < Hz → s.A2 t = decide (TX D v TA2 ≤ t)) ∧
    (TA2 < Hz → RX D v + D.smin ≤ TA2) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.ord
  have hsrv : TA2 < Hz → RX D v + D.smin ≤ TA2 := fun hz =>
    wx_TA2_R R S hz _ (fun t h1 h2 h3 => wx_R0_lo R hM S H t h1 h2 (by omega))
  have hq := wx_q R hM S H (fun h => by
    have := D.H_NONNEG; have h9 := hsrv h; unfold RX at h9; omega)
  have hg1 := wx_g1 R hM S H hq
  have hg2 := wx_g2 R hM S hq
  exact ⟨hq, hg1, hg2, wx_R0 R hM S H hq, A1_win0 R hM hg1 S.A10, wx_A2 R hM S hg2, hsrv⟩

theorem wx_excl (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz) (H : SepX D v u) :
    ∀ t, L ≤ t → t < Hz → (s.g1 t && s.g2 t) = false := by
  intro t h1 h2; rw [(wx_all R hM S H).2.1 t h1 h2]; simp

/-- **C's step fields on the idle-race window, client 2 first, under H_SEP.** -/
theorem wx_fields (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz) (H : SepX D v u)
    {z : Int → Bool} {dz : Int} (Z : ZLine s z dz) (K : RowsX D dz v TA2) :
    ∀ t, L + M + dz ≤ t → t + 1 < Hz → CF s z t := by
  obtain ⟨hq, hg1, hg2, hR0, hA1, hA2, hsrv⟩ := wx_all R hM S H
  have := S.ord; have := K.dz; have := K.g2p; have := K.a1; have := K.zrise; have := K.y1
  have := D.H_NONNEG
  have hT' : RX D v + D.smin ≤ TA2 ∨ Hz ≤ TA2 := by
    by_cases h : TA2 < Hz
    · exact Or.inl (hsrv h)
    · exact Or.inr (by omega)
  intro t h1 h2
  have g1t := hg1 t (by omega) (by omega)
  have g1u := hg1 (t + 1) (by omega) (by omega)
  have g2t := hg2 t (by omega) (by omega)
  have g2u := hg2 (t + 1) (by omega) (by omega)
  have a1t := hA1 t (by omega) (by omega)
  have a1u := hA1 (t + 1) (by omega) (by omega)
  have a2t := hA2 t (by omega) (by omega)
  have a2u := hA2 (t + 1) (by omega) (by omega)
  have zt := Z t
  have zu := Z (t + 1)
  rw [hR0 (t - dz) (by omega) (by omega)] at zt
  rw [hR0 (t + 1 - dz) (by omega) (by omega)] at zu
  have r2t := S.r2 t (by omega) (by omega)
  have a0t := S.A0 t (by omega) (by omega)
  unfold CF CArb
  rw [g1t, g1u, g2t, g2u, a1t, a1u, a2t, a2u, zt, zu, r2t, a0t]
  have e1 : TX D v TA2 ≥ TA2 + D.wa02 + D.c2r := by unfold TX; omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ne_eq, ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.or_false, Bool.false_or] <;> (try simp) <;> omega

/-- **H_SEP at slack −1 (ustate loop) ⇒ C's H_ARB2 fails.** Client 1's request overtakes
client 2's at ustate (`v + wr2s ≤ u + wr1s`) but arrives one tick before q's fall has come
round q's feedback pin: q makes a low runt, g2 rises and falls again while r2 stays high
(the `ArbBinary` runt, here in the held arbiter's gates). Side conditions as in `cex_Q`:
`qr + wfb ≥ 2`, `g2r = g2f` (one corner), and A0 still low at `QX` (`QX < TA2`). -/
theorem cex_SEP (R : Run D s) (hM : MB D M) (S : WX D M s a L v TA2 u Hz)
    (hov : v + D.wr2s ≤ u + D.wr1s) (hslack : u + D.wr1s + 1 = QX D v + D.wfb)
    (h2 : 2 ≤ D.qr + D.wfb) (hg : D.g2r = D.g2f) (hA : QX D v < TA2)
    (hvg : v + D.wr2g ≤ QX D v + D.wq) (hz : u + D.wr1s + D.qr + D.wq + D.g2r < Hz) :
    ∃ t, L ≤ t ∧ t < Hz ∧ s.g2 t = true ∧ s.g2 (t + 1) = false ∧ s.r2 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q; have := hM.g2
  unfold QX at hslack hA hvg
  have qQ : s.q (QX D v) = false := by
    unfold QX
    have view : ∀ d, D.qr ≤ d → d ≤ D.qf →
        FS (s.r1 (v + D.wr2s + D.qf - D.wr1s - d)) (s.r2 (v + D.wr2s + D.qf - D.wr2s - d))
          (s.q (v + D.wr2s + D.qf - D.wfb - d)) (s.A0 (v + D.wr2s + D.qf - D.wa0s - d)) = false := by
      intro d h1 h2
      rw [S.r1 _ (by omega) (by omega), S.r2 _ (by omega) (by omega),
        S.A0 _ (by omega) (by omega)]
      have e1 : ¬ (u ≤ v + D.wr2s + D.qf - D.wr1s - d) := by omega
      have e2 : v ≤ v + D.wr2s + D.qf - D.wr2s - d := by omega
      have e3 : ¬ (TA2 ≤ v + D.wr2s + D.qf - D.wa0s - d) := by omega
      simp only [e1, e2, e3, decide_false, decide_true]
      exact FS_rel _
    rw [R.H_q, view _ (Int.le_refl _) (by omega), view _ (by omega) (Int.le_refl _)]; rfl
  have qt1 : s.q (u + D.wr1s + D.qr) = true := by
    rw [R.H_q, S.r1 (u + D.wr1s + D.qr - D.wr1s - D.qr) (by omega) (by omega),
      S.r2 _ (by omega) (by omega),
      wx_q_hi R hM S (u + D.wr1s + D.qr - D.wfb - D.qr) (by omega) (by unfold QX; omega) (by omega),
      FS_q1]
    have e : u ≤ u + D.wr1s + D.qr - D.wr1s - D.qr := by omega
    simp [e]
  have ga : s.g2 (QX D v + D.wq + D.g2r) = true := by
    rw [R.H_g2, FG2_eq, S.r2 _ (by unfold QX; omega) (by unfold QX; omega),
      show QX D v + D.wq + D.g2r - D.wq - D.g2r = QX D v by omega, qQ]
    unfold QX; simp; omega
  have gb : s.g2 (u + D.wr1s + D.qr + D.wq + D.g2r) = false := by
    rw [R.H_g2, FG2_eq, FG2_eq,
      show u + D.wr1s + D.qr + D.wq + D.g2r - D.wq - D.g2r = u + D.wr1s + D.qr by omega,
      show u + D.wr1s + D.qr + D.wq + D.g2r - D.wq - D.g2f = u + D.wr1s + D.qr by omega, qt1]
    simp
  obtain ⟨t, h1, h3, h4, h5⟩ := fall_tick s.g2 _ _ (by unfold QX; omega) ga gb
  refine ⟨t, by unfold QX at h1; omega, by omega, h4, h5, ?_⟩
  rw [S.r2 t (by unfold QX at h1; omega) (by omega)]; unfold QX at h1; simp; omega

end wx

/-! ## The idle race as one epoch (H_SEP)

From the idle state both clients may request (`u`, `v`); H_SEP says the two requests are
either ordered with client 1 ahead at ustate (epoch WG: no q move, no race) or separated
by more than the loop with client 2 first (epoch WX with `SepX`). The excluded middle is the
metastable window; `cex_SEP` / `sep_cex_run` show it really breaks C's fields. -/

/-- **H_SEP**: the requests reaching an idle arbiter are separated. -/
def HSep (D : Dl) (u v : Int) : Prop := u + D.wr1s ≤ v + D.wr2s ∨ SepX D v u

/-- **The idle-race epoch under H_SEP**: C's step fields and grant exclusion on the window. -/
theorem race_fields {D : Dl} {M : Int} {s : Sigs} {a L u v TA2 Hz : Int}
    (R : Run D s) (hM : MB D M)
    (ord : a ≤ L ∧ L + M ≤ u ∧ L + M ≤ v ∧ u < TA2 ∧ v < TA2 ∧ 1 ≤ M)
    (hr1 : ∀ t, L ≤ t → t < Hz → s.r1 t = decide (u ≤ t))
    (hr2 : ∀ t, L ≤ t → t < Hz → s.r2 t = decide (v ≤ t))
    (hA0 : ∀ t, a ≤ t → t < Hz → s.A0 t = decide (TA2 ≤ t)) (hanc : Anc s false a)
    (hR0 : ∀ t, a ≤ t → t < L + M → s.R0 t = false)
    (hst : ∀ t, L ≤ t → t < L + M → s.q t = true ∧ s.g1 t = false ∧ s.g2 t = false ∧
      s.A1 t = false ∧ s.A2 t = false)
    (H_SEP : HSep D u v) {z : Int → Bool} {dz : Int} (Z : ZLine s z dz)
    (KG : u + D.wr1s ≤ v + D.wr2s → RowsG D dz u TA2) (KX : SepX D v u → RowsX D dz v TA2) :
    ∀ t, L + M + dz ≤ t → t + 1 < Hz → CF s z t ∧ (s.g1 t && s.g2 t) = false := by
  rcases H_SEP with h | h
  · have S : WG D M s a L u TA2 v Hz :=
      ⟨⟨ord.1, ord.2.1, ord.2.2.2.1, ord.2.2.2.2.2⟩, hr1, hr2, h, hA0, hanc, hR0,
        fun t h1 h2 => (hst t h1 h2).1, fun t h1 h2 => (hst t h1 h2).2.1,
        fun t h1 h2 => (hst t h1 h2).2.2.1, fun t h1 h2 => (hst t h1 h2).2.2.2.1,
        fun t h1 h2 => (hst t h1 h2).2.2.2.2⟩
    intro t h1 h2
    have := (KG h).dz
    exact ⟨wg_fields R hM S Z (KG h) t h1 h2, wg_excl R hM S t (by omega) (by omega)⟩
  · have S : WX D M s a L v TA2 u Hz :=
      ⟨⟨ord.1, ord.2.2.1, ord.2.1, ord.2.2.2.2.1, ord.2.2.2.2.2⟩, hr1, hr2, hA0, hanc, hR0,
        fun t h1 h2 => (hst t h1 h2).1, fun t h1 h2 => (hst t h1 h2).2.1,
        fun t h1 h2 => (hst t h1 h2).2.2.1, fun t h1 h2 => (hst t h1 h2).2.2.2.1,
        fun t h1 h2 => (hst t h1 h2).2.2.2.2⟩
    intro t h1 h2
    have := (KX h).dz
    exact ⟨wx_fields R hM S h Z (KX h) t h1 h2, wx_excl R hM S h t (by omega) (by omega)⟩

/-! ## Hold epochs: a settled mode persists while the inputs are constant -/

/-- The three settled modes reachable in the schedule class: idle (q = 1), client 1 holds,
client 2 holds. Values of the internal signals q, g1, g2, A1, A2, R0 and of A0. -/
inductive Md | I | H1 | H2
  deriving DecidableEq

def Md.q : Md → Bool | .I => true | .H1 => true | .H2 => false
def Md.g1 : Md → Bool | .I => false | .H1 => true | .H2 => false
def Md.g2 : Md → Bool | .I => false | .H1 => false | .H2 => true
def Md.A1 : Md → Bool | .I => false | .H1 => true | .H2 => false
def Md.A2 : Md → Bool | .I => false | .H1 => false | .H2 => true
def Md.R0 : Md → Bool | .I => false | .H1 => true | .H2 => true
def Md.A0 : Md → Bool | .I => false | .H1 => true | .H2 => true

/-- The internal signals equal the mode's values at `t`. -/
def InSt (s : Sigs) (m : Md) (t : Int) : Prop :=
  s.q t = m.q ∧ s.g1 t = m.g1 ∧ s.g2 t = m.g2 ∧ s.A1 t = m.A1 ∧ s.A2 t = m.A2 ∧ s.R0 t = m.R0

/-- The mode is a fixed point of every gate for the constant requests `c1`, `c2`. -/
def Fix (m : Md) (c1 c2 : Bool) : Prop :=
  FS c1 c2 m.q m.A0 = m.q ∧ FR c1 c2 m.q = m.R0 ∧ FG1 c1 c2 m.q = m.g1 ∧
  FG2 c1 c2 m.q = m.g2 ∧ CE m.g1 m.A0 m.A1 = m.A1 ∧ CE m.g2 m.A0 m.A2 = m.A2

instance (m : Md) (c1 c2 : Bool) : Decidable (Fix m c1 c2) := by unfold Fix; exact inferInstance

theorem fix_I : Fix .I false false := by decide
theorem fix_H1 (c2 : Bool) : Fix .H1 true c2 := by cases c2 <;> decide
theorem fix_H2 (c1 : Bool) : Fix .H2 c1 true := by cases c1 <;> decide
theorem md_excl : ∀ m : Md, (m.g1 && m.g2) = false := by intro m; cases m <;> rfl

section hold
variable {D : Dl} {M : Int} {s : Sigs}

theorem hold_st (R : Run D s) (hM : MB D M) {m : Md} {c1 c2 : Bool} (hF : Fix m c1 c2)
    {L Hz : Int} (h0 : ∀ t, L ≤ t → t < L + M → InSt s m t)
    (hin : ∀ t, L ≤ t → t < Hz → s.r1 t = c1 ∧ s.r2 t = c2 ∧ s.A0 t = m.A0) :
    ∀ t, L ≤ t → t < Hz → InSt s m t := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS; have := hM.pos
  have := hM.q; have := hM.R0; have := hM.g1; have := hM.g2; have := hM.A1; have := hM.A2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hF
  refine int_ind_w (fun t => t < Hz → InSt s m t) L (L + M) (fun t h1 h2 _ => h0 t h1 h2) ?_
  intro t ht ih hz
  have r1 := fun e (h1 : L ≤ e) (h2 : e < Hz) => (hin e h1 h2).1
  have r2 := fun e (h1 : L ≤ e) (h2 : e < Hz) => (hin e h1 h2).2.1
  have a0 := fun e (h1 : L ≤ e) (h2 : e < Hz) => (hin e h1 h2).2.2
  have I := fun e (h1 : L ≤ e) (h2 : e < t) => ih e h1 h2 (by omega)
  have hq : s.q t = m.q := by
    rw [R.H_q, r1 (t - D.wr1s - D.qr) (by omega) (by omega), r1 (t - D.wr1s - D.qf) (by omega) (by omega),
      r2 (t - D.wr2s - D.qr) (by omega) (by omega), r2 (t - D.wr2s - D.qf) (by omega) (by omega),
      a0 (t - D.wa0s - D.qr) (by omega) (by omega), a0 (t - D.wa0s - D.qf) (by omega) (by omega),
      (I (t - D.wfb - D.qr) (by omega) (by omega)).1, (I (t - D.wfb - D.qf) (by omega) (by omega)).1, f1]
    simp
  have Iq : ∀ e, L ≤ e → e ≤ t → s.q e = m.q := fun e h1 h2 => by
    by_cases h : e < t
    · exact (I e h1 h).1
    · rw [show e = t by omega]; exact hq
  have hg1 : s.g1 t = m.g1 := by
    rw [R.H_g1, r1 (t - D.wr1g - D.g1r1) (by omega) (by omega), r1 (t - D.wr1g - D.g1f1) (by omega) (by omega),
      r2 (t - D.wr2g - D.g1r2) (by omega) (by omega), r2 (t - D.wr2g - D.g1f2) (by omega) (by omega),
      Iq (t - D.wq - D.g1rq) (by omega) (by omega), Iq (t - D.wq - D.g1fq) (by omega) (by omega), f3]
    simp
  have hg2 : s.g2 t = m.g2 := by
    rw [R.H_g2, r1 (t - D.wr1g - D.g2r) (by omega) (by omega), r1 (t - D.wr1g - D.g2f) (by omega) (by omega),
      r2 (t - D.wr2g - D.g2r) (by omega) (by omega), r2 (t - D.wr2g - D.g2f) (by omega) (by omega),
      Iq (t - D.wq - D.g2r) (by omega) (by omega), Iq (t - D.wq - D.g2f) (by omega) (by omega), f4]
    simp
  have Ig1 : ∀ e, L ≤ e → e ≤ t → s.g1 e = m.g1 := fun e h1 h2 => by
    by_cases h : e < t
    · exact (I e h1 h).2.1
    · rw [show e = t by omega]; exact hg1
  have Ig2 : ∀ e, L ≤ e → e ≤ t → s.g2 e = m.g2 := fun e h1 h2 => by
    by_cases h : e < t
    · exact (I e h1 h).2.2.1
    · rw [show e = t by omega]; exact hg2
  refine ⟨hq, hg1, hg2, ?_, ?_, ?_⟩
  · rw [R.H_A1, a0 (t - D.wa01 - D.c1r) (by omega) (by omega), a0 (t - D.wa01 - D.c1f) (by omega) (by omega),
      Ig1 (t - D.wg1 - D.c1r) (by omega) (by omega), Ig1 (t - D.wg1 - D.c1f) (by omega) (by omega),
      (I (t - D.wfa1 - D.c1r) (by omega) (by omega)).2.2.2.1,
      (I (t - D.wfa1 - D.c1f) (by omega) (by omega)).2.2.2.1, f5]
    simp
  · rw [R.H_A2, a0 (t - D.wa02 - D.c2r) (by omega) (by omega), a0 (t - D.wa02 - D.c2f) (by omega) (by omega),
      Ig2 (t - D.wg2 - D.c2r) (by omega) (by omega), Ig2 (t - D.wg2 - D.c2f) (by omega) (by omega),
      (I (t - D.wfa2 - D.c2r) (by omega) (by omega)).2.2.2.2.1,
      (I (t - D.wfa2 - D.c2f) (by omega) (by omega)).2.2.2.2.1, f6]
    simp
  · rw [R.H_R0, r1 (t - D.wr1s - D.Rr1) (by omega) (by omega), r1 (t - D.wr1s - D.Rf1) (by omega) (by omega),
      r2 (t - D.wr2s - D.Rr2) (by omega) (by omega), r2 (t - D.wr2s - D.Rf2) (by omega) (by omega),
      Iq (t - D.wfb - D.Rrq) (by omega) (by omega), Iq (t - D.wfb - D.Rfq) (by omega) (by omega), f2]
    simp

/-- **C's step fields on a hold window** (nothing moves): every field holds vacuously, and
grant exclusion holds by the mode. -/
theorem hold_fields (R : Run D s) (hM : MB D M) {m : Md} {c1 c2 : Bool} (hF : Fix m c1 c2)
    {L Hz : Int} (h0 : ∀ t, L ≤ t → t < L + M → InSt s m t)
    (hin : ∀ t, L ≤ t → t < Hz → s.r1 t = c1 ∧ s.r2 t = c2 ∧ s.A0 t = m.A0)
    {z : Int → Bool} {dz : Int} (Z : ZLine s z dz) (hdz : 0 ≤ dz) :
    ∀ t, L + M + dz ≤ t → t + 1 < Hz → CF s z t ∧ (s.g1 t && s.g2 t) = false := by
  have := hM.pos
  have H := hold_st R hM hF h0 hin
  intro t h1 h2
  obtain ⟨_, g1t, g2t, a1t, a2t, _⟩ := H t (by omega) (by omega)
  obtain ⟨_, g1u, g2u, a1u, a2u, _⟩ := H (t + 1) (by omega) (by omega)
  have zt : z t = m.R0 := by rw [Z]; exact (H (t - dz) (by omega) (by omega)).2.2.2.2.2
  have zu : z (t + 1) = m.R0 := by rw [Z]; exact (H (t + 1 - dz) (by omega) (by omega)).2.2.2.2.2
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩, by rw [g1t, g2t]; exact md_excl m⟩
  · intro h; rw [g1t, g1u] at h; exact absurd rfl h
  · intro h; rw [g2t, g2u] at h; exact absurd rfl h
  · intro h; rw [zt, zu] at h; exact absurd rfl h
  · intro h h'; rw [zt] at h; rw [zu, h] at h'; exact absurd h' (by simp)
  · intro h; rw [a1t, a1u] at h; exact absurd rfl h
  · intro h; rw [a2t, a2u] at h; exact absurd rfl h

end hold

end Formal.Cells.ArbAMergeRun
