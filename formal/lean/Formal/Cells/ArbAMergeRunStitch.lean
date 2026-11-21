import Formal.Cells.ArbAMergeRun
import Formal.Net.OpsCM

/-!
# Probe Barb4 (part 2): stitching epochs into a run, and C's `OpsCM.AMerge` instantiated

Stitching (2) and the instantiation of C's `OpsCM.AMerge` (3). Core Lean; imports
`ArbAMergeRun` and C's `Formal.Net.OpsCM`.

* **`stitch_run`** (abstract): if window 0's start condition holds, every window with its
  start condition gives `F` on its range and the next window's start condition, consecutive
  ranges overlap and the windows reach every time, then `F` holds at every tick.
* The schedule class: `Kind` (hold, `wg`, `wrr`, `wri`, `wx`, `e1`, `e2`), `Ep`, start/end
  modes, `StartC` (start mode settled, R0 since the anchor, the anchor), `EndC`, `EpOK` (the
  epoch hypotheses: input pattern, edge order, races, rows, all named in `ArbAMerge` /
  `ArbAMergeRun`), `Link` (boundary match), `Plan` (a run from reset: epoch 0 the reset
  epoch, every epoch OK, consecutive epochs linked, the windows reaching every time).
* **`win_step`**: every kind's window theorem in the uniform form (start ⇒ fields ∧ end).
* **`run_fields`**: C's six step fields and grant exclusion at every tick `t ≥ 0` of any run
  whose schedule is a `Plan`.
* **`amerge_of_plan`**: C's `AMerge` (all 13 fields, including the init fields `i1 i2 iz ix
  iy`, read off the reset epoch) at C's tick = 1 ps, for any `Plan`, with `dat` as the one
  remaining hypothesis H_DAT (B has no timing model of the data mux).
* `epok_*`: constructors of `EpOK`, one per kind.

**Assumed:** `Run`, H_M, `ZLine`, a `Plan`, H_DAT. **Proved:** `AMerge`. **NOT covered:**
schedules outside the class (see `ArbAMergeRun`: client 2 alone, idle with q = 0, a waiter
arriving mid-release, two requests inside the metastable window, which H_SEP excludes);
`dat` is assumed, not derived. Non-vacuity: `ArbAMergeRunWit.amerge_witness`.
-/

namespace Formal.Cells.ArbAMergeRun
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2
open Formal.Cells.ArbMultiToken (MB Dw Dw_MB Dw_rt CArb)
open Formal.Cells.ArbAMerge

/-! ## The stitching lemma (abstract) -/

/-- **Stitching.** A run cut into windows `k = 0, 1, ...`: if the start condition of window 0
holds, if every window whose start condition holds gives the property `F` on `[lo k, hi k)`
AND the start condition of the next window (the boundary states match), if consecutive
windows overlap (`lo (k+1) ≤ hi k`) and the windows reach every time, then `F` holds at
every `t ≥ lo 0`. -/
theorem stitch_run {Start : Nat → Prop} {F : Int → Prop} (lo hi : Nat → Int) (h0 : Start 0)
    (hwin : ∀ k, Start k → (∀ t, lo k ≤ t → t < hi k → F t) ∧ Start (k + 1))
    (hov : ∀ k, lo (k + 1) ≤ hi k) (hunb : ∀ t, ∃ k, t < hi k) :
    ∀ t, lo 0 ≤ t → F t := by
  have hS : ∀ k, Start k := by
    intro k; induction k with
    | zero => exact h0
    | succ k ih => exact (hwin k ih).2
  have key : ∀ n : Nat, ∀ t, lo 0 ≤ t → t < hi n → F t := by
    intro n; induction n with
    | zero => exact (hwin 0 (hS 0)).1
    | succ n ih =>
      intro t h1 h2
      by_cases h : t < hi n
      · exact ih t h1 h
      · exact (hwin (n + 1) (hS (n + 1))).1 t (by have := hov n; omega) h2
  intro t ht
  obtain ⟨k, hk⟩ := hunb t
  exact key k t ht hk

/-! ## Epochs of the schedule class -/

/-- Epoch kinds: hold (a mode with constant inputs), grant from idle to client 1 (`wg`),
client 1 releases with no waiter and re-requests (`wrr`: solo client / same client winning
twice) or not (`wri`: release to idle), grant from idle to client 2 with q flipping (`wx`, the
idle race under H_SEP), and the two handovers of `ArbAMerge` (`e1`: 1 → 2, `e2`: 2 → 1). -/
inductive Kind
  | hold (m : Md) (c1 c2 : Bool)
  | wg | wrr | wri | wx | e1 | e2

/-- One epoch: its kind and its edge times (unused ones are ignored). `a` is A0's last edge
before the window, `[L, Hz)` the window. -/
structure Ep where
  k : Kind
  a : Int
  L : Int
  t0 : Int
  TA : Int
  TA2 : Int
  u : Int
  v : Int
  Hz : Int

def startMode : Kind → Md
  | .hold m _ _ => m | .wg => .I | .wrr => .H1 | .wri => .H1 | .wx => .I | .e1 => .H1 | .e2 => .H2
def endMode : Kind → Md
  | .hold m _ _ => m | .wg => .H1 | .wrr => .H1 | .wri => .I | .wx => .H2 | .e1 => .H2 | .e2 => .H1

/-- The end of the settled part a window needs at its start. -/
def first (M : Int) (e : Ep) : Int :=
  match e.k with
  | .e1 => e.t0 | .e2 => e.t0 | _ => e.L + M
/-- The time from which the window's end mode is settled. -/
def Lend (D : Dl) (e : Ep) : Int :=
  match e.k with
  | .hold _ _ _ => e.L
  | .wg => TU D e.u e.TA2
  | .wrr => TU D e.u e.TA2
  | .wri => TF D e.t0 e.TA
  | .wx => TX D e.v e.TA2
  | .e1 => max (T1 D e.t0 e.TA) (T2r D e.TA e.TA2)
  | .e2 => max (T1b D e.t0 e.TA) (T2rb D e.TA e.TA2)
/-- A0's last edge in the window (the next window's anchor). -/
def aEnd (e : Ep) : Int :=
  match e.k with
  | .hold _ _ _ => e.a | .wri => e.TA | _ => e.TA2

/-- The start condition of a window: the start mode is settled on `[L, first)`, R0 has its
mode value since the anchor `a`, and the anchor is a real A0 edge (or the reset past). -/
def StartC (M : Int) (s : Sigs) (e : Ep) : Prop :=
  (∀ t, e.L ≤ t → t < first M e → InSt s (startMode e.k) t) ∧
  (∀ t, e.a ≤ t → t < e.L + M → s.R0 t = (startMode e.k).R0) ∧
  Anc s (startMode e.k).A0 e.a ∧ e.a ≤ e.L

/-- What a window leaves for the next one. -/
def EndC (D : Dl) (s : Sigs) (e : Ep) : Prop :=
  (∀ t, Lend D e ≤ t → t < e.Hz → InSt s (endMode e.k) t) ∧
  (∀ t, aEnd e ≤ t → t < e.Hz → s.R0 t = (endMode e.k).R0) ∧
  Anc s (endMode e.k).A0 (aEnd e) ∧ aEnd e ≤ Lend D e

/-- The epoch hypotheses: the inputs' pattern on the window (requests, the server's A0
edges), the order of the edges, and the kind's races and tick rows, all named in
`ArbAMerge` / `ArbAMergeRun`. -/
def EpOK (D : Dl) (M : Int) (s : Sigs) (dz : Int) (e : Ep) : Prop :=
  match e.k with
  | .hold m c1 c2 => Fix m c1 c2 ∧
      ∀ t, e.L ≤ t → t < e.Hz → s.r1 t = c1 ∧ s.r2 t = c2 ∧ s.A0 t = m.A0
  | .wg => (e.L + M ≤ e.u ∧ e.u < e.TA2 ∧ e.TA2 < e.Hz) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r1 t = decide (e.u ≤ t)) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r2 t = decide (e.v ≤ t)) ∧
      e.u + D.wr1s ≤ e.v + D.wr2s ∧
      (∀ t, e.a ≤ t → t < e.Hz → s.A0 t = decide (e.TA2 ≤ t)) ∧ RowsG D dz e.u e.TA2
  | .wrr => (e.L + M ≤ e.t0 ∧ e.t0 < e.TA ∧ e.TA < e.TA2 ∧ e.t0 < e.u ∧ e.u < e.Hz ∧ e.TA2 < e.Hz) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r1 t = (decide (t < e.t0) || decide (e.u ≤ t))) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r2 t = decide (e.v ≤ t)) ∧
      e.u + D.wr1s ≤ e.v + D.wr2s ∧
      (∀ t, e.a ≤ t → t < e.Hz → s.A0 t = (decide (t < e.TA) || decide (e.TA2 ≤ t))) ∧
      TF D e.t0 e.TA < e.u ∧ TF D e.t0 e.TA + D.wfa1 ≤ GU D e.u + D.wg1 ∧
      TF D e.t0 e.TA + D.wfa1 ≤ e.TA2 + D.wa01 ∧ RowsR D dz e.t0 e.TA e.TA2 e.u
  | .wri => (e.L + M ≤ e.t0 ∧ e.t0 < e.TA ∧ e.TA < e.TA2 ∧ e.TA < e.Hz ∧ e.Hz ≤ e.u) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r1 t = (decide (t < e.t0) || decide (e.u ≤ t))) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r2 t = decide (e.v ≤ t)) ∧
      e.u + D.wr1s ≤ e.v + D.wr2s ∧
      (∀ t, e.a ≤ t → t < e.Hz → s.A0 t = (decide (t < e.TA) || decide (e.TA2 ≤ t))) ∧
      TF D e.t0 e.TA < e.u ∧ TF D e.t0 e.TA + D.wfa1 ≤ GU D e.u + D.wg1 ∧
      TF D e.t0 e.TA + D.wfa1 ≤ e.TA2 + D.wa01 ∧ RowsR D dz e.t0 e.TA e.TA2 e.u
  | .wx => (e.L + M ≤ e.v ∧ e.L + M ≤ e.u ∧ e.v < e.TA2 ∧ e.TA2 < e.Hz) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r1 t = decide (e.u ≤ t)) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r2 t = decide (e.v ≤ t)) ∧
      (∀ t, e.a ≤ t → t < e.Hz → s.A0 t = decide (e.TA2 ≤ t)) ∧
      SepX D e.v e.u ∧ RowsX D dz e.v e.TA2
  | .e1 => (e.L + M ≤ e.t0 ∧ e.t0 < e.TA ∧ e.TA < e.TA2 ∧ e.TA2 < e.Hz ∧ e.t0 < e.u) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r1 t = (decide (t < e.t0) || decide (e.u ≤ t))) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r2 t = true) ∧
      (∀ t, e.a ≤ t → t < e.Hz → s.A0 t = (decide (t < e.TA) || decide (e.TA2 ≤ t))) ∧
      RQ D e.TA e.u ∧ RRc D e.TA e.u ∧ RG D e.TA e.u ∧ RT1 D ∧
      T1 D e.t0 e.TA + D.wfa1 ≤ e.TA2 + D.wa01 ∧ e.TA + D.wa02 ≤ G2 D e.TA + D.wg2 ∧
      T1 D e.t0 e.TA < e.u ∧ Rows1 D dz e.t0 e.TA e.TA2
  | .e2 => (e.L + M ≤ e.t0 ∧ e.t0 < e.TA ∧ e.TA < e.TA2 ∧ e.TA2 < e.Hz ∧ e.t0 < e.u) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r1 t = true) ∧
      (∀ t, e.L ≤ t → t < e.Hz → s.r2 t = (decide (t < e.t0) || decide (e.u ≤ t))) ∧
      (∀ t, e.a ≤ t → t < e.Hz → s.A0 t = (decide (t < e.TA) || decide (e.TA2 ≤ t))) ∧
      RQ2 D e.TA e.u ∧ RRc2 D e.TA e.u ∧ RG2 D e.TA e.u ∧ RT1b D ∧
      T1b D e.t0 e.TA + D.wfa2 ≤ e.TA2 + D.wa02 ∧ e.TA + D.wa01 ≤ G1b D e.TA + D.wg1 ∧
      T1b D e.t0 e.TA < e.u ∧ Rows2 D dz e.t0 e.TA e.TA2

/-- The field conjunction at a tick: C's six step fields and grant exclusion. -/
def FX (s : Sigs) (z : Int → Bool) (t : Int) : Prop := CF s z t ∧ (s.g1 t && s.g2 t) = false

theorem anc_true {s : Sigs} {a : Int} (h : Anc s true a) : s.A0 (a - 1) = false := by
  rcases h with h | ⟨h, _⟩
  · exact h
  · exact absurd h (by simp)

section step
variable {D : Dl} {M : Int} {s : Sigs} {z : Int → Bool} {dz : Int}

/-- **One window.** For every epoch kind: the epoch hypotheses and the start condition give
the field conjunction on `[L + M + dz, Hz - 1)` and the end condition. -/
theorem win_step (R : Run D s) (hM : MB D M) (Z : ZLine s z dz) (hdz : 0 ≤ dz) (e : Ep)
    (hok : EpOK D M s dz e) (hst : StartC M s e) :
    (∀ t, e.L + M + dz ≤ t → t < e.Hz - 1 → FX s z t) ∧ EndC D s e := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have hp := hM.pos
  obtain ⟨st, sR, sA, saL⟩ := hst
  cases hk : e.k with
  | hold m c1 c2 =>
    simp only [EpOK, startMode, first, hk] at hok st sR sA
    obtain ⟨hF, hin⟩ := hok
    have H := hold_st R hM hF st hin
    refine ⟨fun t h1 h2 => hold_fields R hM hF st hin Z hdz t h1 (by omega), ?_⟩
    simp only [EndC, endMode, Lend, aEnd, hk]
    refine ⟨H, fun t h1 h2 => ?_, sA, saL⟩
    by_cases h : t < e.L
    · exact sR t h1 (by omega)
    · exact (H t (by omega) h2).2.2.2.2.2
  | wg =>
    simp only [EpOK, startMode, first, Md.A0, Md.R0, hk] at hok st sR sA
    obtain ⟨⟨o1, o2, o3⟩, hr1, hr2, hsep, hA0, K⟩ := hok
    have S : WG D M s e.a e.L e.u e.TA2 e.v e.Hz :=
      ⟨⟨saL, o1, o2, hp⟩, hr1, hr2, hsep, hA0, sA, sR,
        fun t h1 h2 => (st t h1 h2).1, fun t h1 h2 => (st t h1 h2).2.1,
        fun t h1 h2 => (st t h1 h2).2.2.1, fun t h1 h2 => (st t h1 h2).2.2.2.1,
        fun t h1 h2 => (st t h1 h2).2.2.2.2.1⟩
    have hT := wg_TA2 R hM S o3
    have e1 : TU D e.u e.TA2 ≥ GU D e.u + D.wg1 + D.c1r ∧ TU D e.u e.TA2 ≥ e.TA2 + D.wa01 + D.c1r := by
      unfold TU; omega
    refine ⟨fun t h1 h2 => ⟨wg_fields R hM S Z K t h1 (by omega),
      wg_excl R hM S t (by omega) (by omega)⟩, ?_⟩
    simp only [EndC, endMode, Lend, aEnd, hk]
    refine ⟨fun t h1 h2 => ⟨wg_q R hM S t (by omega) h2, ?_, wg_g2 R hM S t (by omega) h2, ?_,
      wg_A2 R hM S t (by omega) h2, ?_⟩, fun t h1 h2 => ?_, Or.inl ?_, by omega⟩
    · rw [wg_g1 R hM S t (by omega) h2]; simp [Md.g1]; omega
    · rw [wg_A1 R hM S t (by omega) h2]; simp [Md.A1]; omega
    · rw [wg_R0 R hM S t (by omega) h2]; simp [Md.R0]; omega
    · rw [wg_R0 R hM S t (by omega) h2]; simp [Md.R0]; omega
    · rw [hA0 _ (by omega) (by omega)]; simp [Md.A0] <;> omega
  | wrr =>
    simp only [EpOK, startMode, first, Md.A0, Md.R0, hk] at hok st sR sA
    obtain ⟨⟨o1, o2, o3, o4, o5, o6⟩, hr1, hr2, hsep, hA0, hC, hRA, hRT, K⟩ := hok
    have S : WR D M s e.a e.L e.t0 e.TA e.TA2 e.u e.v e.Hz :=
      ⟨⟨saL, o1, o2, o3, by omega, o4, hp⟩, hr1, hr2, hsep, hA0, anc_true sA, sR,
        fun t h1 h2 => (st t h1 h2).1, fun t h1 h2 => (st t h1 h2).2.1,
        fun t h1 h2 => (st t h1 h2).2.2.1, fun t h1 h2 => (st t h1 h2).2.2.2.1,
        fun t h1 h2 => (st t h1 h2).2.2.2.2.1⟩
    have hT := wr_TA2 R hM S o6
    have hTA := wr_TA R hM S
    have e1 : TU D e.u e.TA2 ≥ GU D e.u + D.wg1 + D.c1r ∧ TU D e.u e.TA2 ≥ e.TA2 + D.wa01 + D.c1r := by
      unfold TU; omega
    have e2 : GF D e.t0 < e.u := by
      have : TF D e.t0 e.TA ≥ GF D e.t0 + D.wg1 + D.c1f := by unfold TF; omega
      omega
    refine ⟨fun t h1 h2 => ⟨wr_fields R hM S hC hRA hRT Z K t h1 (by omega),
      wr_excl R hM S t (by omega) (by omega)⟩, ?_⟩
    simp only [EndC, endMode, Lend, aEnd, hk]
    refine ⟨fun t h1 h2 => ⟨wr_q R hM S t (by omega) h2, ?_, wr_g2 R hM S t (by omega) h2, ?_,
      wr_A2 R hM S t (by omega) h2, ?_⟩, fun t h1 h2 => ?_, Or.inl ?_, by omega⟩
    · rw [wr_g1 R hM S t (by omega) h2]; simp [Md.g1]; omega
    · rw [wr_A1 R hM S hC hRA hRT t (by omega) h2]; simp [Md.A1]; omega
    · rw [wr_R0 R hM S t (by omega) h2]; simp [Md.R0]; unfold TR RU at *; omega
    · rw [wr_R0 R hM S t (by omega) h2]; simp [Md.R0]; unfold TR RU at *; omega
    · rw [hA0 _ (by omega) (by omega)]; simp [Md.A0] <;> omega
  | wri =>
    simp only [EpOK, startMode, first, Md.A0, Md.R0, hk] at hok st sR sA
    obtain ⟨⟨o1, o2, o3, o4, o5⟩, hr1, hr2, hsep, hA0, hC, hRA, hRT, K⟩ := hok
    have S : WR D M s e.a e.L e.t0 e.TA e.TA2 e.u e.v e.Hz :=
      ⟨⟨saL, o1, o2, o3, o4, by omega, hp⟩, hr1, hr2, hsep, hA0, anc_true sA, sR,
        fun t h1 h2 => (st t h1 h2).1, fun t h1 h2 => (st t h1 h2).2.1,
        fun t h1 h2 => (st t h1 h2).2.2.1, fun t h1 h2 => (st t h1 h2).2.2.2.1,
        fun t h1 h2 => (st t h1 h2).2.2.2.2.1⟩
    have hTA := wr_TA R hM S
    have e1 : TU D e.u e.TA2 ≥ GU D e.u + D.wg1 + D.c1r := by unfold TU; omega
    have e2 : TF D e.t0 e.TA ≥ GF D e.t0 + D.wg1 + D.c1f ∧ TF D e.t0 e.TA ≥ e.TA + D.wa01 + D.c1f := by
      unfold TF; omega
    have e3 : e.u ≤ GU D e.u := by unfold GU; omega
    refine ⟨fun t h1 h2 => ⟨wr_fields R hM S hC hRA hRT Z K t h1 (by omega),
      wr_excl R hM S t (by omega) (by omega)⟩, ?_⟩
    simp only [EndC, endMode, Lend, aEnd, hk]
    refine ⟨fun t h1 h2 => ⟨wr_q R hM S t (by omega) h2, ?_, wr_g2 R hM S t (by omega) h2, ?_,
      wr_A2 R hM S t (by omega) h2, ?_⟩, fun t h1 h2 => ?_, Or.inl ?_, by omega⟩
    · rw [wr_g1 R hM S t (by omega) h2]; simp [Md.g1]; omega
    · rw [wr_A1 R hM S hC hRA hRT t (by omega) h2]; simp [Md.A1]; omega
    · rw [wr_R0 R hM S t (by omega) h2]; simp [Md.R0]; unfold TR RU at *; omega
    · rw [wr_R0 R hM S t (by omega) h2]; simp [Md.R0]; unfold TR RU at *; omega
    · rw [hA0 _ (by omega) (by omega)]; simp [Md.A0] <;> omega
  | wx =>
    simp only [EpOK, startMode, first, Md.A0, Md.R0, hk] at hok st sR sA
    obtain ⟨⟨o1, o2, o3, o4⟩, hr1, hr2, hA0, H, K⟩ := hok
    have S : WX D M s e.a e.L e.v e.TA2 e.u e.Hz :=
      ⟨⟨saL, o1, o2, o3, hp⟩, hr1, hr2, hA0, sA, sR,
        fun t h1 h2 => (st t h1 h2).1, fun t h1 h2 => (st t h1 h2).2.1,
        fun t h1 h2 => (st t h1 h2).2.2.1, fun t h1 h2 => (st t h1 h2).2.2.2.1,
        fun t h1 h2 => (st t h1 h2).2.2.2.2.1⟩
    obtain ⟨hq, hg1, hg2, hR0, hA1, hA2, hsrv⟩ := wx_all R hM S H
    have hT := hsrv o4
    have e1 : TX D e.v e.TA2 ≥ GX D e.v + D.wg2 + D.c2r ∧ TX D e.v e.TA2 ≥ e.TA2 + D.wa02 + D.c2r := by
      unfold TX; omega
    have e2 : RX D e.v ≥ QX D e.v := by unfold RX; omega
    refine ⟨fun t h1 h2 => ⟨wx_fields R hM S H Z K t h1 (by omega),
      wx_excl R hM S H t (by omega) (by omega)⟩, ?_⟩
    simp only [EndC, endMode, Lend, aEnd, hk]
    refine ⟨fun t h1 h2 => ⟨?_, hg1 t (by omega) h2, ?_, hA1 t (by omega) h2, ?_, ?_⟩,
      fun t h1 h2 => ?_, Or.inl ?_, by omega⟩
    · rw [hq t (by omega) h2]; simp [Md.q]; omega
    · rw [hg2 t (by omega) h2]; simp [Md.g2]; omega
    · rw [hA2 t (by omega) h2]; simp [Md.A2]; omega
    · rw [hR0 t (by omega) h2]; simp [Md.R0]; omega
    · rw [hR0 t (by omega) h2]; simp [Md.R0]; omega
    · rw [hA0 _ (by omega) (by omega)]; simp [Md.A0] <;> omega
  | e1 =>
    simp only [EpOK, startMode, first, Md.A0, Md.R0, hk] at hok st sR sA
    obtain ⟨⟨o1, o2, o3, o4, o5⟩, hr1, hr2, hA0, hQ, hRR, hG, hRT1, hRT2a, hF, hC, K⟩ := hok
    have S : E1 D M s e.a e.L e.t0 e.TA e.TA2 e.u e.Hz :=
      ⟨⟨saL, o1, o2, o3, o4, o5, hp⟩, hr1, hr2, hA0, anc_true sA, sR,
        fun t h1 h2 => (st t h1 h2).1, fun t h1 h2 => (st t h1 h2).2.2.2.1,
        fun t h1 h2 => (st t h1 h2).2.2.2.2.1, fun t h1 h2 => (st t h1 h2).2.1,
        fun t h1 h2 => (st t h1 h2).2.2.1⟩
    have hH := e_HQ R hM S hRR
    have hT := e_TA2_ge R hM S hRR
    have e1 := T2r_cases D e.TA e.TA2
    have e2 : T1 D e.t0 e.TA ≥ G1 D e.t0 e.TA + D.wg1 + D.c1f := by unfold T1; omega
    have e3 : RR D e.TA ≥ QB D e.TA := by unfold RR; omega
    refine ⟨fun t h1 h2 => ⟨e_fields R hM S hQ hRR hG hRT2a hF hC Z K t h1 (by omega),
      e_exclusion R hM S hQ hH hG hRT1 t (by omega) (by omega)⟩, ?_⟩
    simp only [EndC, endMode, Lend, aEnd, hk]
    refine ⟨fun t h1 h2 => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun t h1 h2 => ?_, Or.inl ?_, by omega⟩
    · rw [e_q_eq R hM S hQ hH t (by omega) h2]; simp [Md.q]; omega
    · rw [e_g1_eq R hM S hQ hH hG t (by omega) h2]; simp [Md.g1]; omega
    · rw [e_g2_eq R hM S hQ hH t (by omega) h2]; simp [Md.g2]; omega
    · rw [e_A1_eq R hM S hQ hH hG hRT2a t (by omega) h2]; simp [Md.A1]; omega
    · rw [e_A2_eq R hM S hQ hH hF t (by omega) h2]; simp [Md.A2]; omega
    · rw [e_R0_eq R hM S hQ hRR t (by omega) h2]; simp [Md.R0]; omega
    · rw [e_R0_eq R hM S hQ hRR t (by omega) h2]; simp [Md.R0]; omega
    · rw [hA0 _ (by omega) (by omega)]; simp [Md.A0] <;> omega
  | e2 =>
    simp only [EpOK, startMode, first, Md.A0, Md.R0, hk] at hok st sR sA
    obtain ⟨⟨o1, o2, o3, o4, o5⟩, hr1, hr2, hA0, hQ, hRR, hG, hRT1, hRT2a, hF, hC, K⟩ := hok
    have S : E2 D M s e.a e.L e.t0 e.TA e.TA2 e.u e.Hz :=
      ⟨⟨saL, o1, o2, o3, o4, o5, hp⟩, hr1, hr2, hA0, anc_true sA, sR,
        fun t h1 h2 => (st t h1 h2).1, fun t h1 h2 => (st t h1 h2).2.2.2.1,
        fun t h1 h2 => (st t h1 h2).2.2.2.2.1, fun t h1 h2 => (st t h1 h2).2.1,
        fun t h1 h2 => (st t h1 h2).2.2.1⟩
    have hH := f_HQ R hM S hRR
    have hT := f_TA2_ge R hM S hRR
    have e1 := T2rb_cases D e.TA e.TA2
    have e2 : T1b D e.t0 e.TA ≥ G2b D e.t0 e.TA + D.wg2 + D.c2f := by unfold T1b; omega
    have e3 : RRb D e.TA ≥ QBb D e.TA := by unfold RRb; omega
    refine ⟨fun t h1 h2 => ⟨f_fields R hM S hQ hRR hG hRT2a hF hC Z K t h1 (by omega),
      f_exclusion R hM S hQ hRR hG hRT1 t (by omega) (by omega)⟩, ?_⟩
    simp only [EndC, endMode, Lend, aEnd, hk]
    refine ⟨fun t h1 h2 => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun t h1 h2 => ?_, Or.inl ?_, by omega⟩
    · rw [f_q_eq R hM S hQ hH t (by omega) h2]; simp [Md.q]; omega
    · rw [f_g1_eq R hM S hQ hH t (by omega) h2]; simp [Md.g1]; omega
    · rw [f_g2_eq R hM S hQ hH hG t (by omega) h2]; simp [Md.g2]; omega
    · rw [f_A1_eq R hM S hQ hH hF t (by omega) h2]; simp [Md.A1]; omega
    · rw [f_A2_eq R hM S hQ hH hG hRT2a t (by omega) h2]; simp [Md.A2]; omega
    · rw [f_R0_eq R hM S hQ hRR t (by omega) h2]; simp [Md.R0]; omega
    · rw [f_R0_eq R hM S hQ hRR t (by omega) h2]; simp [Md.R0]; omega
    · rw [hA0 _ (by omega) (by omega)]; simp [Md.A0] <;> omega

end step

/-! ## The schedule class and the whole run -/

/-- Boundary match between consecutive epochs: the next start mode is this end mode, the
next anchor is this window's last A0 edge, the next window starts after this one settled and
its settled part ends before this window's horizon, and the windows overlap by more than
`M + dz` (so that their field ranges abut). -/
def Link (D : Dl) (M dz : Int) (e e' : Ep) : Prop :=
  startMode e'.k = endMode e.k ∧ e'.a = aEnd e ∧ Lend D e ≤ e'.L ∧ first M e' ≤ e.Hz ∧
  e'.L + M + dz + 1 ≤ e.Hz

/-- **The schedule class**: a run from reset cut into infinitely many epochs of the kinds
above, each meeting its epoch hypotheses, consecutive ones linked, reaching every time;
epoch 0 is the reset epoch (idle, requests low, starting from the reset past `rst`). -/
structure Plan (D : Dl) (M : Int) (s : Sigs) (dz : Int) where
  ep : Nat → Ep
  ok : ∀ k, EpOK D M s dz (ep k)
  link : ∀ k, Link D M dz (ep k) (ep (k + 1))
  unb : ∀ t : Int, ∃ k, t < (ep k).Hz - 1
  k0 : (ep 0).k = .hold .I false false
  a0 : (ep 0).a = (ep 0).L
  L0 : (ep 0).L + M + dz ≤ 0
  Hz0 : 0 < (ep 0).Hz
  rst : ∀ t, t < 0 → InSt s .I t
  dz0 : 0 ≤ dz

theorem link_start {D : Dl} {M dz : Int} {s : Sigs} {e e' : Ep} (hdz : 0 ≤ dz)
    (hE : EndC D s e) (hL : Link D M dz e e') : StartC M s e' := by
  obtain ⟨E1, E2, E3, E4⟩ := hE
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  refine ⟨fun t h1 h2 => by rw [l1]; exact E1 t (by omega) (by omega),
    fun t h1 h2 => by rw [l1]; exact E2 t (by omega) (by omega), by rw [l1, l2]; exact E3,
    by omega⟩

theorem plan_start0 {D : Dl} {M : Int} {s : Sigs} {dz : Int} (hM : MB D M) (P : Plan D M s dz) :
    StartC M s (P.ep 0) := by
  have := P.L0; have := P.dz0; have := hM.pos
  have hk := P.k0; have ha := P.a0
  refine ⟨fun t h1 h2 => ?_, fun t h1 h2 => ?_, ?_, by omega⟩
  · simp only [first, startMode, hk] at h2 ⊢; exact P.rst t (by omega)
  · simp only [startMode, hk, Md.R0]; exact (P.rst t (by omega)).2.2.2.2.2
  · simp only [startMode, hk, Md.A0]
    exact Or.inr ⟨rfl, fun t ht => (P.rst t (by omega)).2.2.2.2.2⟩

/-- **The fields at every tick of a scheduled run.** Assumed: the gate model, H_M, the z
line, and a schedule in the class `Plan`. Proved: C's six step fields (`CF`) and grant
exclusion at every `t ≥ 0`. -/
theorem run_fields {D : Dl} {M : Int} {s : Sigs} {z : Int → Bool} {dz : Int}
    (R : Run D s) (hM : MB D M) (Z : ZLine s z dz) (P : Plan D M s dz) :
    ∀ t, 0 ≤ t → FX s z t := by
  have hS := stitch_run (Start := fun k => StartC M s (P.ep k)) (F := FX s z)
    (fun k => (P.ep k).L + M + dz) (fun k => (P.ep k).Hz - 1) (plan_start0 hM P)
    (fun k hk => ⟨(win_step R hM Z P.dz0 (P.ep k) (P.ok k) hk).1,
      link_start P.dz0 (win_step R hM Z P.dz0 (P.ep k) (P.ok k) hk).2 (P.link k)⟩)
    (fun k => by have := (P.link k).2.2.2.2; omega) P.unb
  intro t ht
  exact hS t (by have := P.L0; omega)

open Formal.Net.Handshake (Chan) in
open Formal.Net.Ops.CM (AMerge) in
open Formal.Net.Ops.Mux (b2n) in
/-- **C's `OpsCM.AMerge` instantiated for the held `bd_arbiter`** on any schedule of the
class `Plan`, at C's tick = 1 ps (`n ↦ n`): x = client 1 (req r1, ack A1), y = client 2
(req r2, ack A2), z = the output (req = R0 through the delay line, ack = A0), grants g1, g2.
Every field is derived from the gate model except `dat`, which B does not model (the data
mux `z_data = won ? in1 : in0`); it is the one remaining hypothesis `H_DAT`. -/
theorem amerge_of_plan {D : Dl} {M : Int} {s : Sigs} {z : Int → Bool} {dz : Int}
    (R : Run D s) (hM : MB D M) (Z : ZLine s z dz) (P : Plan D M s dz)
    (xd yd zd : Nat → Nat)
    (H_DAT : ∀ n : Nat, zd n = 2 * (if (s.g2 n || s.A2 n) then yd n else xd n) +
      b2n (s.g2 n || s.A2 n)) :
    AMerge ⟨fun n => s.r1 n, fun n => s.A1 n, xd⟩ ⟨fun n => s.r2 n, fun n => s.A2 n, yd⟩
      ⟨fun n => z n, fun n => s.A0 n, zd⟩ (fun n => s.g1 n) (fun n => s.g2 n) := by
  have F := fun (n : Nat) => run_fields R hM Z P (n : Int) (by omega)
  have c : ∀ n : Nat, ((n + 1 : Nat) : Int) = (n : Int) + 1 := by intro n; omega
  have E0 := (win_step R hM Z P.dz0 (P.ep 0) (P.ok 0) (plan_start0 hM P)).2.1
  simp only [Lend, endMode, P.k0] at E0
  have := P.L0; have := P.Hz0; have := P.dz0; have := hM.pos
  have I0 := E0 0 (by omega) (by omega)
  have Iz := E0 (0 - dz) (by omega) (by omega)
  refine ⟨fun t => ?_, fun t => ?_, fun t => (F t).2, fun t => ?_, fun t => ?_, fun t => ?_,
    fun t => ?_, H_DAT, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [c]; exact (F t).1.1.1
  · simp only [c]; exact (F t).1.1.2
  · simp only [c]; exact (F t).1.2.1
  · simp only [c]; exact (F t).1.2.2.1
  · simp only [c]; exact (F t).1.2.2.2.1
  · simp only [c]; exact (F t).1.2.2.2.2
  · exact I0.2.1
  · exact I0.2.2.1
  · show z ((0 : Nat) : Int) = false
    rw [Z]; exact Iz.2.2.2.2.2
  · exact I0.2.2.2.1
  · exact I0.2.2.2.2.1

/-! ## Constructors for the epoch hypotheses (one per kind) -/

section ctor
variable {D : Dl} {M : Int} {s : Sigs} {dz : Int} {e : Ep}

theorem epok_hold {m : Md} {c1 c2 : Bool} (h : e.k = .hold m c1 c2) (hF : Fix m c1 c2)
    (hin : ∀ t, e.L ≤ t → t < e.Hz → s.r1 t = c1 ∧ s.r2 t = c2 ∧ s.A0 t = m.A0) :
    EpOK D M s dz e := by
  simp only [EpOK, h]; exact ⟨hF, hin⟩

theorem epok_wg (h : e.k = .wg) (o : e.L + M ≤ e.u ∧ e.u < e.TA2 ∧ e.TA2 < e.Hz)
    (r1 : ∀ t, e.L ≤ t → t < e.Hz → s.r1 t = decide (e.u ≤ t))
    (r2 : ∀ t, e.L ≤ t → t < e.Hz → s.r2 t = decide (e.v ≤ t))
    (sp : e.u + D.wr1s ≤ e.v + D.wr2s)
    (a0 : ∀ t, e.a ≤ t → t < e.Hz → s.A0 t = decide (e.TA2 ≤ t)) (K : RowsG D dz e.u e.TA2) :
    EpOK D M s dz e := by
  simp only [EpOK, h]; exact ⟨o, r1, r2, sp, a0, K⟩

theorem epok_wrr (h : e.k = .wrr)
    (o : e.L + M ≤ e.t0 ∧ e.t0 < e.TA ∧ e.TA < e.TA2 ∧ e.t0 < e.u ∧ e.u < e.Hz ∧ e.TA2 < e.Hz)
    (r1 : ∀ t, e.L ≤ t → t < e.Hz → s.r1 t = (decide (t < e.t0) || decide (e.u ≤ t)))
    (r2 : ∀ t, e.L ≤ t → t < e.Hz → s.r2 t = decide (e.v ≤ t))
    (sp : e.u + D.wr1s ≤ e.v + D.wr2s)
    (a0 : ∀ t, e.a ≤ t → t < e.Hz → s.A0 t = (decide (t < e.TA) || decide (e.TA2 ≤ t)))
    (x1 : TF D e.t0 e.TA < e.u ∧ TF D e.t0 e.TA + D.wfa1 ≤ GU D e.u + D.wg1 ∧
      TF D e.t0 e.TA + D.wfa1 ≤ e.TA2 + D.wa01) (K : RowsR D dz e.t0 e.TA e.TA2 e.u) :
    EpOK D M s dz e := by
  simp only [EpOK, h]; exact ⟨o, r1, r2, sp, a0, x1.1, x1.2.1, x1.2.2, K⟩

theorem epok_wri (h : e.k = .wri)
    (o : e.L + M ≤ e.t0 ∧ e.t0 < e.TA ∧ e.TA < e.TA2 ∧ e.TA < e.Hz ∧ e.Hz ≤ e.u)
    (r1 : ∀ t, e.L ≤ t → t < e.Hz → s.r1 t = (decide (t < e.t0) || decide (e.u ≤ t)))
    (r2 : ∀ t, e.L ≤ t → t < e.Hz → s.r2 t = decide (e.v ≤ t))
    (sp : e.u + D.wr1s ≤ e.v + D.wr2s)
    (a0 : ∀ t, e.a ≤ t → t < e.Hz → s.A0 t = (decide (t < e.TA) || decide (e.TA2 ≤ t)))
    (x1 : TF D e.t0 e.TA < e.u ∧ TF D e.t0 e.TA + D.wfa1 ≤ GU D e.u + D.wg1 ∧
      TF D e.t0 e.TA + D.wfa1 ≤ e.TA2 + D.wa01) (K : RowsR D dz e.t0 e.TA e.TA2 e.u) :
    EpOK D M s dz e := by
  simp only [EpOK, h]; exact ⟨o, r1, r2, sp, a0, x1.1, x1.2.1, x1.2.2, K⟩

theorem epok_wx (h : e.k = .wx) (o : e.L + M ≤ e.v ∧ e.L + M ≤ e.u ∧ e.v < e.TA2 ∧ e.TA2 < e.Hz)
    (r1 : ∀ t, e.L ≤ t → t < e.Hz → s.r1 t = decide (e.u ≤ t))
    (r2 : ∀ t, e.L ≤ t → t < e.Hz → s.r2 t = decide (e.v ≤ t))
    (a0 : ∀ t, e.a ≤ t → t < e.Hz → s.A0 t = decide (e.TA2 ≤ t))
    (H : SepX D e.v e.u) (K : RowsX D dz e.v e.TA2) : EpOK D M s dz e := by
  simp only [EpOK, h]; exact ⟨o, r1, r2, a0, H, K⟩

theorem epok_e1 (h : e.k = .e1)
    (o : e.L + M ≤ e.t0 ∧ e.t0 < e.TA ∧ e.TA < e.TA2 ∧ e.TA2 < e.Hz ∧ e.t0 < e.u)
    (r1 : ∀ t, e.L ≤ t → t < e.Hz → s.r1 t = (decide (t < e.t0) || decide (e.u ≤ t)))
    (r2 : ∀ t, e.L ≤ t → t < e.Hz → s.r2 t = true)
    (a0 : ∀ t, e.a ≤ t → t < e.Hz → s.A0 t = (decide (t < e.TA) || decide (e.TA2 ≤ t)))
    (x : RQ D e.TA e.u ∧ RRc D e.TA e.u ∧ RG D e.TA e.u ∧ RT1 D ∧
      T1 D e.t0 e.TA + D.wfa1 ≤ e.TA2 + D.wa01 ∧ e.TA + D.wa02 ≤ G2 D e.TA + D.wg2 ∧
      T1 D e.t0 e.TA < e.u) (K : Rows1 D dz e.t0 e.TA e.TA2) : EpOK D M s dz e := by
  simp only [EpOK, h]
  exact ⟨o, r1, r2, a0, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, K⟩

theorem epok_e2 (h : e.k = .e2)
    (o : e.L + M ≤ e.t0 ∧ e.t0 < e.TA ∧ e.TA < e.TA2 ∧ e.TA2 < e.Hz ∧ e.t0 < e.u)
    (r1 : ∀ t, e.L ≤ t → t < e.Hz → s.r1 t = true)
    (r2 : ∀ t, e.L ≤ t → t < e.Hz → s.r2 t = (decide (t < e.t0) || decide (e.u ≤ t)))
    (a0 : ∀ t, e.a ≤ t → t < e.Hz → s.A0 t = (decide (t < e.TA) || decide (e.TA2 ≤ t)))
    (x : RQ2 D e.TA e.u ∧ RRc2 D e.TA e.u ∧ RG2 D e.TA e.u ∧ RT1b D ∧
      T1b D e.t0 e.TA + D.wfa2 ≤ e.TA2 + D.wa02 ∧ e.TA + D.wa01 ≤ G1b D e.TA + D.wg1 ∧
      T1b D e.t0 e.TA < e.u) (K : Rows2 D dz e.t0 e.TA e.TA2) : EpOK D M s dz e := by
  simp only [EpOK, h]
  exact ⟨o, r1, r2, a0, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, K⟩

end ctor

end Formal.Cells.ArbAMergeRun
