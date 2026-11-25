import Formal.Cells.AMergeTimedW

/-!
# Necessity3AMerge: `bdc_amerge.bundled_idx_ack_g` (BidxB.gack) is tight

Probe Bsx3 (shard B). Row `bdc_amerge.bundled_idx_ack_g` was "sufficient;
no counter-trace for this leg". Its theorem is
`AMergeTimed.bidx_old_owner` (Cm2 model: Int ps, 7h's arbiter `Run` with the
REAL INITs and every route, 7j's mirror scenario `Scn2`, the inferred index
LUT `g2 | in1_ack` as the rise-fast OR channel, transport consumer
`wid` + setup `su`, request path `dz`); its field `gack` is the OR of the
r2 form and the q form (g2 falls by its EARLIER cause).

## Results

* `gack_counter` (general, every run): in ANY run of `Run` + `Scn2` whose
  server answers in exactly `smin` (`TA = TRb + smin`), if BOTH forms of
  `gack` fail, the consumer still sees `index = 1` (the previous owner)
  `su` before the minimal capture `RRb + dz`. So the OR is the exact
  condition at the minimal capture with a worst-case server; ack and grant
  play no part in it.
* `GackClaim s` is `bidx_old_owner` with both forms of `gack` weakened by
  `s` (RT2b, ack, grant, H_REQ_PATH, Run, Scn2 verbatim). `gack0` is the
  shipped theorem; `gack1_false : ¬ GackClaim 1`.
  Counter-run `W2G` (one consistent corner: O6 arcs 4, O5 from I0/I1 4,
  O5 from I2 4, server 10, every route 0 except r2 -> ugrant.I1 = 16;
  index LUT 3, `wid = su = 0`, `dz = 4`): the r2 form is off by exactly 1
  (27 vs 26), the q form by 3; RT2b, ack and grant hold. g2 falls at 20,
  A2 at 24, and the index is 1 at the capture 26 (A2 still high in its
  view at 23).

Not covered: a server slower than `smin` or a capture later than
`RRb + dz` (the field is a worst-case bound there); the edge-sampling
consumer caveat of the row (Bfd) is unchanged.

Core Lean only.
-/

namespace Formal.Cells.Necessity3AMerge
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2 Formal.Cells.AMergeTimed

/-- The r2 form of `gack`, weakened by `s`. -/
def GackR (D : Dl) (W : Wd) (s : Int) : Prop :=
  D.wr2g + D.g2f + D.wg2 + D.c2f + W.wai + W.xf + W.wid + W.su ≤
    D.wr2s + D.Rf2 + D.smin + D.wa0s + D.qr + D.wfb + D.Rrq + W.dz + s
/-- The q form of `gack`, weakened by `s`. -/
def GackQ (D : Dl) (W : Wd) (s : Int) : Prop :=
  D.wq + D.g2f + D.wg2 + D.c2f + W.wai + W.xf + W.wid + W.su ≤ D.wfb + D.Rrq + W.dz + s

/-- `BidxB` with `gack` weakened by `s` (ack, grant verbatim). -/
structure BidxBs (D : Dl) (W : Wd) (s : Int) : Prop where
  ack : D.wa02 + D.c2f + W.wai + W.xf + W.wid + W.su ≤ D.wa0s + D.qr + D.wfb + D.Rrq + W.dz
  gack : GackR D W s ∨ GackQ D W s
  grant : D.wr2g + D.g2f + W.wgi + W.xf + W.wid + W.su ≤
      D.wr2s + D.Rf2 + D.smin + D.wa0s + D.qr + D.wfb + D.Rrq + W.dz ∨
    D.wq + D.g2f + W.wgi + W.xf + W.wid + W.su ≤ D.wfb + D.Rrq + W.dz

/-- `bidx_old_owner` with `gack` weakened by `s`. -/
def GackClaim (s : Int) : Prop :=
  ∀ (D : Dl) (sg : Sigs) (t0 ta TA TA2 Hz : Int) (W : Wd) (Zr : Int),
    Run D sg → Scn2 D sg t0 ta TA TA2 Hz → RT2b D → ReqZ sg (TRb D t0) Hz Zr W.dz →
    BidxBs D W s → ∀ t, Zr - W.su ≤ t → t - W.wid < Hz → Cons W sg t = false

theorem gack0 : GackClaim 0 := by
  intro D sg t0 ta TA TA2 Hz W Zr R S H hZ B t h1 h2
  refine bidx_old_owner R S H hZ ⟨B.ack, ?_, B.grant⟩ t h1 h2
  rcases B.gack with g | g
  · left; unfold GackR at g; omega
  · right; unfold GackQ at g; omega

/-! ## The general counter-trace -/

theorem idx_of_af (W : Wd) (sg : Sigs) (t : Int) (h : sg.A2 (t - W.wai - W.xf) = true) :
    Idx W sg t = true := by
  unfold Idx; rw [IX_eq, IX_eq, h]; simp

/-- **Both forms fail ⇒ stale index at the minimal capture**, in every run
whose server answers in exactly `smin`. -/
theorem gack_counter {D : Dl} {sg : Sigs} {t0 ta TA TA2 Hz : Int} {W : Wd}
    (R : Run D sg) (S : Scn2 D sg t0 ta TA TA2 Hz)
    (hTA : TA = TRb D t0 + D.smin) (hR : ¬ GackR D W 0) (hQ : ¬ GackQ D W 0)
    (hz : RRb D TA + W.dz - W.su - W.wid - W.wai - W.xf < Hz) :
    Cons W sg (RRb D TA + W.dz - W.su) = true := by
  unfold Cons; apply idx_of_af
  apply A2_hi_before2 R S _ _ hz
  unfold GackR at hR; unfold GackQ at hQ
  unfold T1b G2b RRb QBb; unfold TRb at hTA; omega

/-! ## The counter-run W2G -/

/-- One consistent corner (every O6 arc 4, every O5 arc 4), server 10, every
route 0 except r2 -> ugrant.I1 = 16. -/
def DG : Dl where
  wr1s := 0
  wr2s := 0
  wr1g := 0
  wr2g := 16
  wfb := 0
  wa0s := 0
  wq := 0
  wg1 := 0
  wa01 := 0
  wfa1 := 0
  wg2 := 0
  wa02 := 0
  wfa2 := 0
  qr := 4
  qf := 4
  Rr1 := 4
  Rf1 := 4
  Rr2 := 4
  Rf2 := 4
  Rrq := 4
  Rfq := 4
  g1r1 := 4
  g1f1 := 4
  g1r2 := 4
  g1f2 := 4
  g1rq := 4
  g1fq := 4
  g2r := 4
  g2f := 4
  c1r := 4
  c1f := 4
  c2r := 4
  c2f := 4
  smin := 10
  H_NONNEG := by omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by omega

/-- Index LUT arc 3, routes 0, no setup, request path 4. -/
def WG : Wd := ⟨0, 0, 3, 3, 0, 4, 0, by omega, by omega, by omega⟩

/-- r2 drops at 0, R0 falls at 4, A0 falls at 14 (server 10), q rises at 18,
R0 re-rises at 22, g1 at 22, A0 re-rises at 32, A1 at 36; g2 falls at 20
(r2 through the 16 ps route), A2 at 24. -/
def W2G : Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (18 ≤ t)
  R0 := fun t => decide (t < 4) || decide (22 ≤ t)
  g1 := fun t => decide (22 ≤ t)
  g2 := fun t => decide (t < 20)
  A0 := fun t => (decide (-1000 ≤ t) && decide (t < 14)) || decide (32 ≤ t)
  A1 := fun t => decide (36 ≤ t)
  A2 := fun t => decide (t < 24)

theorem W2G_run : Run DG W2G where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W2G, DG, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W2G, DG, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2G, DG, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2G, DG, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2G, DG, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2G, DG, CE_eq]; omega
  H_SRV := by
    intro t ht
    have e : t = -1000 ∨ t = 14 ∨ t = 32 := by
      exact Classical.byContradiction fun hc => ht (by rw [Bool.eq_iff_iff]; simp [W2G]; omega)
    rcases e with rfl | rfl | rfl
    · exact ⟨-1000 - 10, by simp [DG], by rw [Bool.eq_iff_iff]; simp [W2G],
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [W2G]; omega⟩
    · exact ⟨4, by simp [DG], by rw [Bool.eq_iff_iff]; simp [W2G],
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [W2G]; omega⟩
    · exact ⟨22, by simp [DG], by rw [Bool.eq_iff_iff]; simp [W2G],
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [W2G]; omega⟩

theorem W2G_scn : Scn2 DG W2G 0 (-1000) 14 32 100 where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W2G]; omega
  H_A0_prev := by simp [W2G]
  H_q_init := by intro t ht; simp [W2G]; omega
  H_A1_init := by intro t ht; simp [W2G]; omega
  H_A2_init := by intro t ht; simp [W2G]; omega
  H_SETTLED := by simp [DG]

theorem W2G_rt2b : RT2b DG := ⟨by decide, by decide, by decide, by decide⟩

/-- The minimal capture `RRb + dz = 22 + 4 = 26` is a legal `ReqZ` (R0 high at 22). -/
theorem W2G_reqz : ReqZ W2G (TRb DG 0) 100 26 WG.dz :=
  ⟨22, by decide, by decide, by decide, by decide⟩

/-- r2 form off by exactly 1 (27 = 26 + 1), q form off by 3 (11 vs 8);
ack (3 ≤ 8) and grant's q form (7 ≤ 8) hold. -/
theorem W2G_viol : GackR DG WG 1 ∧ ¬ GackR DG WG 0 ∧ ¬ GackQ DG WG 2 ∧
    BidxBs DG WG 1 := by
  refine ⟨?_, ?_, ?_, ⟨?_, Or.inl ?_, Or.inr ?_⟩⟩ <;> simp [GackR, GackQ, DG, WG]

/-- The index is 1 (stale) at the capture. -/
theorem W2G_stale : Cons WG W2G 26 = true := by decide

/-- **`gack` cannot be weakened by 1 ps.** -/
theorem gack1_false : ¬ GackClaim 1 := by
  intro h
  have := h DG W2G 0 (-1000) 14 32 100 WG 26 W2G_run W2G_scn W2G_rt2b W2G_reqz W2G_viol.2.2.2
    26 (by decide) (by decide)
  rw [W2G_stale] at this; exact absurd this (by decide)

/-- The general counter-trace applies to the same run (server exact:
`TA = 14 = TRb + smin`). -/
theorem W2G_general : Cons WG W2G (RRb DG 14 + WG.dz - WG.su) = true :=
  gack_counter W2G_run W2G_scn (by decide) W2G_viol.2.1
    (by simp [GackQ, DG, WG]) (by decide)

/-! Non-vacuity at slack 0: `AMergeTimedW.nonvacuous_slow` / `nonvacuous_fast`
(BidxB, RT2b, Run, Scn2 at both corners, index 0 at the capture). -/

end Formal.Cells.Necessity3AMerge
