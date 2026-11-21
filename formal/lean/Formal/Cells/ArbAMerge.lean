import Formal.Cells.ArbMultiToken

/-!
# Probe Barb3 (part 1): early re-request handover of the held `bd_arbiter`, `z_req`, C's fields

Probe Barb2 (`ArbMultiToken`) chained 7h/7j over alternating contention, but only under
H_SLOW_REREQ (`TA2 + 4M ≤ u`: the releasing client re-requests only after the handover
settled), and it had no `z_req`, so C's H_AMERGE_RTZ / `zr` were not derivable. This
file redoes the one-handover analysis on a WINDOW `[L, Hz)` (nothing assumed before `L`
except A0's last rise), with the releasing client's re-request `u` FREE, and adds the
z line. Core Lean; imports `ArbMultiToken` (for `MB`, `CArb`, `Dw`), hence 7h and 7j.

* `E1` / `E2`: the window scenarios (client 1 / client 2 releases, the other waits, the
  releaser re-requests at any `u > t0`). Exact traces on the window: q (`e_q_eq`,
  `f_q_eq`), R0 (`e_R0_eq`, `f_R0_eq`), g1, g2, A1, A2 (`e_A2_eq`, `f_A1_eq`, ...).
* The three races of notes/B-arb-multi-token.md, now exact per arc view:
  - Q (ustate): `RQ  : QB + wfb ≤ u + wr1s`, mirror `RQ2 : QBb + wfb ≤ u + wr2s`;
  - R (R0):     `RRc : RR ≤ u + wr1s + Rr1`, mirror `RRc2 : RRb ≤ u + wr2s + Rr2`
    (the fall-arc view is implied; the note's `QB+wfb+Rfq ≤ u+wr1s+Rr1` is stronger
    than needed);
  - G (grant):  `RG` (two views, g1 has per-pin arcs), mirror `RG2 : QBb + wq ≤ u + wr2g`.
  What race R protects is H_HOLDQ (`HQ`: A0's re-rise reaches ustate after q's reset came
  round), which the q/grant lemmas take directly; `e_HQ` derives it from race R + server.
* `e_exclusion`, `f_exclusion`: grant exclusion on the window for every server meeting
  H_SERVER_MIN, given RT1 / RT1b and the races. H_SLOW_REREQ is gone.
* `CF`: C's `OpsCM.AMerge` step fields H_ARB1, H_ARB2, `zr`, H_AMERGE_RTZ, `xa`, `ya`,
  verbatim, at the 1 ps tick, with `z` = R0 through the delay line (`ZLine`, H_DZ
  `0 ≤ dz ≤ smin`). `e_fields`, `f_fields`: all six hold at every tick of
  `[L + M + dz, Hz - 1)`, given the races, RT2a and the A0 fork (run form), the
  four-phase client (`T1 < u`) and the run-form tick rows `Rows1` / `Rows2`.
* Counter-runs at slack −1 (every hypothesis but one race, that race missed by 1 ps):
  `cex_Q` (H_ARB2 fails), `cex_G` (H_ARB1 fails), `cex_R` (`zr` fails, with the z-rise
  row tight), and the mirrors `cex_Q2` (H_ARB1), `cex_G2` (H_ARB2), `cex_R2` (`zr`).
  `cexG_run`: a concrete from-reset run for race G (the others are universal lemmas
  without a concrete run).
* `Arc1`, `Arc2`, `races_of_arc1/2`: with the four-phase client at zero reaction time the
  races follow from A0-fork-type arc inequalities.
* `early_nonvacuous`: a from-reset run (every signal low before 0, all delays nonzero)
  meets every hypothesis of both window theorems for two consecutive handovers, with both
  re-requests before A0's re-rise.

**Assumed:** 7h's gate model `Run` (real INITs, rise-fast OR channel per LUT, routed
delay per pin, H_SERVER_MIN on R0), H_M, H_ZLINE/H_DZ, the window scenario, the named
races and rows. **Proved:** see above. **NOT covered:** C's `AMerge` is still NOT
instantiated: the windows are not chained into a whole run (the chain needs a reset
epoch, solo/idle epochs, and the stitching of windows; only the alternating-contention
chain of `ArbMultiToken` exists, and it still assumes H_SLOW_REREQ); the init fields
(`i1`, `i2`, ...) and `dat` are not derived; solo client, idle gaps and same-client-twice
schedules have no window theorem; the server reads R0 (with `dz ≤ smin`), not `z`
(a server specified on `z` implies the R0 form only up to its constancy clause);
metastability (requests racing at an idle arbiter) is outside every window here.
-/

namespace Formal.Cells.ArbAMerge
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2 Formal.Cells.ArbMultiToken

/-! ## Tools -/

/-- Strong induction over `Int` on `[L, ∞)` with a base region `[L, a)`. -/
theorem int_ind_w (P : Int → Prop) (L a : Int) (hb : ∀ t, L ≤ t → t < a → P t)
    (hs : ∀ t, a ≤ t → (∀ v, L ≤ v → v < t → P v) → P t) : ∀ t, L ≤ t → P t := by
  have key : ∀ n : Nat, ∀ t, L ≤ t → t < a + n → P t := by
    intro n
    induction n with
    | zero => intro t h1 h2; exact hb t h1 (by omega)
    | succ n ih =>
      intro t h1 h2
      by_cases h : t < a + n
      · exact ih t h1 h
      · exact hs t (by omega) (fun v hv1 hv2 => ih v hv1 (by omega))
  intro t ht
  exact key (t - a + 1).toNat t ht (by omega)

/-- A Boolean trace that is high at `a` and low at `b > a` has a falling tick in `[a, b)`. -/
theorem fall_tick (f : Int → Bool) (a b : Int) (hab : a < b) (ha : f a = true) (hb : f b = false) :
    ∃ t, a ≤ t ∧ t < b ∧ f t = true ∧ f (t + 1) = false := by
  have key : ∀ n : Nat, ∀ c, a ≤ c → c + n = b → f c = true →
      ∃ t, c ≤ t ∧ t < b ∧ f t = true ∧ f (t + 1) = false := by
    intro n
    induction n with
    | zero => intro c _ h1 h2; rw [show c = b by omega, hb] at h2; exact absurd h2 (by simp)
    | succ n ih =>
      intro c hc h1 h2
      cases h3 : f (c + 1)
      · exact ⟨c, Int.le_refl _, by omega, h2, h3⟩
      · obtain ⟨t, ht1, ht2, ht3, ht4⟩ := ih (c + 1) (by omega) (by omega) h3
        exact ⟨t, by omega, ht2, ht3, ht4⟩
  exact key (b - a).toNat a (Int.le_refl _) (by omega) ha

/-- A Boolean trace low at `a` and high at `b > a` has a rising tick in `[a, b)`. -/
theorem rise_tick (f : Int → Bool) (a b : Int) (hab : a < b) (ha : f a = false) (hb : f b = true) :
    ∃ t, a ≤ t ∧ t < b ∧ f t = false ∧ f (t + 1) = true := by
  obtain ⟨t, h1, h2, h3, h4⟩ := fall_tick (fun x => !f x) a b hab (by simp [ha]) (by simp [hb])
  exact ⟨t, h1, h2, by simpa using h3, by simpa using h4⟩

/-- Both clients requesting, A0 low: q holds (the INIT, by `decide`). -/
theorem FS_both : ∀ q : Bool, FS true true q false = q := by decide
/-- R0 with client 2 requesting and q low: high. -/
theorem FR_r2nq : ∀ r1 : Bool, FR r1 true false = true := by decide
/-- R0 with client 1 requesting and q high: high. -/
theorem FR_r1q : ∀ r2 : Bool, FR true r2 true = true := by decide
/-- R0 with client 2 low and q low: low. -/
theorem FR_nr2nq : ∀ r1 : Bool, FR r1 false false = false := by decide
theorem FR_r1q_lo : FR true true true = true := by decide

/-! ## Direction 1: client 1 releases, client 2 waits, client 1 may re-request early

The window `[L, Hz)`; nothing is assumed before `L` except A0's last rise `a ≤ L`
(and R0 high from `a` until `L + M`). `u` is client 1's re-request (any `u > t0`,
also `u ≥ Hz`, i.e. none). -/

structure E1 (D : Dl) (M : Int) (s : Sigs) (a L t0 TA TA2 u Hz : Int) : Prop where
  ord : a ≤ L ∧ L + M ≤ t0 ∧ t0 < TA ∧ TA < TA2 ∧ TA2 < Hz ∧ t0 < u ∧ 1 ≤ M
  r1 : ∀ t, L ≤ t → t < Hz → s.r1 t = (decide (t < t0) || decide (u ≤ t))
  r2 : ∀ t, L ≤ t → t < Hz → s.r2 t = true
  A0 : ∀ t, a ≤ t → t < Hz → s.A0 t = (decide (t < TA) || decide (TA2 ≤ t))
  A0p : s.A0 (a - 1) = false
  R0a : ∀ t, a ≤ t → t < L + M → s.R0 t = true
  q0 : ∀ t, L ≤ t → t < t0 → s.q t = true
  A10 : ∀ t, L ≤ t → t < t0 → s.A1 t = true
  A20 : ∀ t, L ≤ t → t < t0 → s.A2 t = false
  g10 : ∀ t, L ≤ t → t < t0 → s.g1 t = true
  g20 : ∀ t, L ≤ t → t < t0 → s.g2 t = false

/-- **Race Q** (ustate): client 1's re-request reaches ustate no earlier than q's
reset has come back round q's own feedback pin. -/
def RQ (D : Dl) (TA u : Int) : Prop := QB D TA + D.wfb ≤ u + D.wr1s
/-- **Race R** (R0, O5 of ustate): r1's rise seen through R0's I0 rise arc no earlier
than R0's I2 sees q low through its rise arc (the fall-arc view is then implied). -/
def RRc (D : Dl) (TA u : Int) : Prop := RR D TA ≤ u + D.wr1s + D.Rr1
/-- **Race G** (g1, O5 of ugrant), one inequality per arc view (rise view, fall view). -/
def RG (D : Dl) (TA u : Int) : Prop :=
  QB D TA + D.wq + D.g1rq ≤ u + D.wr1g + D.g1r1 ∧ QB D TA + D.wq + D.g1fq ≤ u + D.wr1g + D.g1f1

/-- **H_HOLDQ** (the race race R protects): A0's re-rise reaches ustate's hold pin no
earlier than q's reset has come round q's feedback pin. -/
def HQ (D : Dl) (TA TA2 : Int) : Prop := QB D TA + D.wfb ≤ TA2 + D.wa0s

/-- C's `OpsCM.AMerge` step fields at the 1 ps tick `t → t+1`, with x = client 1
(req r1, ack A1), y = client 2 (req r2, ack A2), z = the output (req `z`, ack A0):
H_ARB1, H_ARB2 (`CArb`), `zr`, H_AMERGE_RTZ, `xa`, `ya`, verbatim shapes. -/
def CF (s : Sigs) (z : Int → Bool) (t : Int) : Prop :=
  CArb s t ∧
  (z (t + 1) ≠ z t → z (t + 1) = (s.g1 t || s.g2 t)) ∧
  (z t = false → z (t + 1) = true → s.A1 t = false ∧ s.A2 t = false) ∧
  (s.A1 (t + 1) ≠ s.A1 t → s.g1 t = s.A1 (t + 1) ∧ s.A0 t = s.A1 (t + 1)) ∧
  (s.A2 (t + 1) ≠ s.A2 t → s.g2 t = s.A2 (t + 1) ∧ s.A0 t = s.A2 (t + 1))

/-- H_ZLINE: `z_req` is R0 through the `bd_delay` line, one pure delay `dz` (rise = fall;
prjxray gives no edge split). H_DZ (`0 ≤ dz ≤ smin`) is in `Rows1`/`Rows2`. -/
def ZLine (s : Sigs) (z : Int → Bool) (dz : Int) : Prop := ∀ t, z t = s.R0 (t - dz)

/-- A2's rise instant. -/
def T2r (D : Dl) (TA TA2 : Int) : Int := max (G2 D TA + D.wg2) (TA2 + D.wa02) + D.c2r

/-- The tick rows of direction 1 in run form (each a named timing row):
* `rt1s` RT1 STRICT (old grant low one tick before the new one rises);
* `g1p` H_TICK_CAUSAL (g1 falls strictly after r1);
* `a1` H_GRANT_IN_A0_LOW (g2 rises inside A0's low phase);
* `zf`, `zrise` H_ZR (z falls after g1 fell; z rises after g2 rose);
* `rtz` the H_AMERGE_RTZ row (A1 has fallen when z re-rises; A2 is low then by H_DZ);
* `x1`, `y1` H_ACK_IN_PHASE (A1 falls strictly after g1 and A0 fell and before A0
  re-rises; A2 rises strictly after g2 and A0 rose);
* `dz` H_DZ. -/
structure Rows1 (D : Dl) (dz t0 TA TA2 : Int) : Prop where
  rt1s : G1 D t0 TA < G2 D TA
  g1p : t0 < G1 D t0 TA
  a1 : TA < G2 D TA ∧ G2 D TA ≤ TA2
  zf : G1 D t0 TA < TR D t0 + dz
  zrise : G2 D TA < RR D TA + dz
  rtz : T1 D t0 TA < RR D TA + dz
  x1 : G1 D t0 TA < T1 D t0 TA ∧ TA < T1 D t0 TA ∧ T1 D t0 TA ≤ TA2
  y1 : G2 D TA < T2r D TA TA2 ∧ TA2 < T2r D TA TA2
  dz : 0 ≤ dz ∧ dz ≤ D.smin

section dir1
variable {D : Dl} {M : Int} {s : Sigs} {a L t0 TA TA2 u Hz : Int}

theorem e_r1_hi (S : E1 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : L ≤ t) (h2 : t < t0) :
    s.r1 t = true := by
  have := S.ord; rw [S.r1 t h1 (by omega)]; simp; omega
theorem e_r1_lo (S : E1 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : t0 ≤ t) (h2 : t < u) (h3 : t < Hz) :
    s.r1 t = false := by
  have := S.ord; rw [S.r1 t (by omega) h3]; simp; omega
theorem e_r1_hi2 (S : E1 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : u ≤ t) (h3 : t < Hz) :
    s.r1 t = true := by
  have := S.ord; rw [S.r1 t (by omega) h3]; simp; omega
theorem e_A0_h1 (S : E1 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : a ≤ t) (h2 : t < TA) :
    s.A0 t = true := by
  have := S.ord; rw [S.A0 t h1 (by omega)]; simp; omega
theorem e_A0_l (S : E1 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : TA ≤ t) (h2 : t < TA2) :
    s.A0 t = false := by
  have := S.ord; rw [S.A0 t (by omega) (by omega)]; simp; omega
theorem e_A0_h2 (S : E1 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : TA2 ≤ t) (h2 : t < Hz) :
    s.A0 t = true := by
  have := S.ord; rw [S.A0 t (by omega) h2]; simp; omega

theorem e_R0_hi (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz) (t : Int)
    (h0 : a ≤ t) (h : t < TR D t0) (hz : t < Hz) : s.R0 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0; have := S.ord
  by_cases hc : t < L + M
  · exact S.R0a t h0 hc
  · unfold TR at h
    rw [R.H_R0 t, e_r1_hi S (t - D.wr1s - D.Rf1) (by omega) (by omega),
      S.r2 (t - D.wr2s - D.Rf2) (by omega) (by omega), FR_r1r2]
    simp

theorem e_TA_ge (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz) :
    TR D t0 + D.smin ≤ TA := by
  have ho := S.ord
  have := D.H_NONNEG
  have e1 : s.A0 TA = false := e_A0_l S TA (by omega) (by omega)
  have e0 : s.A0 (TA - 1) = true := e_A0_h1 S _ (by omega) (by omega)
  obtain ⟨v, hv, hR, hc⟩ := R.H_SRV TA (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hv1 : a ≤ v := by
    by_cases hc' : a ≤ v
    · exact hc'
    · have := hc (a - 1) (by omega) (by omega)
      rw [S.A0p, e0] at this; exact absurd this (by simp)
  by_cases hd : TR D t0 + D.smin ≤ TA
  · exact hd
  · have := e_R0_hi R hM S v hv1 (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

theorem e_q_hi (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz) :
    ∀ t, L ≤ t → t < QB D TA → s.q t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q
  refine int_ind_w (fun t => t < QB D TA → s.q t = true) L t0
    (fun t h1 h2 _ => S.q0 t h1 h2) ?_
  intro t ht ih hb
  unfold QB at hb
  rw [R.H_q t, e_A0_h1 S (t - D.wa0s - D.qf) (by omega) (by omega), FS_hold,
    ih (t - D.wfb - D.qf) (by omega) (by omega) (by unfold QB; omega)]
  simp

theorem e_R0_lo (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz) (hR : RRc D TA u)
    (t : Int) (h1 : TR D t0 ≤ t) (h2 : t < RR D TA) (hz : t < Hz) : s.R0 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0; have := S.ord
  unfold TR at h1; unfold RRc RR at hR; unfold RR at h2
  rw [R.H_R0 t, e_r1_lo S (t - D.wr1s - D.Rr1) (by omega) (by omega) (by omega),
    e_r1_lo S (t - D.wr1s - D.Rf1) (by omega) (by omega) (by omega),
    e_q_hi R hM S (t - D.wfb - D.Rrq) (by omega) (by omega),
    e_q_hi R hM S (t - D.wfb - D.Rfq) (by omega) (by omega), FR_lo, FR_lo]
  simp

theorem e_TA2_ge (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz) (hR : RRc D TA u) :
    RR D TA + D.smin ≤ TA2 := by
  have ho := S.ord
  have := D.H_NONNEG
  have hTA := e_TA_ge R hM S
  have e1 : s.A0 TA2 = true := e_A0_h2 S TA2 (by omega) (by omega)
  have e0 : s.A0 (TA2 - 1) = false := e_A0_l S _ (by omega) (by omega)
  obtain ⟨v, hv, hR0, hc⟩ := R.H_SRV TA2 (by rw [e1, e0]; simp)
  rw [e1] at hR0
  have hv1 : TA ≤ v := by
    by_cases hc' : TA ≤ v
    · exact hc'
    · have := hc (TA - 1) (by omega) (by omega)
      rw [e_A0_h1 S (TA - 1) (by omega) (by omega), e0] at this; exact absurd this (by simp)
  by_cases hd : RR D TA + D.smin ≤ TA2
  · exact hd
  · unfold TR at hTA
    have := e_R0_lo R hM S hR v (by unfold TR; omega) (by omega) (by omega)
    rw [hR0] at this; exact absurd this (by simp)

theorem e_q_lo (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) :
    ∀ t, QB D TA ≤ t → t < Hz → s.q t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q
  have hTA := e_TA_ge R hM S
  have hTA2 := hH
  unfold TR at hTA; unfold HQ QB at hTA2; unfold RQ QB at hQ
  refine int_ind_w (fun t => t < Hz → s.q t = false) (QB D TA) (QB D TA)
    (fun t h1 h2 _ => absurd h2 (by omega)) ?_
  intro t ht ih hz
  unfold QB at ht
  have view : ∀ d, D.qr ≤ d → d ≤ D.qf →
      FS (s.r1 (t - D.wr1s - d)) (s.r2 (t - D.wr2s - d)) (s.q (t - D.wfb - d))
        (s.A0 (t - D.wa0s - d)) = false := by
    intro d hd1 hd2
    rw [S.r2 _ (by omega) (by omega)]
    by_cases hc : t - D.wa0s - d < TA2
    · rw [e_A0_l S _ (by omega) hc]
      by_cases hu : t - D.wr1s - d < u
      · rw [e_r1_lo S _ (by omega) hu (by omega), FS_rel]
      · rw [e_r1_hi2 S _ (by omega) (by omega), FS_both]
        exact ih _ (by unfold QB; omega) (by omega) (by omega)
    · rw [e_A0_h2 S _ (by omega) (by omega), FS_hold]
      exact ih _ (by unfold QB; omega) (by omega) (by omega)
  rw [R.H_q t, view D.qr (by omega) (by omega), view D.qf (by omega) (by omega)]
  rfl

theorem e_q_eq (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (t : Int) (h1 : L ≤ t) (hz : t < Hz) :
    s.q t = decide (t < QB D TA) := by
  by_cases h : t < QB D TA
  · rw [e_q_hi R hM S t h1 h]; simp [h]
  · rw [e_q_lo R hM S hQ hH t (by omega) hz]; simp [h]

theorem e_g2_eq (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (t : Int) (h0 : L ≤ t) (hz : t < Hz) :
    s.g2 t = decide (G2 D TA ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.g2; have := S.ord
  by_cases h1 : t < L + M
  · rw [S.g20 t h0 (by omega)]; symm; rw [decide_eq_false_iff_not]; unfold G2 QB; omega
  rw [R.H_g2 t, FG2_eq, FG2_eq, S.r2 _ (by omega) (by omega), S.r2 _ (by omega) (by omega),
    e_q_eq R hM S hQ hH _ (by omega) (by omega),
    e_q_eq R hM S hQ hH (t - D.wq - D.g2f) (by omega) (by omega)]
  unfold G2
  by_cases h : QB D TA + D.wq + D.g2r ≤ t
  · have : ¬ (t - D.wq - D.g2r < QB D TA) := by omega
    simp [h, this]
  · have e1 : t - D.wq - D.g2r < QB D TA := by omega
    have e2 : t - D.wq - D.g2f < QB D TA := by omega
    simp [h, e1, e2]

theorem e_g1_eq (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (hG : RG D TA u) (t : Int) (h0 : L ≤ t) (hz : t < Hz) :
    s.g1 t = decide (t < G1 D t0 TA) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.g1; have := S.ord
  by_cases h1 : t < L + M
  · rw [S.g10 t h0 (by omega)]; symm; rw [decide_eq_true_eq]; unfold G1 QB; omega
  unfold RG at hG
  rw [R.H_g1 t, FG1_eq, FG1_eq]
  by_cases h : t < G1 D t0 TA
  · have hh := h
    unfold G1 at h
    rw [e_r1_hi S (t - D.wr1g - D.g1f1) (by omega) (by omega),
      e_q_eq R hM S hQ hH (t - D.wq - D.g1fq) (by omega) (by omega)]
    have e2 : t - D.wq - D.g1fq < QB D TA := by omega
    simp [hh, e2]
  · have view : ∀ d1 dq, 0 ≤ d1 → d1 ≤ D.g1f1 → 0 ≤ dq → dq ≤ D.g1fq →
        QB D TA + D.wq + dq ≤ u + D.wr1g + d1 →
        (s.r1 (t - D.wr1g - d1) && s.q (t - D.wq - dq)) = false := by
      intro d1 dq h1 h2 h3 h4 h5
      rw [e_q_eq R hM S hQ hH (t - D.wq - dq) (by omega) (by omega)]
      by_cases hq : t - D.wq - dq < QB D TA
      · have hg : t0 + D.wr1g + D.g1f1 ≤ t := by unfold G1 at h; omega
        rw [e_r1_lo S _ (by omega) (by omega) (by omega)]; simp
      · simp [hq]
    rw [view _ _ (by omega) (by omega) (by omega) (by omega) hG.1,
      view _ _ (by omega) (Int.le_refl _) (by omega) (Int.le_refl _) hG.2]
    simp [h]

theorem e_R0_after (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (t : Int) (h1 : RR D TA ≤ t) (hz : t < Hz) :
    s.R0 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0; have := S.ord
  unfold RR at h1
  rw [R.H_R0 t, S.r2 (t - D.wr2s - D.Rr2) (by unfold QB at h1; omega) (by omega),
    e_q_lo R hM S hQ hH (t - D.wfb - D.Rrq) (by omega) (by omega), FR_r2nq]
  simp

/-- R0's exact trace on the window. -/
theorem e_R0_eq (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hRR : RRc D TA u) (t : Int) (h0 : a ≤ t) (hz : t < Hz) :
    s.R0 t = (decide (t < TR D t0) || decide (RR D TA ≤ t)) := by
  have hH : HQ D TA TA2 := by
    have h9 := e_TA2_ge R hM S hRR; have := D.H_NONNEG; unfold HQ; unfold RR at h9; omega
  by_cases h1 : t < TR D t0
  · rw [e_R0_hi R hM S t h0 h1 hz]; simp [h1]
  · by_cases h2 : RR D TA ≤ t
    · rw [e_R0_after R hM S hQ hH t h2 hz]; simp [h2]
    · rw [e_R0_lo R hM S hRR t (by omega) (by omega) hz]; simp [h1, h2]

/-- A1 is high before `T1`. -/
theorem e_A1_hi (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (hG : RG D TA u) :
    ∀ t, L ≤ t → t < T1 D t0 TA → t < Hz → s.A1 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A1
  refine int_ind_w (fun t => t < T1 D t0 TA → t < Hz → s.A1 t = true) L t0
    (fun t h1 h2 _ _ => S.A10 t h1 h2) ?_
  intro t ht ih hb hz
  unfold T1 at hb
  rw [R.H_A1 t, CE_eq, CE_eq,
    ih (t - D.wfa1 - D.c1f) (by omega) (by omega) (by unfold T1; omega) (by omega)]
  simp only [Bool.and_true, Bool.or_eq_true]
  right
  by_cases hg : t - D.wg1 - D.c1f < G1 D t0 TA
  · rw [e_g1_eq R hM S hQ hH hG _ (by omega) (by omega)]; simp [hg]
  · rw [e_A0_h1 S _ (by omega) (by omega)]; simp

/-- **A1 falls at `T1` and stays low** (RT2a in run form: A1's fall has come round its
own loop before A0's re-rise reaches ua1). -/
theorem e_A1_lo (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (hG : RG D TA u)
    (H_RT2a : T1 D t0 TA + D.wfa1 ≤ TA2 + D.wa01) :
    ∀ t, T1 D t0 TA ≤ t → t < Hz → s.A1 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A1
  refine int_ind_w (fun t => t < Hz → s.A1 t = false) (T1 D t0 TA) (T1 D t0 TA)
    (fun t h1 h2 _ => absurd h2 (by omega)) ?_
  intro t hb ih hz
  unfold T1 at hb H_RT2a
  have view : ∀ d, D.c1r ≤ d → d ≤ D.c1f →
      CE (s.g1 (t - D.wg1 - d)) (s.A0 (t - D.wa01 - d)) (s.A1 (t - D.wfa1 - d)) = false := by
    intro d hd1 hd2
    rw [e_g1_eq R hM S hQ hH hG _ (by omega) (by omega), CE_eq]
    have : ¬ (t - D.wg1 - d < G1 D t0 TA) := by omega
    simp only [this, decide_false, Bool.false_and, Bool.false_or]
    by_cases hc : t - D.wa01 - d < TA2
    · rw [e_A0_l S _ (by omega) hc]; simp
    · rw [ih _ (by unfold T1; omega) (by omega) (by omega)]; simp
  rw [R.H_A1 t, view D.c1r (by omega) (by omega), view D.c1f (by omega) (by omega)]
  rfl

theorem T2r_cases (D : Dl) (TA TA2 : Int) :
    G2 D TA + D.wg2 + D.c2r ≤ T2r D TA TA2 ∧ TA2 + D.wa02 + D.c2r ≤ T2r D TA TA2 ∧
    (T2r D TA TA2 = G2 D TA + D.wg2 + D.c2r ∨ T2r D TA TA2 = TA2 + D.wa02 + D.c2r) := by
  unfold T2r; omega

/-- **A2's exact trace** (given 7g's fork condition, run form). -/
theorem e_A2_eq (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (H_A0_FORK : TA + D.wa02 ≤ G2 D TA + D.wg2) :
    ∀ t, L ≤ t → t < Hz → s.A2 t = decide (T2r D TA TA2 ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A2
  have hTA := e_TA_ge R hM S
  have hc := T2r_cases D TA TA2
  have hG2 : t0 < G2 D TA := by unfold G2 QB; unfold TR at hTA; omega
  unfold TR at hTA
  refine int_ind_w (fun t => t < Hz → s.A2 t = decide (T2r D TA TA2 ≤ t)) L t0
    (fun t h1 h2 _ => by
      rw [S.A20 t h1 h2]; simp; omega) ?_
  intro t ht ih hz
  by_cases hT : T2r D TA TA2 ≤ t
  · rw [R.H_A2 t, CE_eq, e_g2_eq R hM S hQ hH _ (by omega) (by omega),
      e_A0_h2 S _ (by omega) (by omega)]
    have : G2 D TA ≤ t - D.wg2 - D.c2r := by omega
    simp [this, hT]
  · have view : ∀ d, D.c2r ≤ d → d ≤ D.c2f →
        CE (s.g2 (t - D.wg2 - d)) (s.A0 (t - D.wa02 - d)) (s.A2 (t - D.wfa2 - d)) = false := by
      intro d hd1 hd2
      rw [ih _ (by omega) (by omega) (by omega), CE_eq]
      have hf : ¬ (T2r D TA TA2 ≤ t - D.wfa2 - d) := by omega
      simp only [hf, decide_false, Bool.and_false, Bool.or_false]
      by_cases hg : G2 D TA ≤ t - D.wg2 - d
      · rw [e_g2_eq R hM S hQ hH _ (by omega) (by omega),
          e_A0_l S _ (by omega) (by omega)]
        simp
      · rw [e_g2_eq R hM S hQ hH _ (by omega) (by omega)]; simp [hg]
    rw [R.H_A2 t, view D.c2r (by omega) (by omega), view D.c2f (by omega) (by omega)]
    simp [hT]

theorem G1_cases (D : Dl) (t0 TA : Int) :
    G1 D t0 TA ≤ t0 + D.wr1g + D.g1f1 ∧ G1 D t0 TA ≤ QB D TA + D.wq + D.g1fq ∧
    (G1 D t0 TA = t0 + D.wr1g + D.g1f1 ∨ G1 D t0 TA = QB D TA + D.wq + D.g1fq) := by
  unfold G1; omega

/-- **Grant exclusion with early re-request** (client 1 releasing): RT1 (7h, arc form)
and the three races Q, R, G; client 1 may re-request at ANY `u > t0` meeting them. -/
theorem e_exclusion (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (hG : RG D TA u) (H_RT1 : RT1 D) :
    ∀ t, L ≤ t → t < Hz → (s.g1 t && s.g2 t) = false := by
  have hTA := e_TA_ge R hM S
  have hc := G1_cases D t0 TA
  have hle : G1 D t0 TA ≤ G2 D TA := by
    unfold TR at hTA; unfold RT1 at H_RT1; unfold G2 QB; unfold QB at hc; omega
  intro t h1 hz
  rw [e_g1_eq R hM S hQ hH hG t h1 hz, e_g2_eq R hM S hQ hH t h1 hz]
  by_cases h : t < G1 D t0 TA
  · have : ¬ (G2 D TA ≤ t) := by omega
    simp [this]
  · simp [h]


theorem e_HQ (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz) (hR : RRc D TA u) :
    HQ D TA TA2 := by
  have h9 := e_TA2_ge R hM S hR; have := D.H_NONNEG; unfold HQ; unfold RR at h9; omega

theorem e_A1_eq (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (hG : RG D TA u)
    (H_RT2a : T1 D t0 TA + D.wfa1 ≤ TA2 + D.wa01) (t : Int) (h0 : L ≤ t) (hz : t < Hz) :
    s.A1 t = decide (t < T1 D t0 TA) := by
  by_cases h : t < T1 D t0 TA
  · rw [e_A1_hi R hM S hQ hH hG t h0 h hz]; simp [h]
  · rw [e_A1_lo R hM S hQ hH hG H_RT2a t (by omega) hz]; simp [h]

/-- **C's step fields on the window, direction 1, early re-request allowed.**
Assumed: the gate model, H_M, the window `E1`, races Q, R, G, RT2a and the A0 fork
(run form), the four-phase client 1 (`T1 < u`: re-request only after A1 fell), the z line,
and the tick rows `Rows1`. Proved: H_ARB1, H_ARB2, zr, H_AMERGE_RTZ, xa, ya at every tick
of `[L + M + dz, Hz - 1)`. -/
theorem e_fields (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hR : RRc D TA u) (hG : RG D TA u)
    (H_RT2a : T1 D t0 TA + D.wfa1 ≤ TA2 + D.wa01) (H_A0_FORK : TA + D.wa02 ≤ G2 D TA + D.wg2)
    (hC : T1 D t0 TA < u) {z : Int → Bool} {dz : Int} (Z : ZLine s z dz) (K : Rows1 D dz t0 TA TA2) :
    ∀ t, L + M + dz ≤ t → t + 1 < Hz → CF s z t := by
  have hH := e_HQ R hM S hR
  have := S.ord; have := K.dz; have := K.rt1s; have := K.g1p; have := K.a1; have := K.zf
  have := K.zrise; have := K.rtz; have := K.x1; have := K.y1
  have hTA := e_TA_ge R hM S
  have hTA2 := e_TA2_ge R hM S hR
  have hT2 : TR D t0 < RR D TA := by
    unfold RR QB; have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS; omega
  intro t h1 h2
  have g1t := e_g1_eq R hM S hQ hH hG t (by omega) (by omega)
  have g1u := e_g1_eq R hM S hQ hH hG (t + 1) (by omega) (by omega)
  have g2t := e_g2_eq R hM S hQ hH t (by omega) (by omega)
  have g2u := e_g2_eq R hM S hQ hH (t + 1) (by omega) (by omega)
  have a1t := e_A1_eq R hM S hQ hH hG H_RT2a t (by omega) (by omega)
  have a1u := e_A1_eq R hM S hQ hH hG H_RT2a (t + 1) (by omega) (by omega)
  have a2t := e_A2_eq R hM S hQ hH H_A0_FORK t (by omega) (by omega)
  have a2u := e_A2_eq R hM S hQ hH H_A0_FORK (t + 1) (by omega) (by omega)
  have zt := Z t
  have zu := Z (t + 1)
  rw [e_R0_eq R hM S hQ hR (t - dz) (by omega) (by omega)] at zt
  rw [e_R0_eq R hM S hQ hR (t + 1 - dz) (by omega) (by omega)] at zu
  have r1t := S.r1 t (by omega) (by omega)
  have r2t := S.r2 t (by omega) (by omega)
  have a0t := S.A0 t (by omega) (by omega)
  unfold CF CArb
  rw [g1t, g1u, g2t, g2u, a1t, a1u, a2t, a2u, zt, zu, r1t, r2t, a0t]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ne_eq, ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq,
      decide_eq_false_iff_not] <;> omega


/-! ### Counter-runs at slack −1 (direction 1)

Each lemma takes every hypothesis of the window except one race, which it violates by
exactly 1 ps, and derives a violation of one of C's fields on EVERY such run. -/

/-- **Race Q at slack −1 ⇒ C's H_ARB2 fails**: q's reset is undone (a low runt on q),
g2 rises and falls again while r2 stays high. Side conditions: ustate's fast loop is at
least 2 ps (`qr + wfb ≥ 2`) and g2's arcs are equal (one consistent corner). -/
theorem cex_Q (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz) (hH : HQ D TA TA2)
    (hslack : u + D.wr1s + 1 = QB D TA + D.wfb) (h2 : 2 ≤ D.qr + D.wfb) (hg : D.g2r = D.g2f)
    (hz : QB D TA + D.wfb + D.qr + D.wq + D.g2r < Hz) :
    ∃ t, L ≤ t ∧ t < Hz ∧ s.g2 t = true ∧ s.g2 (t + 1) = false ∧ s.r2 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q; have := hM.g2
  have hTA := e_TA_ge R hM S
  unfold TR at hTA; unfold HQ QB at hH; unfold QB at hslack hz
  have qQB : s.q (QB D TA) = false := by
    unfold QB
    rw [R.H_q]
    have view : ∀ d, D.qr ≤ d → d ≤ D.qf →
        FS (s.r1 (TA + D.wa0s + D.qf - D.wr1s - d)) (s.r2 (TA + D.wa0s + D.qf - D.wr2s - d))
          (s.q (TA + D.wa0s + D.qf - D.wfb - d)) (s.A0 (TA + D.wa0s + D.qf - D.wa0s - d)) = false := by
      intro d h1 h2
      rw [e_r1_lo S _ (by omega) (by omega) (by omega), S.r2 _ (by omega) (by omega),
        e_A0_l S _ (by omega) (by omega), FS_rel]
    rw [view D.qr (by omega) (by omega), view D.qf (by omega) (by omega)]; rfl
  have qt1 : s.q (u + D.wr1s + D.qr) = true := by
    rw [R.H_q, e_r1_hi2 S (u + D.wr1s + D.qr - D.wr1s - D.qr) (by omega) (by omega),
      S.r2 _ (by omega) (by omega), e_A0_l S _ (by omega) (by omega), FS_both,
      e_q_hi R hM S _ (by omega) (by unfold QB; omega)]
    simp
  have ga : s.g2 (QB D TA + D.wq + D.g2r) = true := by
    rw [R.H_g2, FG2_eq, S.r2 _ (by unfold QB; omega) (by unfold QB; omega),
      show QB D TA + D.wq + D.g2r - D.wq - D.g2r = QB D TA by omega, qQB]
    simp
  have gb : s.g2 (u + D.wr1s + D.qr + D.wq + D.g2r) = false := by
    rw [R.H_g2, FG2_eq, FG2_eq, S.r2 _ (by omega) (by omega), S.r2 _ (by omega) (by omega),
      show u + D.wr1s + D.qr + D.wq + D.g2r - D.wq - D.g2r = u + D.wr1s + D.qr by omega,
      show u + D.wr1s + D.qr + D.wq + D.g2r - D.wq - D.g2f = u + D.wr1s + D.qr by omega, qt1]
    simp
  obtain ⟨t, h1, h3, h4, h5⟩ := fall_tick s.g2 _ _ (by unfold QB; omega) ga gb
  exact ⟨t, by unfold QB at h1; omega, by omega, h4, h5,
    S.r2 t (by unfold QB at h1; omega) (by omega)⟩

/-- **Race G at slack −1 (either arc view) ⇒ C's H_ARB1 fails**: g1 re-rises after q has
flipped and falls again while r1 stays high. -/
theorem cex_G (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (d1 dq : Int)
    (hv : (d1 = D.g1r1 ∧ dq = D.g1rq) ∨ (d1 = D.g1f1 ∧ dq = D.g1fq))
    (hslack : u + D.wr1g + d1 + 1 = QB D TA + D.wq + dq) (hz : QB D TA + D.wq + D.g1fq < Hz) :
    ∃ t, L ≤ t ∧ t < Hz ∧ s.g1 t = true ∧ s.g1 (t + 1) = false ∧ s.r1 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q; have := hM.g1
  have hTA := e_TA_ge R hM S
  unfold TR at hTA
  have hQB : t0 < QB D TA := by unfold QB; omega
  have ga : s.g1 (u + D.wr1g + d1) = true := by
    rw [R.H_g1, FG1_eq, FG1_eq]
    rcases hv with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · subst e1; subst e2
      rw [e_r1_hi2 S (u + D.wr1g + D.g1r1 - D.wr1g - D.g1r1) (by omega) (by omega),
        e_q_hi R hM S _ (by omega) (by omega)]
      simp
    · subst e1; subst e2
      rw [e_r1_hi2 S (u + D.wr1g + D.g1f1 - D.wr1g - D.g1f1) (by omega) (by omega),
        e_q_hi R hM S (u + D.wr1g + D.g1f1 - D.wq - D.g1fq) (by omega) (by omega)]
      simp
  have gb : s.g1 (QB D TA + D.wq + D.g1fq) = false := by
    rw [R.H_g1, FG1_eq, FG1_eq,
      e_q_lo R hM S hQ hH (QB D TA + D.wq + D.g1fq - D.wq - D.g1rq) (by omega) (by omega),
      e_q_lo R hM S hQ hH (QB D TA + D.wq + D.g1fq - D.wq - D.g1fq) (by omega) (by omega)]
    simp
  have hlt : u + D.wr1g + d1 < QB D TA + D.wq + D.g1fq := by rcases hv with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  obtain ⟨t, h1, h3, h4, h5⟩ := fall_tick s.g1 _ _ hlt ga gb
  have hd : 0 ≤ d1 := by rcases hv with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  exact ⟨t, by omega, by omega, h4, h5, e_r1_hi2 S t (by omega) (by omega)⟩

/-- **Race R at slack −1 ⇒ C's `zr` fails** when the z-rise row is tight (`G2 + 1 = RR + dz`,
slack 0): R0, hence z, rises one tick early (r1 seen with the stale q), while neither
grant is high yet. Side condition: `smin + wa0s + qf + wfb + Rrq ≥ 2`. -/
theorem cex_R (R : Run D s) (hM : MB D M) (S : E1 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ D TA u) (hH : HQ D TA TA2) (hG : RG D TA u)
    (hslack : u + D.wr1s + D.Rr1 + 1 = RR D TA) (h2 : 2 ≤ D.smin + D.wa0s + D.qf + D.wfb + D.Rrq)
    {z : Int → Bool} {dz : Int} (Z : ZLine s z dz) (hdz : 0 ≤ dz)
    (htight : G2 D TA + 1 = RR D TA + dz) (hG1 : G1 D t0 TA + 2 ≤ RR D TA + dz)
    (hz : RR D TA + dz < Hz) :
    ∃ t, L + M ≤ t ∧ t < Hz ∧ z t = false ∧ z (t + 1) = true ∧ (s.g1 t || s.g2 t) = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q; have := hM.R0
  have hTA := e_TA_ge R hM S
  unfold TR at hTA; unfold RR at hslack htight hG1 hz; unfold QB at hslack htight hG1 hz
  have hu : s.R0 (RR D TA - 1) = true := by
    unfold RR QB
    rw [R.H_R0, e_r1_hi2 S _ (by omega) (by omega), S.r2 _ (by omega) (by omega), FR_r1r2]
    simp
  have hl : s.R0 (RR D TA - 2) = false := by
    unfold RR QB
    rw [R.H_R0, e_r1_lo S _ (by omega) (by omega) (by omega),
      e_r1_lo S (TA + D.wa0s + D.qf + D.wfb + D.Rrq - 2 - D.wr1s - D.Rf1) (by omega) (by omega)
        (by omega),
      S.r2 _ (by omega) (by omega), S.r2 _ (by omega) (by omega),
      e_q_hi R hM S _ (by omega) (by unfold QB; omega),
      e_q_hi R hM S (TA + D.wa0s + D.qf + D.wfb + D.Rrq - 2 - D.wfb - D.Rfq) (by omega)
        (by unfold QB; omega), FR_lo]
    rfl
  refine ⟨RR D TA + dz - 2, by unfold RR QB; omega, by unfold RR QB; omega, ?_, ?_, ?_⟩
  · rw [Z, show RR D TA + dz - 2 - dz = RR D TA - 2 by omega, hl]
  · rw [Z, show RR D TA + dz - 2 + 1 - dz = RR D TA - 1 by omega, hu]
  · rw [e_g1_eq R hM S hQ hH hG _ (by unfold RR QB; omega) (by unfold RR QB; omega),
      e_g2_eq R hM S hQ hH _ (by unfold RR QB; omega) (by unfold RR QB; omega)]
    have : ¬ (RR D TA + dz - 2 < G1 D t0 TA) := by unfold RR QB; omega
    have : ¬ (G2 D TA ≤ RR D TA + dz - 2) := by unfold RR QB; omega
    simp [*]

/-! ### Arc form of the races (four-phase client 1 at zero reaction time)

C's `SendStep` for client 1 says r1 rises at `u` only if A1 was low at `u - 1`; with
A1's exact trace (`e_A1_eq`) that is `T1 < u`. Since `T1 ≥ TA + wa01 + c1f` and
`QB = TA + wa0s + qf`, the races follow from A0-fork-type arc inequalities. -/
structure Arc1 (D : Dl) : Prop where
  q : D.wa0s + D.qf + D.wfb ≤ D.wa01 + D.c1f + 1 + D.wr1s
  r : D.wa0s + D.qf + D.wfb + D.Rrq ≤ D.wa01 + D.c1f + 1 + D.wr1s + D.Rr1
  gr : D.wa0s + D.qf + D.wq + D.g1rq ≤ D.wa01 + D.c1f + 1 + D.wr1g + D.g1r1
  gf : D.wa0s + D.qf + D.wq + D.g1fq ≤ D.wa01 + D.c1f + 1 + D.wr1g + D.g1f1

theorem races_of_arc1 (D : Dl) (t0 TA u : Int) (hC : T1 D t0 TA < u) (hA : Arc1 D) :
    RQ D TA u ∧ RRc D TA u ∧ RG D TA u := by
  have := Int.le_max_right (G1 D t0 TA + D.wg1) (TA + D.wa01)
  have hT : TA + D.wa01 + D.c1f ≤ T1 D t0 TA := by unfold T1; omega
  obtain ⟨h1, h2, h3, h4⟩ := hA
  unfold RQ RRc RG RR QB; omega

end dir1

/-! ## Direction 2 (mirror): client 2 releases, client 1 waits, client 2 may re-request early

q RISES here (7j's instants `TRb`, `QBb`, `RRb`, `G1b`, `G2b`, `T1b`). -/

structure E2 (D : Dl) (M : Int) (s : Sigs) (a L t0 TA TA2 u Hz : Int) : Prop where
  ord : a ≤ L ∧ L + M ≤ t0 ∧ t0 < TA ∧ TA < TA2 ∧ TA2 < Hz ∧ t0 < u ∧ 1 ≤ M
  r1 : ∀ t, L ≤ t → t < Hz → s.r1 t = true
  r2 : ∀ t, L ≤ t → t < Hz → s.r2 t = (decide (t < t0) || decide (u ≤ t))
  A0 : ∀ t, a ≤ t → t < Hz → s.A0 t = (decide (t < TA) || decide (TA2 ≤ t))
  A0p : s.A0 (a - 1) = false
  R0a : ∀ t, a ≤ t → t < L + M → s.R0 t = true
  q0 : ∀ t, L ≤ t → t < t0 → s.q t = false
  A10 : ∀ t, L ≤ t → t < t0 → s.A1 t = false
  A20 : ∀ t, L ≤ t → t < t0 → s.A2 t = true
  g10 : ∀ t, L ≤ t → t < t0 → s.g1 t = false
  g20 : ∀ t, L ≤ t → t < t0 → s.g2 t = true

/-- Race Q, mirror: client 2's re-request reaches ustate after q's set came round. -/
def RQ2 (D : Dl) (TA u : Int) : Prop := QBb D TA + D.wfb ≤ u + D.wr2s
/-- Race R, mirror. -/
def RRc2 (D : Dl) (TA u : Int) : Prop := RRb D TA ≤ u + D.wr2s + D.Rr2
/-- Race G, mirror (O6 arcs are flat, so one inequality). -/
def RG2 (D : Dl) (TA u : Int) : Prop := QBb D TA + D.wq ≤ u + D.wr2g
/-- H_HOLDQ, mirror. -/
def HQ2 (D : Dl) (TA TA2 : Int) : Prop := QBb D TA + D.wfb ≤ TA2 + D.wa0s
/-- A1's rise instant (mirror of `T2r`). -/
def T2rb (D : Dl) (TA TA2 : Int) : Int := max (G1b D TA + D.wg1) (TA2 + D.wa01) + D.c1r

structure Rows2 (D : Dl) (dz t0 TA TA2 : Int) : Prop where
  rt1s : G2b D t0 TA < G1b D TA
  g2p : t0 < G2b D t0 TA
  a1 : TA < G1b D TA ∧ G1b D TA ≤ TA2
  zf : G2b D t0 TA < TRb D t0 + dz
  zrise : G1b D TA < RRb D TA + dz
  rtz : T1b D t0 TA < RRb D TA + dz
  x1 : G1b D TA < T2rb D TA TA2 ∧ TA2 < T2rb D TA TA2
  y1 : G2b D t0 TA < T1b D t0 TA ∧ TA < T1b D t0 TA ∧ T1b D t0 TA ≤ TA2
  dz : 0 ≤ dz ∧ dz ≤ D.smin

theorem T2rb_cases (D : Dl) (TA TA2 : Int) :
    G1b D TA + D.wg1 + D.c1r ≤ T2rb D TA TA2 ∧ TA2 + D.wa01 + D.c1r ≤ T2rb D TA TA2 ∧
    (T2rb D TA TA2 = G1b D TA + D.wg1 + D.c1r ∨ T2rb D TA TA2 = TA2 + D.wa01 + D.c1r) := by
  unfold T2rb; omega

theorem G2b_cases (D : Dl) (t0 TA : Int) :
    G2b D t0 TA ≤ t0 + D.wr2g + D.g2f ∧ G2b D t0 TA ≤ QBb D TA + D.wq + D.g2f ∧
    (G2b D t0 TA = t0 + D.wr2g + D.g2f ∨ G2b D t0 TA = QBb D TA + D.wq + D.g2f) := by
  unfold G2b; omega

section dir2
variable {D : Dl} {M : Int} {s : Sigs} {a L t0 TA TA2 u Hz : Int}

theorem f_r2_hi (S : E2 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : L ≤ t) (h2 : t < t0) :
    s.r2 t = true := by
  have := S.ord; rw [S.r2 t h1 (by omega)]; simp; omega
theorem f_r2_lo (S : E2 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : t0 ≤ t) (h2 : t < u) (h3 : t < Hz) :
    s.r2 t = false := by
  have := S.ord; rw [S.r2 t (by omega) h3]; simp; omega
theorem f_r2_hi2 (S : E2 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : u ≤ t) (h3 : t < Hz) :
    s.r2 t = true := by
  have := S.ord; rw [S.r2 t (by omega) h3]; simp; omega
theorem f_A0_h1 (S : E2 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : a ≤ t) (h2 : t < TA) :
    s.A0 t = true := by
  have := S.ord; rw [S.A0 t h1 (by omega)]; simp; omega
theorem f_A0_l (S : E2 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : TA ≤ t) (h2 : t < TA2) :
    s.A0 t = false := by
  have := S.ord; rw [S.A0 t (by omega) (by omega)]; simp; omega
theorem f_A0_h2 (S : E2 D M s a L t0 TA TA2 u Hz) (t : Int) (h1 : TA2 ≤ t) (h2 : t < Hz) :
    s.A0 t = true := by
  have := S.ord; rw [S.A0 t (by omega) h2]; simp; omega

theorem f_R0_hi (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz) (t : Int)
    (h0 : a ≤ t) (h : t < TRb D t0) (hz : t < Hz) : s.R0 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0; have := S.ord
  by_cases hc : t < L + M
  · exact S.R0a t h0 hc
  · unfold TRb at h
    rw [R.H_R0 t, S.r1 (t - D.wr1s - D.Rf1) (by omega) (by omega),
      f_r2_hi S (t - D.wr2s - D.Rf2) (by omega) (by omega), FR_r1]
    simp

theorem f_TA_ge (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz) :
    TRb D t0 + D.smin ≤ TA := by
  have ho := S.ord
  have := D.H_NONNEG
  have e1 : s.A0 TA = false := f_A0_l S TA (by omega) (by omega)
  have e0 : s.A0 (TA - 1) = true := f_A0_h1 S _ (by omega) (by omega)
  obtain ⟨v, hv, hR, hc⟩ := R.H_SRV TA (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hv1 : a ≤ v := by
    by_cases hc' : a ≤ v
    · exact hc'
    · have := hc (a - 1) (by omega) (by omega)
      rw [S.A0p, e0] at this; exact absurd this (by simp)
  by_cases hd : TRb D t0 + D.smin ≤ TA
  · exact hd
  · have := f_R0_hi R hM S v hv1 (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

theorem f_q_lo (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz) :
    ∀ t, L ≤ t → t < QBb D TA → s.q t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q
  refine int_ind_w (fun t => t < QBb D TA → s.q t = false) L t0
    (fun t h1 h2 _ => S.q0 t h1 h2) ?_
  intro t ht ih hb
  unfold QBb at hb
  rw [R.H_q t, f_A0_h1 S (t - D.wa0s - D.qf) (by omega) (by omega),
    f_A0_h1 S (t - D.wa0s - D.qr) (by omega) (by omega), FS_hold, FS_hold,
    ih (t - D.wfb - D.qf) (by omega) (by omega) (by unfold QBb; omega),
    ih (t - D.wfb - D.qr) (by omega) (by omega) (by unfold QBb; omega)]
  rfl

theorem f_R0_lo (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz) (hR : RRc2 D TA u)
    (t : Int) (h1 : TRb D t0 ≤ t) (h2 : t < RRb D TA) (hz : t < Hz) : s.R0 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0; have := S.ord
  unfold TRb at h1; unfold RRc2 RRb at hR; unfold RRb at h2
  rw [R.H_R0 t, S.r1 (t - D.wr1s - D.Rr1) (by omega) (by omega),
    S.r1 (t - D.wr1s - D.Rf1) (by omega) (by omega),
    f_r2_lo S (t - D.wr2s - D.Rr2) (by omega) (by omega) (by omega),
    f_r2_lo S (t - D.wr2s - D.Rf2) (by omega) (by omega) (by omega),
    f_q_lo R hM S (t - D.wfb - D.Rrq) (by omega) (by omega),
    f_q_lo R hM S (t - D.wfb - D.Rfq) (by omega) (by omega), FR_r1]
  rfl

theorem f_TA2_ge (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz) (hR : RRc2 D TA u) :
    RRb D TA + D.smin ≤ TA2 := by
  have ho := S.ord
  have := D.H_NONNEG
  have hTA := f_TA_ge R hM S
  have e1 : s.A0 TA2 = true := f_A0_h2 S TA2 (by omega) (by omega)
  have e0 : s.A0 (TA2 - 1) = false := f_A0_l S _ (by omega) (by omega)
  obtain ⟨v, hv, hR0, hc⟩ := R.H_SRV TA2 (by rw [e1, e0]; simp)
  rw [e1] at hR0
  have hv1 : TA ≤ v := by
    by_cases hc' : TA ≤ v
    · exact hc'
    · have := hc (TA - 1) (by omega) (by omega)
      rw [f_A0_h1 S (TA - 1) (by omega) (by omega), e0] at this; exact absurd this (by simp)
  by_cases hd : RRb D TA + D.smin ≤ TA2
  · exact hd
  · unfold TRb at hTA
    have := f_R0_lo R hM S hR v (by unfold TRb; omega) (by omega) (by omega)
    rw [hR0] at this; exact absurd this (by simp)

theorem f_HQ (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz) (hR : RRc2 D TA u) :
    HQ2 D TA TA2 := by
  have h9 := f_TA2_ge R hM S hR; have := D.H_NONNEG; unfold HQ2; unfold RRb at h9; omega

theorem f_q_hi (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2) :
    ∀ t, QBb D TA ≤ t → t < Hz → s.q t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q
  have hTA := f_TA_ge R hM S
  unfold TRb at hTA; unfold HQ2 QBb at hH; unfold RQ2 QBb at hQ
  refine int_ind_w (fun t => t < Hz → s.q t = true) (QBb D TA) (QBb D TA)
    (fun t h1 h2 _ => absurd h2 (by omega)) ?_
  intro t ht ih hz
  unfold QBb at ht
  have view : FS (s.r1 (t - D.wr1s - D.qr)) (s.r2 (t - D.wr2s - D.qr)) (s.q (t - D.wfb - D.qr))
      (s.A0 (t - D.wa0s - D.qr)) = true := by
    rw [S.r1 _ (by omega) (by omega)]
    by_cases hc : t - D.wa0s - D.qr < TA2
    · rw [f_A0_l S _ (by omega) hc]
      by_cases hu : t - D.wr2s - D.qr < u
      · rw [f_r2_lo S _ (by omega) hu (by omega), FS_set]
      · rw [f_r2_hi2 S _ (by omega) (by omega), FS_both]
        exact ih _ (by unfold QBb; omega) (by omega) (by omega)
    · rw [f_A0_h2 S _ (by omega) (by omega), FS_hold]
      exact ih _ (by unfold QBb; omega) (by omega) (by omega)
  rw [R.H_q t, view]
  rfl

theorem f_q_eq (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2) (t : Int) (h1 : L ≤ t) (hz : t < Hz) :
    s.q t = decide (QBb D TA ≤ t) := by
  by_cases h : QBb D TA ≤ t
  · rw [f_q_hi R hM S hQ hH t h hz]; simp [h]
  · rw [f_q_lo R hM S t h1 (by omega)]; simp [h]

theorem f_g1_eq (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2) (t : Int) (h0 : L ≤ t) (hz : t < Hz) :
    s.g1 t = decide (G1b D TA ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.g1; have := S.ord
  have hTA := f_TA_ge R hM S
  unfold TRb at hTA
  by_cases h1 : t < L + M
  · rw [S.g10 t h0 (by omega)]; symm; rw [decide_eq_false_iff_not]; unfold G1b QBb; omega
  rw [R.H_g1 t, S.r1 _ (by omega) (by omega), S.r1 (t - D.wr1g - D.g1f1) (by omega) (by omega),
    FG1_r1, FG1_r1, f_q_eq R hM S hQ hH _ (by omega) (by omega),
    f_q_eq R hM S hQ hH (t - D.wq - D.g1fq) (by omega) (by omega)]
  unfold G1b
  by_cases h : QBb D TA + D.wq + D.g1rq ≤ t
  · have : QBb D TA ≤ t - D.wq - D.g1rq := by omega
    simp [h, this]
  · have e1 : ¬ QBb D TA ≤ t - D.wq - D.g1rq := by omega
    have e2 : ¬ QBb D TA ≤ t - D.wq - D.g1fq := by omega
    simp [h, e1, e2]

theorem f_g2_eq (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2) (hG : RG2 D TA u) (t : Int) (h0 : L ≤ t) (hz : t < Hz) :
    s.g2 t = decide (t < G2b D t0 TA) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.g2; have := S.ord
  have hTA := f_TA_ge R hM S
  have hc := G2b_cases D t0 TA
  unfold TRb at hTA; unfold RG2 at hG
  by_cases h1 : t < L + M
  · rw [S.g20 t h0 (by omega)]; symm; rw [decide_eq_true_eq]; unfold QBb at hc; omega
  rw [R.H_g2 t, FG2_eq, FG2_eq]
  by_cases h : t < G2b D t0 TA
  · rw [f_r2_hi S (t - D.wr2g - D.g2f) (by omega) (by omega),
      f_q_eq R hM S hQ hH (t - D.wq - D.g2f) (by omega) (by omega)]
    have e2 : ¬ QBb D TA ≤ t - D.wq - D.g2f := by omega
    simp [h, e2]
  · have view : ∀ d, 0 ≤ d → d ≤ D.g2f →
        (s.r2 (t - D.wr2g - d) && !s.q (t - D.wq - d)) = false := by
      intro d h1 h2
      rw [f_q_eq R hM S hQ hH (t - D.wq - d) (by omega) (by omega)]
      by_cases hq : QBb D TA ≤ t - D.wq - d
      · simp [hq]
      · rw [f_r2_lo S _ (by omega) (by omega) (by omega)]; simp
    rw [view _ (by omega) (by omega), view _ (by omega) (Int.le_refl _)]
    simp [h]

theorem f_R0_after (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2) (t : Int) (h1 : RRb D TA ≤ t) (hz : t < Hz) :
    s.R0 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := hM.R0; have := S.ord
  unfold RRb at h1
  rw [R.H_R0 t, S.r1 (t - D.wr1s - D.Rr1) (by unfold QBb at h1; omega) (by omega),
    f_q_hi R hM S hQ hH (t - D.wfb - D.Rrq) (by omega) (by omega), FR_r1q]
  simp

theorem f_R0_eq (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hRR : RRc2 D TA u) (t : Int) (h0 : a ≤ t) (hz : t < Hz) :
    s.R0 t = (decide (t < TRb D t0) || decide (RRb D TA ≤ t)) := by
  have hH := f_HQ R hM S hRR
  by_cases h1 : t < TRb D t0
  · rw [f_R0_hi R hM S t h0 h1 hz]; simp [h1]
  · by_cases h2 : RRb D TA ≤ t
    · rw [f_R0_after R hM S hQ hH t h2 hz]; simp [h2]
    · rw [f_R0_lo R hM S hRR t (by omega) (by omega) hz]; simp [h1, h2]

theorem f_A2_hi (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2) (hG : RG2 D TA u) :
    ∀ t, L ≤ t → t < T1b D t0 TA → t < Hz → s.A2 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A2
  refine int_ind_w (fun t => t < T1b D t0 TA → t < Hz → s.A2 t = true) L t0
    (fun t h1 h2 _ _ => S.A20 t h1 h2) ?_
  intro t ht ih hb hz
  unfold T1b at hb
  rw [R.H_A2 t, CE_eq, CE_eq,
    ih (t - D.wfa2 - D.c2f) (by omega) (by omega) (by unfold T1b; omega) (by omega)]
  simp only [Bool.and_true, Bool.or_eq_true]
  right
  by_cases hg : t - D.wg2 - D.c2f < G2b D t0 TA
  · rw [f_g2_eq R hM S hQ hH hG _ (by omega) (by omega)]; simp [hg]
  · rw [f_A0_h1 S _ (by omega) (by omega)]; simp

theorem f_A2_lo (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2) (hG : RG2 D TA u)
    (H_RT2a : T1b D t0 TA + D.wfa2 ≤ TA2 + D.wa02) :
    ∀ t, T1b D t0 TA ≤ t → t < Hz → s.A2 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A2
  have hc := G2b_cases D t0 TA
  refine int_ind_w (fun t => t < Hz → s.A2 t = false) (T1b D t0 TA) (T1b D t0 TA)
    (fun t h1 h2 _ => absurd h2 (by omega)) ?_
  intro t hb ih hz
  unfold T1b at hb H_RT2a
  have view : ∀ d, D.c2r ≤ d → d ≤ D.c2f →
      CE (s.g2 (t - D.wg2 - d)) (s.A0 (t - D.wa02 - d)) (s.A2 (t - D.wfa2 - d)) = false := by
    intro d hd1 hd2
    rw [f_g2_eq R hM S hQ hH hG _ (by omega) (by omega), CE_eq]
    have : ¬ (t - D.wg2 - d < G2b D t0 TA) := by omega
    simp only [this, decide_false, Bool.false_and, Bool.false_or]
    by_cases hc : t - D.wa02 - d < TA2
    · rw [f_A0_l S _ (by omega) hc]; simp
    · rw [ih _ (by unfold T1b; omega) (by omega) (by omega)]; simp
  rw [R.H_A2 t, view D.c2r (by omega) (by omega), view D.c2f (by omega) (by omega)]
  rfl

theorem f_A2_eq (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2) (hG : RG2 D TA u)
    (H_RT2a : T1b D t0 TA + D.wfa2 ≤ TA2 + D.wa02) (t : Int) (h0 : L ≤ t) (hz : t < Hz) :
    s.A2 t = decide (t < T1b D t0 TA) := by
  by_cases h : t < T1b D t0 TA
  · rw [f_A2_hi R hM S hQ hH hG t h0 h hz]; simp [h]
  · rw [f_A2_lo R hM S hQ hH hG H_RT2a t (by omega) hz]; simp [h]

theorem f_A1_eq (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2) (H_A0_FORK : TA + D.wa01 ≤ G1b D TA + D.wg1) :
    ∀ t, L ≤ t → t < Hz → s.A1 t = decide (T2rb D TA TA2 ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.A1
  have hTA := f_TA_ge R hM S
  have hc := T2rb_cases D TA TA2
  have hG1 : t0 < G1b D TA := by unfold G1b QBb; unfold TRb at hTA; omega
  unfold TRb at hTA
  refine int_ind_w (fun t => t < Hz → s.A1 t = decide (T2rb D TA TA2 ≤ t)) L t0
    (fun t h1 h2 _ => by rw [S.A10 t h1 h2]; simp; omega) ?_
  intro t ht ih hz
  by_cases hT : T2rb D TA TA2 ≤ t
  · rw [R.H_A1 t, CE_eq, f_g1_eq R hM S hQ hH _ (by omega) (by omega),
      f_A0_h2 S _ (by omega) (by omega)]
    have : G1b D TA ≤ t - D.wg1 - D.c1r := by omega
    simp [this, hT]
  · have view : ∀ d, D.c1r ≤ d → d ≤ D.c1f →
        CE (s.g1 (t - D.wg1 - d)) (s.A0 (t - D.wa01 - d)) (s.A1 (t - D.wfa1 - d)) = false := by
      intro d hd1 hd2
      rw [ih _ (by omega) (by omega) (by omega), CE_eq]
      have hf : ¬ (T2rb D TA TA2 ≤ t - D.wfa1 - d) := by omega
      simp only [hf, decide_false, Bool.and_false, Bool.or_false]
      by_cases hg : G1b D TA ≤ t - D.wg1 - d
      · rw [f_g1_eq R hM S hQ hH _ (by omega) (by omega), f_A0_l S _ (by omega) (by omega)]
        simp
      · rw [f_g1_eq R hM S hQ hH _ (by omega) (by omega)]; simp [hg]
    rw [R.H_A1 t, view D.c1r (by omega) (by omega), view D.c1f (by omega) (by omega)]
    simp [hT]

/-- **Grant exclusion with early re-request, mirror direction** (RT1b of 7j). -/
theorem f_exclusion (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hR : RRc2 D TA u) (hG : RG2 D TA u) (H_RT1 : RT1b D) :
    ∀ t, L ≤ t → t < Hz → (s.g1 t && s.g2 t) = false := by
  have hH := f_HQ R hM S hR
  have hTA := f_TA_ge R hM S
  have hc := G2b_cases D t0 TA
  have hle : G2b D t0 TA ≤ G1b D TA := by
    unfold TRb at hTA; unfold RT1b at H_RT1; unfold G1b QBb; unfold QBb at hc; omega
  intro t h1 hz
  rw [f_g1_eq R hM S hQ hH t h1 hz, f_g2_eq R hM S hQ hH hG t h1 hz]
  by_cases h : t < G2b D t0 TA
  · have : ¬ (G1b D TA ≤ t) := by omega
    simp [this]
  · simp [h]

/-- **C's step fields on the window, mirror direction.** -/
theorem f_fields (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hR : RRc2 D TA u) (hG : RG2 D TA u)
    (H_RT2a : T1b D t0 TA + D.wfa2 ≤ TA2 + D.wa02) (H_A0_FORK : TA + D.wa01 ≤ G1b D TA + D.wg1)
    (hC : T1b D t0 TA < u) {z : Int → Bool} {dz : Int} (Z : ZLine s z dz) (K : Rows2 D dz t0 TA TA2) :
    ∀ t, L + M + dz ≤ t → t + 1 < Hz → CF s z t := by
  have hH := f_HQ R hM S hR
  have := S.ord; have := K.dz; have := K.rt1s; have := K.g2p; have := K.a1; have := K.zf
  have := K.zrise; have := K.rtz; have := K.x1; have := K.y1
  have hTA := f_TA_ge R hM S
  have hTA2 := f_TA2_ge R hM S hR
  have hT2 : TRb D t0 < RRb D TA := by
    unfold RRb QBb; have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS; omega
  intro t h1 h2
  have g1t := f_g1_eq R hM S hQ hH t (by omega) (by omega)
  have g1u := f_g1_eq R hM S hQ hH (t + 1) (by omega) (by omega)
  have g2t := f_g2_eq R hM S hQ hH hG t (by omega) (by omega)
  have g2u := f_g2_eq R hM S hQ hH hG (t + 1) (by omega) (by omega)
  have a1t := f_A1_eq R hM S hQ hH H_A0_FORK t (by omega) (by omega)
  have a1u := f_A1_eq R hM S hQ hH H_A0_FORK (t + 1) (by omega) (by omega)
  have a2t := f_A2_eq R hM S hQ hH hG H_RT2a t (by omega) (by omega)
  have a2u := f_A2_eq R hM S hQ hH hG H_RT2a (t + 1) (by omega) (by omega)
  have zt := Z t
  have zu := Z (t + 1)
  rw [f_R0_eq R hM S hQ hR (t - dz) (by omega) (by omega)] at zt
  rw [f_R0_eq R hM S hQ hR (t + 1 - dz) (by omega) (by omega)] at zu
  have r1t := S.r1 t (by omega) (by omega)
  have r2t := S.r2 t (by omega) (by omega)
  have a0t := S.A0 t (by omega) (by omega)
  unfold CF CArb
  rw [g1t, g1u, g2t, g2u, a1t, a1u, a2t, a2u, zt, zu, r1t, r2t, a0t]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ne_eq, ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq,
      decide_eq_false_iff_not] <;> omega

/-! ### Counter-runs at slack −1 (mirror) -/

/-- **Race Q2 at slack −1 ⇒ C's H_ARB1 fails** (q's set undone; g1 rises and falls with r1
high). Side conditions: one consistent corner on ustate O6 and on g1's I2 arcs
(`qr = qf`, `g1rq = g1fq`), and `qr + wfb ≥ 2`. -/
theorem cex_Q2 (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz) (hH : HQ2 D TA TA2)
    (hslack : u + D.wr2s + 1 = QBb D TA + D.wfb) (h2 : 2 ≤ D.qr + D.wfb) (hq : D.qr = D.qf)
    (hg : D.g1rq = D.g1fq) (hz : QBb D TA + D.wfb + D.qr + D.wq + D.g1rq < Hz) :
    ∃ t, L ≤ t ∧ t < Hz ∧ s.g1 t = true ∧ s.g1 (t + 1) = false ∧ s.r1 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q; have := hM.g1
  have hTA := f_TA_ge R hM S
  unfold TRb at hTA; unfold HQ2 QBb at hH; unfold QBb at hslack hz
  have qQB : s.q (QBb D TA) = true := by
    unfold QBb
    rw [R.H_q, f_r2_lo S (TA + D.wa0s + D.qr - D.wr2s - D.qr) (by omega) (by omega) (by omega),
      S.r1 _ (by omega) (by omega), f_A0_l S (TA + D.wa0s + D.qr - D.wa0s - D.qr) (by omega)
        (by omega), FS_set]
    simp
  have qt1 : s.q (u + D.wr2s + D.qr) = false := by
    rw [R.H_q, ← hq, f_r2_hi2 S (u + D.wr2s + D.qr - D.wr2s - D.qr) (by omega) (by omega),
      S.r1 _ (by omega) (by omega), f_A0_l S _ (by omega) (by omega), FS_both,
      f_q_lo R hM S _ (by omega) (by unfold QBb; omega)]
    rfl
  have ga : s.g1 (QBb D TA + D.wq + D.g1rq) = true := by
    rw [R.H_g1, FG1_eq, S.r1 _ (by unfold QBb; omega) (by unfold QBb; omega),
      show QBb D TA + D.wq + D.g1rq - D.wq - D.g1rq = QBb D TA by omega, qQB]
    simp
  have gb : s.g1 (u + D.wr2s + D.qr + D.wq + D.g1rq) = false := by
    rw [R.H_g1, FG1_eq, FG1_eq, ← hg,
      show u + D.wr2s + D.qr + D.wq + D.g1rq - D.wq - D.g1rq = u + D.wr2s + D.qr by omega, qt1]
    simp
  obtain ⟨t, h1, h3, h4, h5⟩ := fall_tick s.g1 _ _ (by unfold QBb; omega) ga gb
  exact ⟨t, by unfold QBb at h1; omega, by omega, h4, h5,
    S.r1 t (by unfold QBb at h1; omega) (by omega)⟩

/-- **Race G2 at slack −1 ⇒ C's H_ARB2 fails** (g2 re-rises after q flipped, falls again
with r2 high). -/
theorem cex_G2 (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2)
    (hslack : u + D.wr2g + 1 = QBb D TA + D.wq) (hz : QBb D TA + D.wq + D.g2f < Hz) :
    ∃ t, L ≤ t ∧ t < Hz ∧ s.g2 t = true ∧ s.g2 (t + 1) = false ∧ s.r2 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q; have := hM.g2
  have hTA := f_TA_ge R hM S
  unfold TRb at hTA
  have hQB : t0 < QBb D TA := by unfold QBb; omega
  have ga : s.g2 (u + D.wr2g + D.g2r) = true := by
    rw [R.H_g2, FG2_eq, f_r2_hi2 S (u + D.wr2g + D.g2r - D.wr2g - D.g2r) (by omega) (by omega),
      f_q_lo R hM S _ (by omega) (by omega)]
    simp
  have gb : s.g2 (QBb D TA + D.wq + D.g2f) = false := by
    rw [R.H_g2, FG2_eq, FG2_eq,
      f_q_hi R hM S hQ hH (QBb D TA + D.wq + D.g2f - D.wq - D.g2r) (by omega) (by omega),
      f_q_hi R hM S hQ hH (QBb D TA + D.wq + D.g2f - D.wq - D.g2f) (by omega) (by omega)]
    simp
  obtain ⟨t, h1, h3, h4, h5⟩ := fall_tick s.g2 _ _ (by omega) ga gb
  exact ⟨t, by omega, by omega, h4, h5, f_r2_hi2 S t (by omega) (by omega)⟩

/-- **Race R2 at slack −1 ⇒ C's `zr` fails** with a tight z-rise row (`G1b + 1 = RRb + dz`). -/
theorem cex_R2 (R : Run D s) (hM : MB D M) (S : E2 D M s a L t0 TA TA2 u Hz)
    (hQ : RQ2 D TA u) (hH : HQ2 D TA TA2) (hG : RG2 D TA u)
    (hslack : u + D.wr2s + D.Rr2 + 1 = RRb D TA) (h2 : 2 ≤ D.smin + D.wa0s + D.qr + D.wfb + D.Rrq)
    {z : Int → Bool} {dz : Int} (Z : ZLine s z dz) (hdz : 0 ≤ dz)
    (htight : G1b D TA + 1 = RRb D TA + dz) (hG2 : G2b D t0 TA + 2 ≤ RRb D TA + dz)
    (hz : RRb D TA + dz < Hz) :
    ∃ t, L + M ≤ t ∧ t < Hz ∧ z t = false ∧ z (t + 1) = true ∧ (s.g1 t || s.g2 t) = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.ord; have := hM.q; have := hM.R0
  have hTA := f_TA_ge R hM S
  unfold TRb at hTA; unfold RRb at hslack htight hG2 hz; unfold QBb at hslack htight hG2 hz
  have hu : s.R0 (RRb D TA - 1) = true := by
    unfold RRb QBb
    rw [R.H_R0, f_r2_hi2 S _ (by omega) (by omega), S.r1 _ (by omega) (by omega), FR_r1r2]
    simp
  have hl : s.R0 (RRb D TA - 2) = false := by
    unfold RRb QBb
    rw [R.H_R0, f_r2_lo S _ (by omega) (by omega) (by omega),
      f_r2_lo S (TA + D.wa0s + D.qr + D.wfb + D.Rrq - 2 - D.wr2s - D.Rf2) (by omega) (by omega)
        (by omega),
      S.r1 _ (by omega) (by omega), S.r1 _ (by omega) (by omega),
      f_q_lo R hM S _ (by omega) (by unfold QBb; omega),
      f_q_lo R hM S (TA + D.wa0s + D.qr + D.wfb + D.Rrq - 2 - D.wfb - D.Rfq) (by omega)
        (by unfold QBb; omega), FR_r1]
    rfl
  refine ⟨RRb D TA + dz - 2, by unfold RRb QBb; omega, by unfold RRb QBb; omega, ?_, ?_, ?_⟩
  · rw [Z, show RRb D TA + dz - 2 - dz = RRb D TA - 2 by omega, hl]
  · rw [Z, show RRb D TA + dz - 2 + 1 - dz = RRb D TA - 1 by omega, hu]
  · rw [f_g1_eq R hM S hQ hH _ (by unfold RRb QBb; omega) (by unfold RRb QBb; omega),
      f_g2_eq R hM S hQ hH hG _ (by unfold RRb QBb; omega) (by unfold RRb QBb; omega)]
    have : ¬ (RRb D TA + dz - 2 < G2b D t0 TA) := by unfold RRb QBb; omega
    have : ¬ (G1b D TA ≤ RRb D TA + dz - 2) := by unfold RRb QBb; omega
    simp [*]

/-- Arc form of the mirror races (four-phase client 2: `T1b < u`). -/
structure Arc2 (D : Dl) : Prop where
  q : D.wa0s + D.qr + D.wfb ≤ D.wa02 + D.c2f + 1 + D.wr2s
  r : D.wa0s + D.qr + D.wfb + D.Rrq ≤ D.wa02 + D.c2f + 1 + D.wr2s + D.Rr2
  g : D.wa0s + D.qr + D.wq ≤ D.wa02 + D.c2f + 1 + D.wr2g

theorem races_of_arc2 (D : Dl) (t0 TA u : Int) (hC : T1b D t0 TA < u) (hA : Arc2 D) :
    RQ2 D TA u ∧ RRc2 D TA u ∧ RG2 D TA u := by
  have := Int.le_max_right (G2b D t0 TA + D.wg2) (TA + D.wa02)
  have hT : TA + D.wa02 + D.c2f ≤ T1b D t0 TA := by unfold T1b; omega
  obtain ⟨h1, h2, h3⟩ := hA
  unfold RQ2 RRc2 RG2 RRb QBb; omega

end dir2

/-! ## Non-vacuity: a run from reset with two handovers and two early re-requests

Delays `Dw` of `ArbMultiToken` (every route and arc 1 ps, rise = fall, server minimum
3 ps), z line `dz = 2`, server the pure delay `A0 t = R0 (t - 3)`. From reset (every
signal low before 0, q = 1): r1 rises at 0, r2 at 10 (waits); client 1 releases at 30
and RE-REQUESTS at 38 = T1 + 1 (its ack fell at 37; A0 re-rises only at 42); client 2
holds, releases at 54 and re-requests at 62 = T1b + 1 (A0 re-rises at 66); client 1
releases again at 80. The traces were produced by a discrete simulation
(`/tmp/claude-0/probes/Barb3/sim.py`, scratch) and are CHECKED here against every gate
relation and the server relation for all `t ∈ ℤ`. -/

def Wn : Sigs where
  r1 := fun t => (decide (0 ≤ t) && decide (t < 30)) || (decide (38 ≤ t) && decide (t < 80))
  r2 := fun t => (decide (10 ≤ t) && decide (t < 54)) || decide (62 ≤ t)
  q := fun t => decide (t < 37) || (decide (61 ≤ t) && decide (t < 87))
  R0 := fun t => (decide (2 ≤ t) && decide (t < 32)) || (decide (39 ≤ t) && decide (t < 56)) ||
    (decide (63 ≤ t) && decide (t < 82)) || decide (89 ≤ t)
  g1 := fun t => (decide (2 ≤ t) && decide (t < 32)) || (decide (63 ≤ t) && decide (t < 82))
  g2 := fun t => (decide (39 ≤ t) && decide (t < 56)) || decide (89 ≤ t)
  A0 := fun t => (decide (5 ≤ t) && decide (t < 35)) || (decide (42 ≤ t) && decide (t < 59)) ||
    (decide (66 ≤ t) && decide (t < 85)) || decide (92 ≤ t)
  A1 := fun t => (decide (7 ≤ t) && decide (t < 37)) || (decide (68 ≤ t) && decide (t < 87))
  A2 := fun t => (decide (44 ≤ t) && decide (t < 61)) || decide (94 ≤ t)

def zn : Int → Bool := fun t => (decide (4 ≤ t) && decide (t < 34)) ||
  (decide (41 ≤ t) && decide (t < 58)) || (decide (65 ≤ t) && decide (t < 84)) || decide (91 ≤ t)

theorem Wn_run : Run Dw Wn where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [Wn, Dw, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [Wn, Dw, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [Wn, Dw, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [Wn, Dw, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [Wn, Dw, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [Wn, Dw, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 5 ∨ t = 35 ∨ t = 42 ∨ t = 59 ∨ t = 66 ∨ t = 85 ∨ t = 92 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [Wn]; omega)
    refine ⟨t - 3, by simp [Dw], by rw [Bool.eq_iff_iff]; simp [Wn]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [Wn]; omega

theorem zn_line : ZLine Wn zn 2 := by
  intro t; rw [Bool.eq_iff_iff]; simp [Wn, zn]; omega

theorem Wn_E1 : E1 Dw 2 Wn 5 12 30 35 42 38 54 where
  ord := by omega
  r1 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [Wn]; omega
  r2 := by intro t h1 h2; simp [Wn]; omega
  A0 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [Wn]; omega
  A0p := by decide
  R0a := by intro t h1 h2; simp [Wn]; omega
  q0 := by intro t h1 h2; simp [Wn]; omega
  A10 := by intro t h1 h2; simp [Wn]; omega
  A20 := by intro t h1 h2; simp [Wn]; omega
  g10 := by intro t h1 h2; simp [Wn]; omega
  g20 := by intro t h1 h2; simp [Wn]; omega

theorem Wn_E2 : E2 Dw 2 Wn 42 46 54 59 66 62 80 where
  ord := by omega
  r1 := by intro t h1 h2; simp [Wn]; omega
  r2 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [Wn]; omega
  A0 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [Wn]; omega
  A0p := by decide
  R0a := by intro t h1 h2; simp [Wn]; omega
  q0 := by intro t h1 h2; simp [Wn]; omega
  A10 := by intro t h1 h2; simp [Wn]; omega
  A20 := by intro t h1 h2; simp [Wn]; omega
  g10 := by intro t h1 h2; simp [Wn]; omega
  g20 := by intro t h1 h2; simp [Wn]; omega

theorem Wn_rows1 : Rows1 Dw 2 30 35 42 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [G1, G2, QB, TR, RR, T1, T2r, Dw] <;> omega

theorem Wn_rows2 : Rows2 Dw 2 54 59 66 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [G1b, G2b, QBb, TRb, RRb, T1b, T2rb, Dw] <;> omega

/-- **Non-vacuity of the window theorems (`e_exclusion`, `e_fields`, `f_exclusion`,
`f_fields`)**: one run from reset (every signal low before 0), with every delay
nonzero, satisfies all their hypotheses for two consecutive handovers (client 1 → 2 at
g2↑ = 39, client 2 → 1 at g1↑ = 63), and in both the releasing client re-requests
BEFORE the server re-raises A0 (38 < 42, 62 < 66), which H_SLOW_REREQ of
`ArbMultiToken` (`TA2 + 4M ≤ u`) excludes. -/
theorem early_nonvacuous : ∃ (D : Dl) (s : Sigs) (z : Int → Bool) (dz M : Int),
    Run D s ∧ MB D M ∧ ZLine s z dz ∧ RT1 D ∧ RT1b D ∧
    E1 D M s 5 12 30 35 42 38 54 ∧ RQ D 35 38 ∧ RRc D 35 38 ∧ RG D 35 38 ∧
    T1 D 30 35 + D.wfa1 ≤ 42 + D.wa01 ∧ 35 + D.wa02 ≤ G2 D 35 + D.wg2 ∧ T1 D 30 35 < 38 ∧
    Rows1 D dz 30 35 42 ∧ Arc1 D ∧
    E2 D M s 42 46 54 59 66 62 80 ∧ RQ2 D 59 62 ∧ RRc2 D 59 62 ∧ RG2 D 59 62 ∧
    T1b D 54 59 + D.wfa2 ≤ 66 + D.wa02 ∧ 59 + D.wa01 ≤ G1b D 59 + D.wg1 ∧ T1b D 54 59 < 62 ∧
    Rows2 D dz 54 59 66 ∧ Arc2 D ∧
    (∀ t, t < 0 → s.r1 t = false ∧ s.r2 t = false ∧ s.g1 t = false ∧ s.g2 t = false ∧
      s.A0 t = false ∧ s.A1 t = false ∧ s.A2 t = false ∧ s.R0 t = false ∧ z t = false) ∧
    0 < D.wr1s ∧ 0 < D.wfb ∧ 0 < D.qr ∧ 0 < D.g1r1 ∧ 0 < D.c1r ∧ 0 < D.smin ∧ 0 < dz ∧
    (38 : Int) < 42 ∧ (38 : Int) < 42 + 4 * M ∧ (62 : Int) < 66 ∧
    s.g2 38 = false ∧ s.g2 39 = true ∧ s.g1 62 = false ∧ s.g1 63 = true :=
  ⟨Dw, Wn, zn, 2, 2, Wn_run, Dw_MB, zn_line, Dw_rt.1, Dw_rt.2.2.1,
    Wn_E1, by simp [RQ, QB, Dw], by simp [RRc, RR, QB, Dw], by simp [RG, QB, Dw],
    by simp [T1, G1, QB, Dw] <;> omega, by simp [G2, QB, Dw], by simp [T1, G1, QB, Dw] <;> omega,
    Wn_rows1, by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Dw],
    Wn_E2, by simp [RQ2, QBb, Dw], by simp [RRc2, RRb, QBb, Dw], by simp [RG2, QBb, Dw],
    by simp [T1b, G2b, QBb, Dw] <;> omega, by simp [G1b, QBb, Dw],
    by simp [T1b, G2b, QBb, Dw] <;> omega,
    Wn_rows2, by refine ⟨?_, ?_, ?_⟩ <;> simp [Dw],
    by intro t ht; simp [Wn, zn]; omega,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## A concrete counter-run for race G at slack −1 (direction 1)

`Dg` = `Dw` with q's route to ugrant 3 ps instead of 1. From reset: r1 at 0, r2 at 10
(waits for ever), client 1 releases at 30 and re-requests at 38 = T1 + 1, the earliest
four-phase instant. Race G misses by exactly 1 ps (`QB + wq + g1rq = u + wr1g + g1r1 + 1`;
the arc form `Arc1.gr` misses by 1 too), races Q and R and H_HOLDQ hold, and g1 makes a
1 ps runt at 40 while r1 is high: C's H_ARB1 fails (g1 falls to 0 with x.req = 1). -/

def Dg : Dl where
  wr1s := 1
  wr2s := 1
  wr1g := 1
  wr2g := 1
  wfb := 1
  wa0s := 1
  wq := 3
  wg1 := 1
  wa01 := 1
  wfa1 := 1
  wg2 := 1
  wa02 := 1
  wfa2 := 1
  qr := 1
  qf := 1
  Rr1 := 1
  Rf1 := 1
  Rr2 := 1
  Rf2 := 1
  Rrq := 1
  Rfq := 1
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 1
  g1fq := 1
  g2r := 1
  g2f := 1
  c1r := 1
  c1f := 1
  c2r := 1
  c2f := 1
  smin := 3
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def Wg : Sigs where
  r1 := fun t => (decide (0 ≤ t) && decide (t < 30)) || decide (38 ≤ t)
  r2 := fun t => decide (10 ≤ t)
  q := fun t => decide (t < 37)
  R0 := fun t => (decide (2 ≤ t) && decide (t < 32)) || decide (39 ≤ t)
  g1 := fun t => (decide (2 ≤ t) && decide (t < 32)) || (decide (40 ≤ t) && decide (t < 41))
  g2 := fun t => decide (41 ≤ t)
  A0 := fun t => (decide (5 ≤ t) && decide (t < 35)) || decide (42 ≤ t)
  A1 := fun t => decide (7 ≤ t) && decide (t < 37)
  A2 := fun t => decide (44 ≤ t)

theorem Wg_run : Run Dg Wg where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [Wg, Dg, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [Wg, Dg, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [Wg, Dg, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [Wg, Dg, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [Wg, Dg, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [Wg, Dg, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 5 ∨ t = 35 ∨ t = 42 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [Wg]; omega)
    refine ⟨t - 3, by simp [Dg], by rw [Bool.eq_iff_iff]; simp [Wg]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [Wg]; omega

theorem Wg_E1 : E1 Dg 4 Wg 5 12 30 35 42 38 100 where
  ord := by omega
  r1 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [Wg]; omega
  r2 := by intro t h1 h2; simp [Wg]; omega
  A0 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [Wg]; omega
  A0p := by decide
  R0a := by intro t h1 h2; simp [Wg]; omega
  q0 := by intro t h1 h2; simp [Wg]; omega
  A10 := by intro t h1 h2; simp [Wg]; omega
  A20 := by intro t h1 h2; simp [Wg]; omega
  g10 := by intro t h1 h2; simp [Wg]; omega
  g20 := by intro t h1 h2; simp [Wg]; omega

theorem Dg_MB : MB Dg 4 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Dg]

/-- **Counter-run for race G (slack −1), concrete and from reset.** Every hypothesis of
`e_fields` except race G holds (races Q, R, RT1, RT2a, A0 fork, the four-phase client),
race G and its arc form miss by exactly 1 ps, and C's H_ARB1 fails at tick 40 → 41;
`cex_G` applies to this run. -/
theorem cexG_run : ∃ (D : Dl) (s : Sigs),
    Run D s ∧ MB D 4 ∧ E1 D 4 s 5 12 30 35 42 38 100 ∧ RQ D 35 38 ∧ RRc D 35 38 ∧
    HQ D 35 42 ∧ RT1 D ∧ T1 D 30 35 < 38 ∧ T1 D 30 35 + D.wfa1 ≤ 42 + D.wa01 ∧
    35 + D.wa02 ≤ G2 D 35 + D.wg2 ∧
    QB D 35 + D.wq + D.g1rq = 38 + D.wr1g + D.g1r1 + 1 ∧
    D.wa0s + D.qf + D.wq + D.g1rq = D.wa01 + D.c1f + 1 + D.wr1g + D.g1r1 + 1 ∧
    (∀ t, t < 0 → s.g1 t = false ∧ s.g2 t = false ∧ s.A0 t = false) ∧
    s.r1 40 = true ∧ s.g1 40 = true ∧ s.g1 41 = false ∧
    (∃ t, 12 ≤ t ∧ t < 100 ∧ s.g1 t = true ∧ s.g1 (t + 1) = false ∧ s.r1 t = true) :=
  ⟨Dg, Wg, Wg_run, Dg_MB, Wg_E1, by simp [RQ, QB, Dg], by simp [RRc, RR, QB, Dg],
    by simp [HQ, QB, Dg], by simp [RT1, Dg], by simp [T1, G1, QB, Dg] <;> omega,
    by simp [T1, G1, QB, Dg] <;> omega, by simp [G2, QB, Dg], by simp [QB, Dg], by simp [Dg],
    by intro t ht; simp [Wg]; omega, by decide, by decide, by decide,
    cex_G Wg_run Dg_MB Wg_E1 (by simp [RQ, QB, Dg]) (by simp [HQ, QB, Dg]) Dg.g1r1 Dg.g1rq
      (Or.inl ⟨rfl, rfl⟩) (by simp [QB, Dg]) (by simp [QB, Dg])⟩

end Formal.Cells.ArbAMerge
