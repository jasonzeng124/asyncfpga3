import Formal.Cells.AMergeTimed

/-!
# Probe Cm2: non-vacuity witnesses for `AMergeTimed` (consistent corners)

A family of explicit runs of 7h's / 7j's arbiter model, parametrised by the
three consistent-corner arc values (`a` = O6, `b` = O5 from I0/I1, `cq` = O5
from I2; prjxray SLOW_MAX 124/152/150, FAST_MIN 45/44/42) and by the server's
response `S`, every route 0 (arc-only). `dW 124 152 150 S` and `dW 45 44 42 S`
are `ArbCorners.cDl slowMax/fastMin RF.sym (x0 S)` (`dW_slow`, `dW_fast`), so
no corner is mixed. The runs satisfy `Run` for ALL t (server relation
included) and the scenario `Scn`/`Scn2` for every horizon past the second
server edge; the server answers in exactly `S`, the worst case.

The wrapper is instantiated with the index LUT arc at the same corner and the
request path `dz` = uor + the 12 hops of gcd_hw's `DELAY = 12` (13 arcs), or
`dz` = uor alone (DELAY = 0, `bd_delay_gated` bypass) for the counter-trace.
The server is taken as `S = dz` (H_Z_IN_SRV with equality: the consumer
acknowledges as soon as it captured).
-/

namespace Formal.Cells.AMergeTimedW
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2
open Formal.Cells.AMergeTimed

/-- 7h's `Dl` at one consistent corner, routes 0, server `S`. -/
def dW (a b cq S : Int) (h : 0 < a ∧ 0 ≤ b ∧ 0 ≤ cq ∧ 0 ≤ S) : Dl where
  wr1s := 0
  wr2s := 0
  wr1g := 0
  wr2g := 0
  wfb := 0
  wa0s := 0
  wq := 0
  wg1 := 0
  wa01 := 0
  wfa1 := 0
  wg2 := 0
  wa02 := 0
  wfa2 := 0
  qr := a
  qf := a
  Rr1 := b
  Rf1 := b
  Rr2 := b
  Rf2 := b
  Rrq := cq
  Rfq := cq
  g1r1 := b
  g1f1 := b
  g1r2 := b
  g1f2 := b
  g1rq := cq
  g1fq := cq
  g2r := a
  g2f := a
  c1r := a
  c1f := a
  c2r := a
  c2f := a
  smin := S
  H_NONNEG := by omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by omega

theorem dW_slow (S : Int) (h : 0 ≤ S) :
    dW 124 152 150 S (by omega) =
      ArbCorners.cDl ArbCorners.slowMax ArbCorners.RF.sym (ArbCorners.x0 S h) := rfl

theorem dW_fast (S : Int) (h : 0 ≤ S) :
    dW 45 44 42 S (by omega) =
      ArbCorners.cDl ArbCorners.fastMin ArbCorners.RF.sym (ArbCorners.x0 S h) := rfl

/-! ## Client 1 -> client 2 (7h's `Scn`) -/

/-- TR = b, TA = b + S, QB = TA + a, G2 = QB + a, RR = QB + cq, TA2 = RR + S,
T2 = TA2 + a. -/
def W1g (a b cq S : Int) : Sigs where
  r1 := fun t => decide (t < 0)
  r2 := fun _ => true
  q := fun t => decide (t < b + S + a)
  R0 := fun t => decide (t < b) || decide (b + S + a + cq ≤ t)
  g1 := fun t => decide (t < b)
  g2 := fun t => decide (b + S + a + a ≤ t)
  A0 := fun t => (decide (-1000 ≤ t) && decide (t < b + S)) || decide (b + S + a + cq + S ≤ t)
  A1 := fun t => decide (t < b + S + a)
  A2 := fun t => decide (b + S + a + cq + S + a ≤ t)

theorem W1g_run (a b cq S : Int) (h : 0 < a ∧ 0 ≤ b ∧ 0 ≤ cq ∧ 0 ≤ S) (hs : a ≤ 500 ∧ b ≤ 500 ∧ a ≤ S) :
    Run (dW a b cq S h) (W1g a b cq S) := by
  have ⟨h1, h2, h3, h4⟩ := h; have ⟨h5, h6, h7⟩ := hs
  exact {
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W1g, dW, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W1g, dW, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1g, dW, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1g, dW, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1g, dW, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1g, dW, CE_eq]; omega
  H_SRV := by
    intro t ht
    have e : t = -1000 ∨ t = b + S ∨ t = b + S + a + cq + S := by
      exact Classical.byContradiction fun hc => ht (by rw [Bool.eq_iff_iff]; simp [W1g]; omega)
    rcases e with rfl | rfl | rfl
    · exact ⟨-1000 - S, by simp [dW], by rw [Bool.eq_iff_iff]; simp [W1g]; omega,
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [W1g]; omega⟩
    · exact ⟨b, by simp [dW], by rw [Bool.eq_iff_iff]; simp [W1g] <;> omega,
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [W1g]; omega⟩
    · exact ⟨b + S + a + cq, by simp [dW], by rw [Bool.eq_iff_iff]; simp [W1g] <;> omega,
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [W1g]; omega⟩ }

theorem W1g_scn (a b cq S : Int) (h : 0 < a ∧ 0 ≤ b ∧ 0 ≤ cq ∧ 0 ≤ S) (hs : a ≤ 500 ∧ b ≤ 500 ∧ a ≤ S)
    (Hz : Int) (hz : b + S + a + cq + S < Hz) :
    Scn (dW a b cq S h) (W1g a b cq S) 0 (-1000) (b + S) (b + S + a + cq + S) Hz := by
  have ⟨h1, h2, h3, h4⟩ := h; have ⟨h5, h6, h7⟩ := hs
  exact {
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W1g]; omega
  H_A0_prev := by simp [W1g] <;> omega
  H_q_init := by intro t ht; simp [W1g]; omega
  H_A1_init := by intro t ht; simp [W1g]; omega
  H_A2_init := by intro t ht; simp [W1g]; omega
  H_SETTLED := by simp [dW]; omega }

/-! ## Client 2 -> client 1 (7j's `Scn2`) -/

/-- TRb = b, TA = b + S, QBb = TA + a, RRb = QBb + cq, G1b = QBb + cq,
G2b = a, T1b = TA + a (needs `a ≤ b + S`; `a ≤ S` is assumed: A0's low pulse covers ua1/ua2's loop), TA2 = RRb + S, T2b = TA2 + a. -/
def W2g (a b cq S : Int) : Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (b + S + a ≤ t)
  R0 := fun t => decide (t < b) || decide (b + S + a + cq ≤ t)
  g1 := fun t => decide (b + S + a + cq ≤ t)
  g2 := fun t => decide (t < a)
  A0 := fun t => (decide (-1000 ≤ t) && decide (t < b + S)) || decide (b + S + a + cq + S ≤ t)
  A1 := fun t => decide (b + S + a + cq + S + a ≤ t)
  A2 := fun t => decide (t < b + S + a)

theorem W2g_run (a b cq S : Int) (h : 0 < a ∧ 0 ≤ b ∧ 0 ≤ cq ∧ 0 ≤ S) (hs : a ≤ 500 ∧ b ≤ 500 ∧ a ≤ S) :
    Run (dW a b cq S h) (W2g a b cq S) := by
  have ⟨h1, h2, h3, h4⟩ := h; have ⟨h5, h6, h7⟩ := hs
  exact {
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W2g, dW, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W2g, dW, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2g, dW, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2g, dW, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2g, dW, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2g, dW, CE_eq]; omega
  H_SRV := by
    intro t ht
    have e : t = -1000 ∨ t = b + S ∨ t = b + S + a + cq + S := by
      exact Classical.byContradiction fun hc => ht (by rw [Bool.eq_iff_iff]; simp [W2g]; omega)
    rcases e with rfl | rfl | rfl
    · exact ⟨-1000 - S, by simp [dW], by rw [Bool.eq_iff_iff]; simp [W2g]; omega,
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [W2g]; omega⟩
    · exact ⟨b, by simp [dW], by rw [Bool.eq_iff_iff]; simp [W2g] <;> omega,
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [W2g]; omega⟩
    · exact ⟨b + S + a + cq, by simp [dW], by rw [Bool.eq_iff_iff]; simp [W2g] <;> omega,
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [W2g]; omega⟩ }

theorem W2g_scn (a b cq S : Int) (h : 0 < a ∧ 0 ≤ b ∧ 0 ≤ cq ∧ 0 ≤ S) (hs : a ≤ 500 ∧ b ≤ 500 ∧ a ≤ S)
    (Hz : Int) (hz : b + S + a + cq + S < Hz) :
    Scn2 (dW a b cq S h) (W2g a b cq S) 0 (-1000) (b + S) (b + S + a + cq + S) Hz := by
  have ⟨h1, h2, h3, h4⟩ := h; have ⟨h5, h6, h7⟩ := hs
  exact {
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W2g]; omega
  H_A0_prev := by simp [W2g] <;> omega
  H_q_init := by intro t ht; simp [W2g]; omega
  H_A1_init := by intro t ht; simp [W2g]; omega
  H_A2_init := by intro t ht; simp [W2g]; omega
  H_SETTLED := by simp [dW]; omega }

/-! ## The wrapper at one corner -/

/-- Arc-only wrapper: every route 0, no setup, index LUT arc `x`, request path `dz`. -/
def wW (x dz : Int) (h : 0 < x ∧ 0 ≤ dz) : Wd :=
  ⟨0, 0, x, x, 0, dz, 0, by omega, by omega, by omega⟩

/-! ### Sufficiency is not vacuous (H_BUNDLED_IDX, both races) -/

/-- SLOW_MAX, server = request path = uor + 12 DELAY hops = 13 × 124 ps. -/
def Ds : Dl := dW 124 152 150 1612 (by omega)
def Ws : Wd := wW 124 1612 (by omega)
/-- FAST_MIN, the same with 13 × 45 ps. -/
def Df : Dl := dW 45 44 42 585 (by omega)
def Wf : Wd := wW 45 585 (by omega)

/-- **SLOW_MAX, DELAY = 12.** Both races hold (race 1 margin
`cq + dz − a − x` = 1514 ps; race 2 `ack` margin `cq + dz − x` = 1638 ps), the
arbiter's own RT2b and 7g fork hold, H_Z_IN_SRV holds with equality, the runs
exist for all t and the minimal capture `RR + dz` is a legal `ReqZ`. The index
at the consumer really changes: 0 at 2135, 1 from 2136 (`G2 + x`) on, and is
1 at the capture 3650; in the mirror run it is 0 at the capture. -/
theorem nonvacuous_slow :
    BidxA Ds Ws ∧ BidxB Ds Ws ∧ A0Fork Ds ∧ RT2b Ds ∧ Ws.dz ≤ Ds.smin ∧
    Run Ds (W1g 124 152 150 1612) ∧ Run Ds (W2g 124 152 150 1612) ∧
    (∀ Hz, 3650 < Hz → Scn Ds (W1g 124 152 150 1612) 0 (-1000) 1764 3650 Hz) ∧
    (∀ Hz, 3650 < Hz → Scn2 Ds (W2g 124 152 150 1612) 0 (-1000) 1764 3650 Hz) ∧
    ReqZ (W1g 124 152 150 1612) (TR Ds 0) 3651 (RR Ds 1764 + 1612) 1612 ∧
    ReqZ (W2g 124 152 150 1612) (TRb Ds 0) 3651 (RRb Ds 1764 + 1612) 1612 ∧
    Cons Ws (W1g 124 152 150 1612) 2135 = false ∧
    Cons Ws (W1g 124 152 150 1612) 2136 = true ∧
    Cons Ws (W1g 124 152 150 1612) (RR Ds 1764 + 1612) = true ∧
    Cons Ws (W2g 124 152 150 1612) (RRb Ds 1764 + 1612) = false := by
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_,
    W1g_run _ _ _ _ _ (by omega), W2g_run _ _ _ _ _ (by omega),
    fun Hz hz => W1g_scn _ _ _ _ _ (by omega) Hz hz,
    fun Hz hz => W2g_scn _ _ _ _ _ (by omega) Hz hz, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [Ds, Ws, BidxA, A0Fork, ReqZ, TR, TRb, RR, RRb, QB, QBb, dW, wW, Cons, Idx, IX_eq,
    W1g, W2g]
  · exact ⟨2038, by omega, by omega, by omega, by omega⟩
  · exact ⟨2038, by omega, by omega, by omega, by omega⟩

/-- **FAST_MIN, DELAY = 12.** Race 1 margin 537 ps; race 2 (`ack`) margin 582 ps. -/
theorem nonvacuous_fast :
    BidxA Df Wf ∧ BidxB Df Wf ∧ A0Fork Df ∧ RT2b Df ∧ Wf.dz ≤ Df.smin ∧
    Run Df (W1g 45 44 42 585) ∧ Run Df (W2g 45 44 42 585) ∧
    (∀ Hz, 1301 < Hz → Scn Df (W1g 45 44 42 585) 0 (-1000) 629 1301 Hz) ∧
    (∀ Hz, 1301 < Hz → Scn2 Df (W2g 45 44 42 585) 0 (-1000) 629 1301 Hz) ∧
    Cons Wf (W1g 45 44 42 585) (RR Df 629 + 585) = true ∧
    Cons Wf (W2g 45 44 42 585) (RRb Df 629 + 585) = false := by
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_,
    W1g_run _ _ _ _ _ (by omega), W2g_run _ _ _ _ _ (by omega),
    fun Hz hz => W1g_scn _ _ _ _ _ (by omega) Hz hz,
    fun Hz hz => W2g_scn _ _ _ _ _ (by omega) Hz hz, ?_, ?_⟩ <;>
  simp [Df, Wf, BidxA, A0Fork, RR, RRb, QB, QBb, dW, wW, Cons, Idx, IX_eq, W1g, W2g]

/-! ### Counter-trace instance: DELAY = 0 at FAST_MIN -/

def D0f : Dl := dW 45 44 42 45 (by omega)
def W0f : Wd := wW 45 45 (by omega)

/-- **FAST_MIN, `bd_delay_gated` bypassed (DELAY = 0, dz = uor = 45).** Race 1
fails by 3 ps at zero routing: g2 (ugrant O6, 45) + index (O6, 45) = 90 exceeds
R0 (ustate O5 from I2, 42) + uor (45) = 87, so the consumer still sees
`index = 0` at the capture of client 2's token. (At SLOW_MAX the same cell
passes by 26 ps: 124 + 124 vs 150 + 124, `slow_delay0_passes`.) gcd_hw uses
DELAY = 12; this says what the DELAY line is FOR, it is not a gcd_hw bug. -/
theorem counter_fast_delay0 :
    ¬ BidxA D0f W0f ∧ A0Fork D0f ∧ W0f.dz ≤ D0f.smin ∧
    Run D0f (W1g 45 44 42 45) ∧ Cons W0f (W1g 45 44 42 45) (RR D0f 89 + 45) = false := by
  refine ⟨?_, ?_, ?_, W1g_run _ _ _ _ _ (by omega), ?_⟩
  · simp [D0f, W0f, BidxA, dW, wW]
  · simp [D0f, A0Fork, dW]
  · simp [D0f, W0f, dW, wW]
  · exact bidx_new_owner_counter (W1g_run 45 44 42 45 (by omega) (by omega))
      (W1g_scn 45 44 42 45 (by omega) (by omega) 1000 (by omega))
      (by simp [A0Fork, dW]) (by simp [W0f, dW, wW]) (by simp [W0f, BidxA, dW, wW])

theorem slow_delay0_passes : BidxA (dW 124 152 150 124 (by omega)) (wW 124 124 (by omega)) := by
  simp [BidxA, dW, wW]

/-- **Per-pin O5 (ArbCornersPin).** On routed seeds S1, S2, S4 ustate reads its
own q on A5, whose SLICEM O5 arc is 48/116 (FAST_MIN/SLOW_MAX), not O5_I2's
42/150 (`ArbCornersPin.q_pins`, `pinCol 4`). With DELAY = 0 race 1 then fails
at SLOW_MAX by 8 ps (124 + 124 vs 116 + 124) and passes at FAST_MIN by 3 ps
(45 + 45 vs 48 + 45): with the bypass, every routed seed fails at one corner. -/
theorem pinA5_delay0 :
    ¬ BidxA (dW 124 152 116 124 (by omega)) (wW 124 124 (by omega)) ∧
    BidxA (dW 45 44 48 45 (by omega)) (wW 45 45 (by omega)) := by
  simp [BidxA, dW, wW]

/-! ## H_IDX_ACK_FORK witnesses -/

/-- The fork scenario's signals: client 2 owns (q = 0), A2 rises at `Ar`,
client 2 drops r2 at `t1`; g2 is ugrant's O6 at arc `a` (route 0). -/
def Fk (a Ar t1 : Int) : Sigs where
  r1 := fun _ => false
  r2 := fun t => decide (t < t1)
  q := fun _ => false
  R0 := fun _ => false
  g1 := fun _ => false
  g2 := fun t => decide (t < t1 + a)
  A0 := fun _ => true
  A1 := fun _ => false
  A2 := fun t => decide (Ar ≤ t)

theorem Fk_g2 (a Ar t1 S : Int) (h : 0 < a ∧ 0 ≤ 0 ∧ 0 ≤ 0 ∧ 0 ≤ S) : ∀ t, (Fk a Ar t1).g2 t =
    (FG2 ((Fk a Ar t1).r1 (t - (dW a 0 0 S h).wr1g - (dW a 0 0 S h).g2r))
      ((Fk a Ar t1).r2 (t - (dW a 0 0 S h).wr2g - (dW a 0 0 S h).g2r))
      ((Fk a Ar t1).q (t - (dW a 0 0 S h).wq - (dW a 0 0 S h).g2r)) ||
     FG2 ((Fk a Ar t1).r1 (t - (dW a 0 0 S h).wr1g - (dW a 0 0 S h).g2f))
      ((Fk a Ar t1).r2 (t - (dW a 0 0 S h).wr2g - (dW a 0 0 S h).g2f))
      ((Fk a Ar t1).q (t - (dW a 0 0 S h).wq - (dW a 0 0 S h).g2f))) := by
  intro t; rw [Bool.eq_iff_iff]; simp [Fk, dW, FG2_eq]; omega

/-- **Non-vacuity (SLOW_MAX).** ugrant O6 = index O6 = 124, client = two LUT
arcs (`cmin = 248`), every route 0: `IdxAckFork` holds with margin
248 + 124 = 372 ps (the O6 arcs cancel), ugrant's relation holds for all t, the
scenario holds and the index stays 1 on [Ar, Hz). -/
theorem fork_nonvacuous_slow :
    IdxAckFork (dW 124 0 0 0 (by omega)) Ws 248 ∧
    FkScn (dW 124 0 0 0 (by omega)) Ws (Fk 124 0 248) (-500) 0 248 2000 248 ∧
    (∀ t, 0 ≤ t → t < 2000 → Idx Ws (Fk 124 0 248) t = true) := by
  have F : FkScn (dW 124 0 0 0 (by omega)) Ws (Fk 124 0 248) (-500) 0 248 2000 248 :=
    { H_ORDER := by omega
      H_q := fun _ _ _ => rfl
      H_r2 := fun _ _ _ => rfl
      H_A2 := fun _ _ _ => rfl
      H_CLIENT := by omega
      H_SETTLED := by simp [dW, Ws, wW] }
  have H : IdxAckFork (dW 124 0 0 0 (by omega)) Ws 248 := by simp [IdxAckFork, dW, Ws, wW]
  exact ⟨H, F, idx_ack_fork_hold (Fk_g2 124 0 248 0 (by omega)) F H⟩

/-- **The counter-trace is realisable.** Same cell, but the in1_ack route to the
index LUT is 700 ps (`wai = 700`, a deliberately long route; client = two
arcs): the index is 0 at t = 496 while `in1_ack` is high. -/
def Wlong : Wd := ⟨0, 700, 124, 124, 0, 1612, 0, by omega, by omega, by omega⟩

theorem fork_counter_witness :
    ¬ IdxAckFork (dW 124 0 0 0 (by omega)) Wlong 248 ∧
    FkScn (dW 124 0 0 0 (by omega)) Wlong (Fk 124 0 248) (-1000) 0 248 2000 248 ∧
    (Fk 124 0 248).A2 496 = true ∧ Idx Wlong (Fk 124 0 248) 496 = false := by
  have F : FkScn (dW 124 0 0 0 (by omega)) Wlong (Fk 124 0 248) (-1000) 0 248 2000 248 :=
    { H_ORDER := by omega
      H_q := fun _ _ _ => rfl
      H_r2 := fun _ _ _ => rfl
      H_A2 := fun _ _ _ => rfl
      H_CLIENT := by omega
      H_SETTLED := by simp [dW, Wlong] }
  have := idx_ack_fork_counter_minclient (Fk_g2 124 0 248 0 (by omega)) F (by omega)
    (by simp [IdxAckFork, dW, Wlong]) (by simp [dW, Wlong])
  simp [dW, Wlong] at this
  exact ⟨by simp [IdxAckFork, dW, Wlong], F, this⟩

end Formal.Cells.AMergeTimedW
