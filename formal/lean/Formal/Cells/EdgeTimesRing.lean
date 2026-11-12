import Formal.Cells.EdgeTimes
import Formal.Cells.RingPhys

/-!
# Probe Bedge (shard B): every live ring has a run, every `N`

`RingPhys` proves that any solution of a ring's edge-time equations (`PRing`, `PRingT`)
circulates forever and refines C's `Ring`, and that the hypotheses force C's condition
`0 < D < N` (`ring_cond`); solutions were exhibited only for `N = 3` and `N = 5`
(`RingPhysWit`, `RingPhysWit2`). This file constructs one for every `N`, every reset
pattern with `0 < D < N` and every delay assignment in the bands.

The edge-time recurrence of a ring has same-level dependencies (stage `i` waits for
`τ (prv i) j` when there is no wavefront at `i`, for `τ (nxt i) j` when there is one at
`nxt i`); it is well founded exactly when the wavefronts are neither absent nor everywhere.
The order used is a potential `phi` that rises by `D` across a channel without a wavefront
and falls by `N - D` across one with (consistent around the ring because the totals cancel),
with key `Mk * j + phi i` (`key_prv`, `key_nxt`, `key_low`).

## Assumed / proved / NOT covered

**Assumed** (`RDly`, `RBand`, `PRingT` on the bands): `N`, a reset pattern `b` with
`0 < D < N`, bands with `lo, wl, vl ≥ 1`, one realised constant delay per gate inside its
band, and RingPhys's timing rows (H_RST_LONG, H_LAT, H_WIRE_R, H_RT) on the BANDS.

**Proved:**
* `tauR`: the edge times, defined for every stage and every edge index by the recurrence;
  `tauR_eq`: they satisfy `H_TIMES` of the degenerate bands;
* `ring_c` (degenerate bands) and `ring_b` (the given bands): the run (real `bd_c2n` /
  `bd_c2n_set` INITs, transport gates, `nr`) satisfies every field of `PRing`;
  `ring_solution`, `ring_exists`;
* `ring_solution_witness`: the hypotheses are jointly satisfiable for EVERY `N` and EVERY
  `b` with `0 < D < N` (band `[1, 3]`, realised `1 + i % 3`, H_LAT with equality);
* `ring_run_iff`: a run satisfying `PRing ∧ PRingT` exists iff `0 < D < N` (the converse of
  `RingPhys.ring_cond`, RingPhys's open item); `ring_reset_exists`: C's reset rings
  (`resetState K`, `0 < K < N`, `N ≥ 3`) have a run that circulates forever with `D = 2`.

**NOT covered:** the closed max-plus form of the ring's edges (`tauR` is the trace read with
the degenerate band, `τ = nt (On i) d d (cph j) (Vph j)`, which lies in
`[cph j + d, cph j + d + 1]`; that the excitation is already at `Vph j` at `cph j`, giving
exactly `cph j + d`, is not proved here); a periodic-regime (cycle-time) statement; delays
varying from edge to edge. Core Lean only.
-/

namespace Formal.Cells.EdgeTimesRing
open Formal.Cells Formal.Net
open Formal.Cells.WinFifo (Win win_le Clean Spread)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_eq nt_before Stage cph τs cW vW)
open Formal.Cells.PipeTimed (Vph ex Ret)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo ash)
open Formal.Cells.RingPhys (xr exS SetStage StageB WireB)
open Formal.Cells.RingPhys (RingData PRing PRingT ring_nodes)
open Formal.Net.Ring (prv nxt)

/-- A delay assignment for a ring: reset pattern `b`, the bands of `RingData`, and one
realised constant delay inside each band. -/
structure RDly where
  N : Nat
  R : Nat
  b : Nat → Bool
  lo : Nat → Nat
  hi : Nat → Nat
  fl : Nat → Nat
  fh : Nat → Nat
  wl : Nat → Nat
  wh : Nat → Nat
  vl : Nat → Nat
  vh : Nat → Nat
  d : Nat → Nat
  f : Nat → Nat
  w : Nat → Nat
  v : Nat → Nat

/-- A constant-delay wire whose pin powers up at `b0`. -/
def pinB (b0 : Bool) (d : Nat) (x : Nat → Bool) (t : Nat) : Bool := if d ≤ t then x (t - d) else b0

/-- The INIT of a stage of reset polarity `c` (`bd_c2n_set` if `c`, else `bd_c2n`). -/
def initOf (c : Bool) : Nat := cond c CElemFn.INIT_c2n_set CElemTiming.INIT_c2n

/-- **The ring's run** (strong recursion on time). -/
def nr (P : RDly) (i t : Nat) : Bool :=
  if i < P.N then
    if _h : 1 ≤ P.d i ∧ P.d i ≤ t then
      CElemTiming.exc (initOf (P.b i))
        (if P.w i ≤ t - P.d i then nr P (prv P.N i) (t - P.d i - P.w i) else P.b (prv P.N i))
        (if P.v i ≤ t - P.d i then nr P (nxt P.N i) (t - P.d i - P.v i) else P.b (nxt P.N i))
        (if P.f i ≤ t - P.d i then nr P i (t - P.d i - P.f i) else P.b i)
        (decide (t - P.d i < P.R))
    else P.b i
  else P.b i
termination_by t
decreasing_by all_goals omega

def rqR (P : RDly) (i : Nat) : Nat → Bool := pinB (P.b (prv P.N i)) (P.w i) (nr P (prv P.N i))
def akR (P : RDly) (i : Nat) : Nat → Bool := pinB (P.b (nxt P.N i)) (P.v i) (nr P (nxt P.N i))
def qfR (P : RDly) (i : Nat) : Nat → Bool := pinB (P.b i) (P.f i) (nr P i)
def rsR (P : RDly) (t : Nat) : Bool := decide (t < P.R)

theorem nr_eq (P : RDly) (i t : Nat) (hi : i < P.N) : nr P i t =
    (if 1 ≤ P.d i ∧ P.d i ≤ t then CElemTiming.exc (initOf (P.b i)) (rqR P i (t - P.d i))
      (akR P i (t - P.d i)) (qfR P i (t - P.d i)) (rsR P (t - P.d i)) else P.b i) := by
  rw [nr]; simp only [hi, ↓reduceIte, dite_eq_ite, rqR, akR, qfR, rsR, pinB]

/-! ## The potential: a well-founded order on the events of one level -/

/-- `cnt` of the wavefronts among stages `< m`. -/
def ct (P : RDly) (m : Nat) : Nat := Ring.cnt (Ring.tok P.N P.b) m
/-- The potential of stage `i`: it rises by `D` across a channel without a wavefront and
falls by `N - D` across one with (so it is consistent around the ring). -/
def phi (P : RDly) (i : Nat) : Nat := P.N * P.N + Ring.D P.N P.b * (i + 1) - P.N * ct P (i + 1)
def Mk (P : RDly) : Nat := 2 * (P.N * P.N) + 1
/-- The event key: level-major, potential-minor. -/
def key (P : RDly) (i j : Nat) : Nat := Mk P * j + phi P i

theorem ct_le (P : RDly) (m : Nat) : ct P m ≤ m := Ring.cnt_le _ m

theorem ct_succ (P : RDly) (m : Nat) :
    ct P (m + 1) = ct P m + (if Ring.tok P.N P.b m then 1 else 0) := rfl

theorem DN_le (P : RDly) : Ring.D P.N P.b ≤ P.N := Ring.cnt_le _ _

theorem phi_lt (P : RDly) (i : Nat) (hi : i < P.N) : phi P i < Mk P := by
  unfold phi Mk
  have : Ring.D P.N P.b * (i + 1) ≤ P.N * P.N := Nat.mul_le_mul (DN_le P) (by omega)
  omega

theorem key_low (P : RDly) (i i' j : Nat) (hi' : i' < P.N) (hj : j ≠ 0) :
    key P i' (j - 1) < key P i j := by
  unfold key
  have := phi_lt P i' hi'
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.mul_succ]; omega

theorem phi_step (P : RDly) (i : Nat) (hi : i + 1 < P.N) :
    phi P (i + 1) + P.N * (if Ring.tok P.N P.b (i + 1) then 1 else 0) =
      phi P i + Ring.D P.N P.b := by
  unfold phi
  have h1 : P.N * ct P (i + 1) ≤ P.N * P.N := Nat.mul_le_mul_left _ (by have := ct_le P (i + 1); omega)
  have h2 : P.N * ct P (i + 1 + 1) ≤ P.N * P.N :=
    Nat.mul_le_mul_left _ (by have := ct_le P (i + 1 + 1); omega)
  have e1 : P.N * ct P (i + 1 + 1) = P.N * ct P (i + 1) +
      P.N * (if Ring.tok P.N P.b (i + 1) then 1 else 0) := by rw [ct_succ, Nat.mul_add]
  have e2 : Ring.D P.N P.b * (i + 1 + 1) = Ring.D P.N P.b * (i + 1) + Ring.D P.N P.b :=
    Nat.mul_succ _ _
  rw [e2]; rw [e1] at h2 ⊢; omega

theorem phi_last (P : RDly) (h : 1 ≤ P.N) : phi P (P.N - 1) = P.N * P.N := by
  unfold phi
  rw [show P.N - 1 + 1 = P.N by omega]
  show P.N * P.N + Ring.D P.N P.b * P.N - P.N * Ring.D P.N P.b = _
  rw [Nat.mul_comm (Ring.D P.N P.b)]; omega

theorem phi_zero (P : RDly) :
    phi P 0 + P.N * (if Ring.tok P.N P.b 0 then 1 else 0) = P.N * P.N + Ring.D P.N P.b := by
  unfold phi
  have e : ct P 1 = (if Ring.tok P.N P.b 0 then 1 else 0) := by
    rw [ct_succ]; show 0 + _ = _; rw [Nat.zero_add]
  rw [e, Nat.mul_one]
  have : P.N * (if Ring.tok P.N P.b 0 = true then 1 else 0) ≤ P.N := by split <;> omega
  have : Ring.D P.N P.b * 1 = Ring.D P.N P.b := Nat.mul_one _
  have : P.N ≤ P.N * P.N ∨ P.N = 0 := by
    rcases Nat.eq_zero_or_pos P.N with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_left _ h)
  omega

theorem prv_pos {n i : Nat} (h0 : 0 < i) (hi : i < n) : prv n i = i - 1 := by
  unfold prv
  rw [show i + n - 1 = (i - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem prv_zero {n : Nat} (h : 1 ≤ n) : prv n 0 = n - 1 := by
  unfold prv; rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]

theorem nxt_lt' {n i : Nat} (hi : i + 1 < n) : nxt n i = i + 1 := by
  unfold nxt; rw [Nat.mod_eq_of_lt hi]

theorem nxt_last {n : Nat} (h : 1 ≤ n) : nxt n (n - 1) = 0 := by
  unfold nxt; rw [show n - 1 + 1 = n by omega, Nat.mod_self]

/-- Same-level dependency on the upstream stage (no wavefront at `i`): the key drops. -/
theorem key_prv (P : RDly) (H0 : 0 < Ring.D P.N P.b) (i j : Nat) (hi : i < P.N)
    (ht : Ring.tok P.N P.b i = false) : key P (prv P.N i) j < key P i j := by
  unfold key
  suffices phi P (prv P.N i) < phi P i by omega
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    rw [prv_zero (by omega), phi_last P (by omega)]
    have := phi_zero P; rw [ht] at this; simp at this; omega
  · rw [prv_pos h hi]
    have := phi_step P (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega, ht] at this; simp at this; omega

/-- Same-level dependency on the downstream stage (wavefront at `nxt i`): the key drops. -/
theorem key_nxt (P : RDly) (H1 : Ring.D P.N P.b < P.N) (i j : Nat) (hi : i < P.N)
    (ht : Ring.tok P.N P.b (nxt P.N i) = true) : key P (nxt P.N i) j < key P i j := by
  unfold key
  suffices phi P (nxt P.N i) < phi P i by omega
  by_cases h : i + 1 < P.N
  · rw [nxt_lt' h] at ht ⊢
    have := phi_step P i h
    rw [ht] at this; simp at this; omega
  · have e : i = P.N - 1 := by omega
    subst e
    rw [nxt_last (by omega)] at ht ⊢
    rw [phi_last P (by omega)]
    have := phi_zero P; rw [ht] at this; simp at this; omega

/-! ## The edge times -/

def OnR (P : RDly) (i : Nat) : Nat → Bool := xr (P.b i) (nr P i)
def PR (P : RDly) (i : Nat) : Nat → Bool := xr (P.b (prv P.N i)) (rqR P i)
def QR (P : RDly) (i : Nat) : Nat → Bool := xr (P.b (nxt P.N i)) (akR P i)

/-- **The ring's edge times**, read off the run exactly as `PRing.H_TIMES` reads them (every
band degenerate at its realised delay). Well-founded by the event key: an event reads
events of the previous level, or same-level events of strictly smaller potential (the
guards hold whenever `0 < D < N`, `key_prv`, `key_nxt`, `key_low`). -/
def tauR (P : RDly) (i j : Nat) : Nat :=
  if i < P.N then
    nt (OnR P i) (P.d i) (P.d i)
      (max
        (if Ring.tok P.N P.b i then
          (if j = 0 then P.R else
            if _h : key P (prv P.N i) (j - 1) < key P i j then
              nt (PR P i) (P.w i) (P.w i) (tauR P (prv P.N i) (j - 1)) (Vph (j - 1)) else 0)
         else
          (if _h : key P (prv P.N i) j < key P i j then
              nt (PR P i) (P.w i) (P.w i) (tauR P (prv P.N i) j) (Vph j) else 0))
        (if Ring.tok P.N P.b (nxt P.N i) then
          (if _h : key P (nxt P.N i) j < key P i j then
              nt (QR P i) (P.v i) (P.v i) (tauR P (nxt P.N i) j) (Vph j) else 0)
         else
          (if j = 0 then P.R else
            if _h : key P (nxt P.N i) (j - 1) < key P i j then
              nt (QR P i) (P.v i) (P.v i) (tauR P (nxt P.N i) (j - 1)) (Vph (j - 1)) else 0)))
      (Vph j)
  else 0
termination_by key P i j

/-- The ring run as `RingData`, every band DEGENERATE at its realised delay. -/
def cR (P : RDly) : RingData where
  N := P.N
  R := P.R
  b := P.b
  O := nr P
  req := rqR P
  ack := akR P
  qp := qfR P
  rst := rsR P
  lo := P.d
  hi := P.d
  fl := P.f
  fh := P.f
  wl := P.w
  wh := P.w
  vl := P.v
  vh := P.v
  τ := tauR P

/-- The same run with the given BANDS. -/
def bR (P : RDly) : RingData where
  N := P.N
  R := P.R
  b := P.b
  O := nr P
  req := rqR P
  ack := akR P
  qp := qfR P
  rst := rsR P
  lo := P.lo
  hi := P.hi
  fl := P.fl
  fh := P.fh
  wl := P.wl
  wh := P.wh
  vl := P.vl
  vh := P.vh
  τ := tauR P

theorem tauR_eq (P : RDly) (H0 : 0 < Ring.D P.N P.b) (H1 : Ring.D P.N P.b < P.N) (i j : Nat)
    (hi : i < P.N) :
    tauR P i j = τs ((cR P).On i) (P.d i) (P.d i) ((cR P).ρR i) ((cR P).αR i) j := by
  have hx := Ring.prv_lt hi
  have hy := Ring.nxt_lt hi
  have eX : (if Ring.tok P.N P.b i then
          (if j = 0 then P.R else
            if _h : key P (prv P.N i) (j - 1) < key P i j then
              nt (PR P i) (P.w i) (P.w i) (tauR P (prv P.N i) (j - 1)) (Vph (j - 1)) else 0)
         else
          (if _h : key P (prv P.N i) j < key P i j then
              nt (PR P i) (P.w i) (P.w i) (tauR P (prv P.N i) j) (Vph j) else 0)) =
      (cR P).ρR i j := by
    show _ = cond (Ring.tok P.N P.b i) (ash P.R (ε (PR P i) (P.w i) (P.w i) (tauR P (prv P.N i))))
      (ε (PR P i) (P.w i) (P.w i) (tauR P (prv P.N i))) j
    cases htk : Ring.tok P.N P.b i
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
      rw [dif_pos (key_prv P H0 i j hi htk)]; rfl
    · simp only [↓reduceIte, Bool.cond_true]
      cases j with
      | zero => rfl
      | succ k =>
        rw [if_neg (by omega), dif_pos (key_low P i _ (k + 1) hx (by omega))]
        rfl
  have eY : (if Ring.tok P.N P.b (nxt P.N i) then
          (if _h : key P (nxt P.N i) j < key P i j then
              nt (QR P i) (P.v i) (P.v i) (tauR P (nxt P.N i) j) (Vph j) else 0)
         else
          (if j = 0 then P.R else
            if _h : key P (nxt P.N i) (j - 1) < key P i j then
              nt (QR P i) (P.v i) (P.v i) (tauR P (nxt P.N i) (j - 1)) (Vph (j - 1)) else 0)) =
      (cR P).αR i j := by
    show _ = cond (Ring.tok P.N P.b (nxt P.N i)) (ε (QR P i) (P.v i) (P.v i) (tauR P (nxt P.N i)))
      (ash P.R (ε (QR P i) (P.v i) (P.v i) (tauR P (nxt P.N i)))) j
    cases htk : Ring.tok P.N P.b (nxt P.N i)
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
      cases j with
      | zero => rfl
      | succ k =>
        rw [if_neg (by omega), dif_pos (key_low P i _ (k + 1) hy (by omega))]
        rfl
    · simp only [↓reduceIte, Bool.cond_true]
      rw [dif_pos (key_nxt P H1 i j hi htk)]; rfl
  unfold tauR
  rw [if_pos hi, eX, eY]; rfl

/-! ## The degenerate-band run solves `PRing` -/

structure RPos (P : RDly) : Prop where
  H_D : ∀ i, i < P.N → 1 ≤ P.d i
  H_W : ∀ i, i < P.N → 1 ≤ P.w i
  H_V : ∀ i, i < P.N → 1 ≤ P.v i
  H_TOK : 0 < Ring.D P.N P.b ∧ Ring.D P.N P.b < P.N

theorem stageB_of {c : Bool} {req ack rst O qp : Nat → Bool} {lo hi fl fh d f : Nat}
    (h1 : lo ≤ d) (h2 : d ≤ hi) (hf1 : fl ≤ f) (hf2 : f ≤ fh) (hlp : 1 ≤ lo + fl)
    (hO : ∀ t, d ≤ t → O t = CElemTiming.exc (initOf c) (req (t - d)) (ack (t - d)) (qp (t - d))
      (rst (t - d)))
    (hq : ∀ t, qp (t + f) = O t)
    (hnr : NoRevertI lo hi (fun s => CElemTiming.exc (initOf c) (req s) (ack s) (qp s) (rst s)) O) :
    StageB c req ack rst O qp lo hi fl fh := by
  cases c
  · exact { H_LUT_WIN := fun t ht => ⟨t - d, by omega, by omega, hO t (by omega)⟩
            H_NO_REVERT := hnr
            H_FB := CElemTiming.transport_winDelay hf1 hf2 hq
            H_LOOP_POS := hlp }
  · exact { H_LUT_WIN := fun t ht => ⟨t - d, by omega, by omega, hO t (by omega)⟩
            H_NO_REVERT := hnr
            H_FB := CElemTiming.transport_winDelay hf1 hf2 hq
            H_LOOP_POS := hlp }

theorem wireB_pin (b0 : Bool) (x : Nat → Bool) {d : Nat} (hd : 1 ≤ d) :
    WireB b0 d d x (pinB b0 d x) :=
  ⟨CElemTiming.transport_winDelay (Nat.le_refl d) (Nat.le_refl d) (fun t => by simp [pinB]),
    WinFifoCausal.noRevertI_shift (fun t ht => by simp [pinB, ht]), hd,
    fun t ht => by simp [pinB]; omega⟩

theorem nr_tr (P : RDly) (i : Nat) (hi : i < P.N) (hd : 1 ≤ P.d i) :
    ∀ t, P.d i ≤ t → nr P i t = CElemTiming.exc (initOf (P.b i)) (rqR P i (t - P.d i))
      (akR P i (t - P.d i)) (qfR P i (t - P.d i)) (rsR P (t - P.d i)) := by
  intro t ht; rw [nr_eq P i t hi, if_pos ⟨hd, ht⟩]

theorem qf_shift (P : RDly) (i t : Nat) : qfR P i (t + P.f i) = nr P i t := by
  simp [qfR, pinB]

/-- **The degenerate-band ring run is a solution of `PRing`**, for every `N`, every reset
pattern with `0 < D < N` and every positive delay assignment. -/
theorem ring_c {P : RDly} (H : RPos P) : PRing (cR P) where
  H_RST _ := rfl
  H_STAGE i hi := by
    have hd := H.H_D i hi
    exact stageB_of (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (show 1 ≤ P.d i + P.f i by omega) (nr_tr P i hi hd) (qf_shift P i) (WinFifoCausal.noRevertI_shift (nr_tr P i hi hd))
  H_PWR i hi t ht := by
    show nr P i t = P.b i
    rw [nr_eq P i t hi, if_neg (by have : t < P.d i := ht; omega)]
  H_LUT_POS i hi := H.H_D i hi
  H_WF i hi := wireB_pin _ _ (H.H_W i hi)
  H_WB i hi := wireB_pin _ _ (H.H_V i hi)
  H_TIMES i hi j := tauR_eq P H.H_TOK.1 H.H_TOK.2 i j hi
  H_TOK := by
    obtain ⟨j, hj, ht⟩ := Ring.cnt_pos H.H_TOK.1
    exact ⟨j, hj, ht⟩

/-! ## The bands -/

structure RBand (P : RDly) : Prop where
  H_D : ∀ i, i < P.N → P.lo i ≤ P.d i ∧ P.d i ≤ P.hi i
  H_F : ∀ i, i < P.N → P.fl i ≤ P.f i ∧ P.f i ≤ P.fh i
  H_W : ∀ i, i < P.N → P.wl i ≤ P.w i ∧ P.w i ≤ P.wh i
  H_V : ∀ i, i < P.N → P.vl i ≤ P.v i ∧ P.v i ≤ P.vh i
  H_LUT_POS : ∀ i, i < P.N → 1 ≤ P.lo i
  H_WIRE_POS : ∀ i, i < P.N → 1 ≤ P.wl i ∧ 1 ≤ P.vl i
  /-- C's token/bubble condition on the reset pattern. -/
  H_TOK : 0 < Ring.D P.N P.b ∧ Ring.D P.N P.b < P.N

theorem rpos_of_band {P : RDly} (B : RBand P) : RPos P where
  H_D i hi := by have := B.H_D i hi; have := B.H_LUT_POS i hi; omega
  H_W i hi := by have := B.H_W i hi; have := B.H_WIRE_POS i hi; omega
  H_V i hi := by have := B.H_V i hi; have := B.H_WIRE_POS i hi; omega
  H_TOK := B.H_TOK

theorem ringT_c {P : RDly} (B : RBand P) (T : PRingT (bR P)) : PRingT (cR P) where
  H_RST_LONG i hi := by
    have h0 : P.hi i + P.fh i ≤ P.R := T.H_RST_LONG i hi
    have := B.H_D i hi; have := B.H_F i hi
    show P.d i + P.f i ≤ P.R; omega
  H_LAT i hi := by
    have hi' : i < P.N := hi
    have hx := Ring.prv_lt hi'; have hy := Ring.nxt_lt hi'
    have h0 : P.hi i + P.fh i ≤ P.lo i + min (P.vl (prv P.N i) + P.lo (prv P.N i) + P.wl i)
      (P.wl (nxt P.N i) + P.lo (nxt P.N i) + P.vl i) := T.H_LAT i hi
    have := B.H_D i hi; have := B.H_F i hi; have := B.H_D _ hx; have := B.H_D _ hy
    have := B.H_W i hi; have := B.H_V i hi; have := B.H_W _ hy; have := B.H_V _ hx
    show P.d i + P.f i ≤ P.d i + min (P.v (prv P.N i) + P.d (prv P.N i) + P.w i)
      (P.w (nxt P.N i) + P.d (nxt P.N i) + P.v i)
    omega
  H_WIRE_R i hi := by
    have h0 : P.wh i ≤ P.R ∧ P.vh i ≤ P.R := T.H_WIRE_R i hi
    have := B.H_W i hi; have := B.H_V i hi
    show P.w i ≤ P.R ∧ P.v i ≤ P.R; omega
  H_RT i _ := by
    show P.w i ≤ P.w i + P.d i + P.v (prv P.N i) + P.d (prv P.N i) ∧
      P.v i ≤ P.v i + P.d i + P.w (nxt P.N i) + P.d (nxt P.N i)
    omega

/-- `nt` with any band containing the realised one finds the same edge, also when the
degenerate read missed by one tick (`e j = c + hi + 1` is the not-found value). -/
theorem nt_phase' {x : Nat → Bool} {e : Nat → Nat} (hx : Phases x e) {lo hi c j : Nat}
    (hlo : c + lo ≤ e j) (hhi : e j ≤ c + hi + 1) (hinc : e j < e (j + 1))
    (hprev : ∀ k, j = k + 1 → e k ≤ c + lo) : nt x lo hi c (Vph j) = e j := by
  have hmin : ∀ t, t < e j → (decide (c + lo ≤ t) && (x t == Vph j)) = false := by
    intro t ht
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    by_cases hl : c + lo ≤ t
    · right
      cases j with
      | zero => rw [hx.pre t (by omega)]; decide
      | succ k =>
        have := hprev k rfl
        rw [hx.ph k t (by omega) (by omega), PipeTimed.Vph_succ]; cases Vph k <;> decide
    · left; exact hl
  unfold nt
  rcases Nat.lt_or_ge (e j) (c + hi + 1) with h | h
  · apply WinFifoCausal.lfind_eq _ _ _ h
    · have := hx.ph j (e j) (Nat.le_refl _) hinc
      rw [this]; simp; omega
    · exact hmin
  · have hle := PipeTimed.lfind_le (fun t => decide (c + lo ≤ t) && (x t == Vph j)) (c + hi + 1)
    rcases Nat.lt_or_ge (PipeTimed.lfind (fun t => decide (c + lo ≤ t) && (x t == Vph j))
      (c + hi + 1)) (c + hi + 1) with h' | h'
    · have := PipeTimed.lfind_spec _ _ h'
      rw [hmin _ (by omega)] at this; cases this
    · omega

/-- A transport read of delay `d ∈ [lo, hi]` whose OUTPUT (normalised by `cb`) is a clean
step signal with edges more than the spread apart satisfies H_NO_REVERT of the band: its
input is then the same step signal shifted back by `d`. -/
theorem noRevertI_tr {x y : Nat → Bool} (cb : Bool) {lo hi d : Nat} {e : Nat → Nat}
    (h1 : lo ≤ d) (h2 : d ≤ hi) (hy : ∀ t, d ≤ t → y t = x (t - d)) (hph : Phases (xr cb y) e)
    (h0 : d < e 0) (hsp : ∀ j, e j + hi < e (j + 1) + lo) : NoRevertI lo hi x y := by
  have hy' : ∀ t, d ≤ t → xr cb y t = xr cb x (t - d) := fun t ht => by
    unfold xr; rw [hy t ht]
  have hge : ∀ j, d < e j := by
    intro j; induction j with
    | zero => exact h0
    | succ j ih => have := hsp j; omega
  have hc := WinFifoCausal.clean_of_phases (x := xr cb x) (c := fun j => e j - d) (lo := lo) (hi := hi)
    (by show 1 ≤ e 0 - d; omega)
    (fun s hs => by
      have := hy' (s + d) (by omega); rw [Nat.add_sub_cancel] at this
      rw [← this]; exact hph.pre _ (by have : s < e 0 - d := hs; omega))
    (fun j s hs1 hs2 => by
      have := hy' (s + d) (by omega); rw [Nat.add_sub_cancel] at this
      have a : e j - d ≤ s := hs1; have b : s < e (j + 1) - d := hs2
      have g1 := hge j; have g2 := hge (j + 1)
      rw [← this]; exact hph.ph j _ (by omega) (by omega))
    (fun j => by
      have := hsp j; have := hge j; have := hge (j + 1)
      show e j - d + hi < e (j + 1) - d + lo; omega) (by omega)
  have hn : NoRevertI lo hi (xr cb x) (xr cb y) :=
    WinFifoCausal.noRevertI_of_ret hc.1 hc.2 (EdgeTimes.bRet lo hi d h1 h2) rfl rfl
      (fun t ht => hy' t (by omega))
  cases cb
  · exact hn
  · have := RingPhys.nr_neg hn
    have e1 : ∀ z : Nat → Bool, xr true (xr true z) = z := fun z => funext fun t => by
      simp [xr]
    rw [e1, e1] at this; exact this

theorem xr_false_iff {c : Bool} {x : Nat → Bool} {t : Nat} (h : xr c x t = false) : x t = c := by
  unfold xr at h; cases c <;> cases hx : x t <;> simp_all

theorem pinPhases (b0 : Bool) {x : Nat → Bool} {e : Nat → Nat} (w : Nat) (hx : Phases (xr b0 x) e) :
    Phases (xr b0 (pinB b0 w x)) (fun j => e j + w) := by
  have hb : ∀ t, w ≤ t → xr b0 (pinB b0 w x) t = xr b0 x (t - w) := fun t ht => by
    simp [xr, pinB, ht]
  refine ⟨fun s hs => ?_, fun j s h1 h2 => ?_⟩
  · by_cases h : w ≤ s
    · rw [hb s h]; exact hx.pre _ (by omega)
    · cases b0 <;> simp [xr, pinB, h]
  · rw [hb s (by omega)]; exact hx.ph j _ (by omega) (by omega)

section band
variable {P : RDly} (B : RBand P) (T : PRingT (bR P))
include B T
set_option linter.unusedSectionVars false

theorem rC : PRing (cR P) := ring_c (rpos_of_band B)
theorem rT : PRingT (cR P) := ringT_c B T

theorem rnodes (i : Nat) (hi : i < P.N) : Phases (OnR P i) (tauR P i) :=
  ring_nodes (rC B T) (rT B T) i hi

theorem rinc (i : Nat) (hi : i < P.N) (j : Nat) : tauR P i j < tauR P i (j + 1) :=
  RingPhys.r_inc (rC B T) i hi j

theorem rgeR (i : Nat) (hi : i < P.N) (j : Nat) : P.R < tauR P i j :=
  RingPhys.r_geR (rC B T) i hi j

theorem εF_c (i : Nat) (hi : i < P.N) (j : Nat) :
    (cR P).εF i j = tauR P (prv P.N i) j + P.w i := by
  have hx := Ring.prv_lt hi
  show nt (PR P i) (P.w i) (P.w i) (tauR P (prv P.N i) j) (Vph j) = _
  apply nt_eq _ (Nat.le_refl _)
  have := (pinPhases (P.b (prv P.N i)) (P.w i) (rnodes B T _ hx)).ph j
    (tauR P (prv P.N i) j + P.w i) (Nat.le_refl _) (by have := rinc B T _ hx j; omega)
  exact this

theorem εB_c (i : Nat) (hi : i < P.N) (j : Nat) :
    (cR P).εB i j = tauR P (nxt P.N i) j + P.v i := by
  have hy := Ring.nxt_lt hi
  show nt (QR P i) (P.v i) (P.v i) (tauR P (nxt P.N i) j) (Vph j) = _
  apply nt_eq _ (Nat.le_refl _)
  have := (pinPhases (P.b (nxt P.N i)) (P.v i) (rnodes B T _ hy)).ph j
    (tauR P (nxt P.N i) j + P.v i) (Nat.le_refl _) (by have := rinc B T _ hy j; omega)
  exact this

theorem εF_b (i : Nat) (hi : i < P.N) : (bR P).εF i = (cR P).εF i := by
  funext j
  have hx := Ring.prv_lt hi
  rw [εF_c B T i hi j]
  show nt (PR P i) (P.wl i) (P.wh i) (tauR P (prv P.N i) j) (Vph j) = _
  have hw := B.H_W i hi
  apply EdgeTimes.nt_phase (pinPhases (P.b (prv P.N i)) (P.w i) (rnodes B T _ hx)) hw.1 hw.2 rfl
  · have := rinc B T _ hx j; show _ + _ < _ + _; omega
  · intro k hk; subst hk
    have h1 : tauR P (prv P.N i) k + (cR P).RTF i ≤ tauR P (prv P.N i) (k + 1) :=
      RingPhys.r_spF (rC B T) i hi k
    have : (cR P).RTF i = P.w i + P.d i + P.v (prv P.N i) + P.d (prv P.N i) := rfl
    show tauR P (prv P.N i) k + P.w i ≤ tauR P (prv P.N i) (k + 1) + P.wl i
    omega

theorem εB_b (i : Nat) (hi : i < P.N) : (bR P).εB i = (cR P).εB i := by
  funext j
  have hy := Ring.nxt_lt hi
  rw [εB_c B T i hi j]
  show nt (QR P i) (P.vl i) (P.vh i) (tauR P (nxt P.N i) j) (Vph j) = _
  have hv := B.H_V i hi
  apply EdgeTimes.nt_phase (pinPhases (P.b (nxt P.N i)) (P.v i) (rnodes B T _ hy)) hv.1 hv.2 rfl
  · have := rinc B T _ hy j; show _ + _ < _ + _; omega
  · intro k hk; subst hk
    have h1 : tauR P (nxt P.N i) k + (cR P).RTB i ≤ tauR P (nxt P.N i) (k + 1) :=
      RingPhys.r_spB (rC B T) i hi k
    have : (cR P).RTB i = P.v i + P.d i + P.w (nxt P.N i) + P.d (nxt P.N i) := rfl
    show tauR P (nxt P.N i) k + P.v i ≤ tauR P (nxt P.N i) (k + 1) + P.vl i
    omega

theorem ρR_b (i : Nat) (hi : i < P.N) : (bR P).ρR i = (cR P).ρR i := by
  show cond _ (ash P.R ((bR P).εF i)) ((bR P).εF i) = cond _ (ash P.R ((cR P).εF i)) ((cR P).εF i)
  rw [εF_b B T i hi]; rfl

theorem αR_b (i : Nat) (hi : i < P.N) : (bR P).αR i = (cR P).αR i := by
  show cond _ ((bR P).εB i) (ash P.R ((bR P).εB i)) = cond _ ((cR P).εB i) (ash P.R ((cR P).εB i))
  rw [εB_b B T i hi]; rfl

/-- Node spacing above the LUT spread (from the derived departure bound `r_snd`). -/
theorem rsp (i : Nat) (hi : i < P.N) (j : Nat) :
    tauR P i j + P.hi i < tauR P i (j + 1) + P.lo i := by
  have hx := Ring.prv_lt hi; have hy := Ring.nxt_lt hi
  have a : tauR P i j + (cR P).Es i ≤ (cR P).ρR i (j + 1) := RingPhys.r_snd (rC B T) i hi j
  have b : (cR P).ρR i (j + 1) + P.d i ≤ tauR P i (j + 1) := RingPhys.t_ρ (rC B T) i hi (j + 1)
  have e : (cR P).Es i = P.v (prv P.N i) + P.d (prv P.N i) + P.w i := rfl
  have h0 : P.hi i + P.fh i ≤ P.lo i + min (P.vl (prv P.N i) + P.lo (prv P.N i) + P.wl i)
      (P.wl (nxt P.N i) + P.lo (nxt P.N i) + P.vl i) := T.H_LAT i hi
  have := B.H_D i hi; have := B.H_D _ hx; have := B.H_W i hi; have := B.H_V _ hx
  have := (rpos_of_band B).H_D i hi
  omega

/-- **The ring run with the given bands is a solution of `PRing`.** -/
theorem ring_b : PRing (bR P) where
  H_RST _ := rfl
  H_STAGE i hi := by
    have hd := (rpos_of_band B).H_D i hi
    have hb := B.H_D i hi; have hf := B.H_F i hi; have hl := B.H_LUT_POS i hi
    have hR : P.hi i + P.fh i ≤ P.R := T.H_RST_LONG i hi
    exact stageB_of hb.1 hb.2 hf.1 hf.2 (show 1 ≤ P.lo i + P.fl i by omega) (nr_tr P i hi hd)
      (qf_shift P i)
      (noRevertI_tr (P.b i) hb.1 hb.2 (nr_tr P i hi hd) (rnodes B T i hi)
        (by have := rgeR B T i hi 0; omega) (rsp B T i hi))
  H_PWR i hi t ht := by
    have hR : P.hi i + P.fh i ≤ P.R := T.H_RST_LONG i hi
    have := rgeR B T i hi 0
    have ht' : t < P.hi i := ht
    exact xr_false_iff ((rnodes B T i hi).pre t (by omega))
  H_LUT_POS i hi := B.H_LUT_POS i hi
  H_WF i hi := by
    have hi' : i < P.N := hi
    have hx := Ring.prv_lt hi'
    have hw := B.H_W i hi
    have hWR : P.wh i ≤ P.R ∧ P.vh i ≤ P.R := T.H_WIRE_R i hi
    have g0 := rgeR B T _ hx 0
    have hy : ∀ t, P.w i ≤ t → rqR P i t = nr P (prv P.N i) (t - P.w i) := fun t ht => by
      simp [rqR, pinB, ht]
    refine ⟨CElemTiming.transport_winDelay hw.1 hw.2 (fun t => by
        show rqR P i (t + P.w i) = nr P (prv P.N i) t; simp [rqR, pinB]),
      noRevertI_tr (P.b (prv P.N i)) hw.1 hw.2 hy (pinPhases _ (P.w i) (rnodes B T _ hx))
        (by show P.w i < tauR P (prv P.N i) 0 + P.w i; omega) (fun j => ?_),
      (B.H_WIRE_POS i hi).1, fun t ht => ?_⟩
    · have h1 : tauR P (prv P.N i) j + (cR P).RTF i ≤ tauR P (prv P.N i) (j + 1) :=
        RingPhys.r_spF (rC B T) i hi j
      have h2 : P.wh i ≤ (bR P).RTF i ∧ P.vh i ≤ (bR P).RTB i := T.H_RT i hi
      have e1 : (cR P).RTF i = P.w i + P.d i + P.v (prv P.N i) + P.d (prv P.N i) := rfl
      have e2 : (bR P).RTF i = P.wl i + P.lo i + P.vl (prv P.N i) + P.lo (prv P.N i) := rfl
      have := B.H_D i hi; have := B.H_D _ hx; have := B.H_V _ hx
      have := (B.H_WIRE_POS i hi).1
      show tauR P (prv P.N i) j + P.w i + P.wh i < tauR P (prv P.N i) (j + 1) + P.w i + P.wl i
      omega
    · show rqR P i t = P.b (prv P.N i)
      have ht' : t < P.wh i := ht
      unfold rqR pinB; split
      · exact xr_false_iff ((rnodes B T _ hx).pre _ (by omega))
      · rfl
  H_WB i hi := by
    have hi' : i < P.N := hi
    have hy' := Ring.nxt_lt hi'
    have hv := B.H_V i hi
    have hWR : P.wh i ≤ P.R ∧ P.vh i ≤ P.R := T.H_WIRE_R i hi
    have g0 := rgeR B T _ hy' 0
    have hy : ∀ t, P.v i ≤ t → akR P i t = nr P (nxt P.N i) (t - P.v i) := fun t ht => by
      simp [akR, pinB, ht]
    refine ⟨CElemTiming.transport_winDelay hv.1 hv.2 (fun t => by
        show akR P i (t + P.v i) = nr P (nxt P.N i) t; simp [akR, pinB]),
      noRevertI_tr (P.b (nxt P.N i)) hv.1 hv.2 hy (pinPhases _ (P.v i) (rnodes B T _ hy'))
        (by show P.v i < tauR P (nxt P.N i) 0 + P.v i; omega) (fun j => ?_),
      (B.H_WIRE_POS i hi).2, fun t ht => ?_⟩
    · have h1 : tauR P (nxt P.N i) j + (cR P).RTB i ≤ tauR P (nxt P.N i) (j + 1) :=
        RingPhys.r_spB (rC B T) i hi j
      have h2 : P.wh i ≤ (bR P).RTF i ∧ P.vh i ≤ (bR P).RTB i := T.H_RT i hi
      have e1 : (cR P).RTB i = P.v i + P.d i + P.w (nxt P.N i) + P.d (nxt P.N i) := rfl
      have e2 : (bR P).RTB i = P.vl i + P.lo i + P.wl (nxt P.N i) + P.lo (nxt P.N i) := rfl
      have := B.H_D i hi; have := B.H_D _ hy'; have := B.H_W _ hy'
      have := (B.H_WIRE_POS i hi).2
      show tauR P (nxt P.N i) j + P.v i + P.vh i < tauR P (nxt P.N i) (j + 1) + P.v i + P.vl i
      omega
    · show akR P i t = P.b (nxt P.N i)
      have ht' : t < P.vh i := ht
      unfold akR pinB; split
      · exact xr_false_iff ((rnodes B T _ hy').pre _ (by omega))
      · rfl
  H_TIMES i hi j := by
    have hi' : i < P.N := hi
    show tauR P i j = τs (OnR P i) (P.lo i) (P.hi i) ((bR P).ρR i) ((bR P).αR i) j
    rw [ρR_b B T i hi, αR_b B T i hi]
    have hb := B.H_D i hi
    have e := tauR_eq P B.H_TOK.1 B.H_TOK.2 i j hi
    have l1 := nt_lo (OnR P i) (cph ((cR P).ρR i) ((cR P).αR i) j) (Vph j) (Nat.le_refl (P.d i))
      (hi := P.d i)
    have l2 := PipeTimed.lfind_le
      (fun t => decide (cph ((cR P).ρR i) ((cR P).αR i) j + P.d i ≤ t) && (OnR P i t == Vph j))
      (cph ((cR P).ρR i) ((cR P).αR i) j + P.d i + 1)
    have e' : tauR P i j = nt (OnR P i) (P.d i) (P.d i) (cph ((cR P).ρR i) ((cR P).αR i) j) (Vph j) := e
    unfold τs
    rw [nt_phase' (rnodes B T i hi) (by rw [e']; omega) (by rw [e']; unfold nt; omega)
      (rinc B T i hi j) (fun k hk => ?_)]
    subst hk
    have a : tauR P i k + (cR P).Es i ≤ (cR P).ρR i (k + 1) := RingPhys.r_snd (rC B T) i hi k
    have : (cR P).ρR i (k + 1) ≤ cph ((cR P).ρR i) ((cR P).αR i) (k + 1) := Nat.le_max_left _ _
    omega
  H_TOK := (rC B T).H_TOK

end band

/-! ## Headline theorems -/

/-- **Existence of solutions of the ring's edge-time equations.** For every `N`, every reset
pattern `b` with `0 < D < N` (C's condition, `RBand.H_TOK`), and every assignment of
realised constant delays inside the bands (`RBand`) satisfying the timing rows `PRingT` on
the BANDS, the run `nr P` (real `bd_c2n`/`bd_c2n_set` INITs, each gate a transport delay)
with the edge times `tauR P` (defined for EVERY stage and EVERY edge index by the
well-founded recurrence of `H_TIMES`) satisfies every field of `PRing` and `PRingT`. -/
theorem ring_solution (P : RDly) (B : RBand P) (T : PRingT (bR P)) :
    PRing (bR P) ∧ PRingT (bR P) ∧
    ∀ i, i < P.N → ∀ j, tauR P i j =
      nt (OnR P i) (P.d i) (P.d i) (cph ((cR P).ρR i) ((cR P).αR i) j) (Vph j) :=
  ⟨ring_b B T, T, fun i hi j => tauR_eq P B.H_TOK.1 B.H_TOK.2 i j hi⟩

theorem ring_exists (P : RDly) (B : RBand P) (T : PRingT (bR P)) :
    ∃ D : RingData, D.N = P.N ∧ D.R = P.R ∧ D.b = P.b ∧ D.lo = P.lo ∧ D.hi = P.hi ∧
      D.fl = P.fl ∧ D.fh = P.fh ∧ D.wl = P.wl ∧ D.wh = P.wh ∧ D.vl = P.vl ∧ D.vh = P.vh ∧
      PRing D ∧ PRingT D :=
  ⟨bR P, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ring_b B T, T⟩

/-- Uniform witness delays for ANY ring: LUT band `[1, 3]`, realised `1 + i % 3`, feedback
and wires 1, reset 4. -/
def wR (N : Nat) (b : Nat → Bool) : RDly where
  N := N
  R := 4
  b := b
  lo _ := 1
  hi _ := 3
  fl _ := 1
  fh _ := 1
  wl _ := 1
  wh _ := 1
  vl _ := 1
  vh _ := 1
  d i := 1 + i % 3
  f _ := 1
  w _ := 1
  v _ := 1

theorem wR_band (N : Nat) (b : Nat → Bool) (h0 : 0 < Ring.D N b) (h1 : Ring.D N b < N) :
    RBand (wR N b) where
  H_D i _ := by show 1 ≤ 1 + i % 3 ∧ 1 + i % 3 ≤ 3; omega
  H_F _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  H_W _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  H_V _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  H_LUT_POS _ _ := Nat.le_refl 1
  H_WIRE_POS _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  H_TOK := ⟨h0, h1⟩

theorem wR_T (N : Nat) (b : Nat → Bool) : PRingT (bR (wR N b)) where
  H_RST_LONG _ _ := by show 3 + 1 ≤ 4; decide
  H_LAT _ _ := by show 3 + 1 ≤ 1 + min (1 + 1 + 1) (1 + 1 + 1); decide
  H_WIRE_R _ _ := by show 1 ≤ 4 ∧ 1 ≤ 4; decide
  H_RT _ _ := by show 1 ≤ 1 + 1 + 1 + 1 ∧ 1 ≤ 1 + 1 + 1 + 1; decide

/-- **Non-vacuity of `ring_solution` for every ring and every reset pattern with
`0 < D < N`**: its hypotheses hold jointly (H_LAT met with equality on the bands, realised
LUT delays spread over the whole band). -/
theorem ring_solution_witness (N : Nat) (b : Nat → Bool) (h0 : 0 < Ring.D N b)
    (h1 : Ring.D N b < N) :
    RBand (wR N b) ∧ PRingT (bR (wR N b)) ∧
    (∀ i, (bR (wR N b)).hi i + (bR (wR N b)).fh i =
      (bR (wR N b)).lo i + min ((bR (wR N b)).Es i) ((bR (wR N b)).Ea i)) :=
  ⟨wR_band N b h0 h1, wR_T N b, fun _ => rfl⟩

/-- **The converse of `RingPhys.ring_cond`, closing RingPhys's open item**: a ring of `N`
stages with reset pattern `b` has a run satisfying `PRing` and `PRingT` (some delays in some
bands) IF AND ONLY IF `0 < D < N` (C's token/bubble condition; it implies `N ≥ 3`). -/
theorem ring_run_iff (N : Nat) (b : Nat → Bool) :
    (∃ D : RingData, D.N = N ∧ D.b = b ∧ PRing D ∧ PRingT D) ↔
      (0 < Ring.D N b ∧ Ring.D N b < N) := by
  constructor
  · rintro ⟨D, hN, hb, C, T⟩
    have := RingPhys.ring_cond C T
    subst hN; subst hb; exact ⟨this.2.1, this.2.2⟩
  · rintro ⟨h0, h1⟩
    exact ⟨bR (wR N b), rfl, rfl, ring_b (wR_band N b h0 h1) (wR_T N b), wR_T N b⟩

/-- **C's reset rings, physically realised, every `N ≥ 3` and every `0 < K < N`**: the run
exists and (by `RingPhys.ring_reset_live`) circulates forever with one loop token. -/
theorem ring_reset_exists (N K : Nat) (hK0 : 0 < K) (hKn : K < N) (hN : 3 ≤ N) :
    PRing (bR (wR N (Ring.resetState K))) ∧ PRingT (bR (wR N (Ring.resetState K))) ∧
    (∀ i, i < N → ∀ j, tauR (wR N (Ring.resetState K)) i j <
      tauR (wR N (Ring.resetState K)) i (j + 1)) ∧
    (∀ t, Ring.D N (RingPhys.st (bR (wR N (Ring.resetState K))) t) = 2) := by
  have hD := Ring.D_reset (n := N) hK0 hKn
  have C := ring_b (wR_band N (Ring.resetState K) (by omega) (by omega)) (wR_T N _)
  have L := RingPhys.ring_reset_live C (wR_T N _) K hK0 hKn rfl
  exact ⟨C, wR_T N _, fun i hi j => (L.2.1 i hi j).1, L.2.2⟩

end Formal.Cells.EdgeTimesRing
