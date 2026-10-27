import Formal.Cells.Prelim
import Formal.Cells.CElemTiming
import Formal.Core.Delay.Pure
import Formal.Core.Delay.Inertial
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Track 5, probe 5d: the `bd_c2` loop on shard A's continuous-time channels

The cell is `bd_c2` (`cells/rtl/bd_ce.v`, INIT `0x00E800E800E800E8`, pins
`I0=a I1=b I2=q I3=rst`), evaluated through `Prelim.lutB` via
`CElemTiming.exc` (the INIT is proved equal to `~rst·maj(a,b,q)` there).
Time is `ℝ`, signals `ℝ → Bool`.

1. **Pure (FIFO, bounded) channels** (`Formal.Core.Delay.Pure.Chan`): 5b's
   results restated: (a) `c2_follow_hold`, `c2_reset`; (b) `runt_loopR`,
   `runt_oscillatesR`; (c) `c2_four_phase`.
2. **Inertial LUT** (`Formal.Core.Delay.Inertial.InertialRD ρ dl`) plus a
   fixed wire `dw`, loop delay `D = dl + dw`. The loop is deterministic
   (`inLoop_unique`), and a runt of width `w` on `b` (with `a = 1`) is
   * lost if `w < ρ` (`inertial_lost`),
   * circulates forever if `ρ ≤ w ≤ D - ρ` (`inertial_circulates`),
   * latches if `ρ ≤ w` and `D - ρ < w` (`inertial_latches`).
   So "`ρ ≤ w < D` circulates" is FALSE on `(D - ρ, D)`
   (`runt_below_D_can_latch`), and if `2ρ > D` no width circulates.
3. **Involution channel** (Fuegger/Najvirt/Nowak/Schmid), defined minimally
   here (`InvCh`) on transition sequences: the loop's output transitions obey
   `o (n+2) = o n + δ_n (o n - o (n+1))`. There is a runt width that makes the
   loop oscillate FOREVER (`inv_eternal`, by connectedness of an interval
   split into the open "lost" and "latched" sets), and on such an orbit the
   output keeps switching after any time bound (`osc_unbounded`): no bounded
   resolution time.
-/

namespace Formal.Cells.CElemCore
open Formal.Cells
open Formal.Core
open Formal.Cells.CElemTiming (exc INIT_c2 c2_eq)
open Formal.Core.DelayPure (Chan Retime)
open Formal.Core.DelayInertial (InertialRD Filt FiltAt Stable NoShort filtAt_unique
  inertialRD_of_noShort inertialRD_of_filt inertialRD_pulse_short_exists shift)

abbrev Sig := ℝ → Bool

/-- Archimedean helper: every real is exceeded by some multiple of `D > 0`. -/
theorem exists_mul_gt {D : ℝ} (hD : 0 < D) (x : ℝ) : ∃ n : ℕ, x < n * D := by
  obtain ⟨n, hn⟩ := Archimedean.arch x hD
  refine ⟨n + 1, ?_⟩
  rw [nsmul_eq_mul] at hn
  push_cast
  linarith

/-- Excitation of the LUT: its Boolean function of the current pin values. -/
def excR (init : Nat) (a b rst qp : Sig) : Sig := fun t => exc init (a t) (b t) (qp t) (rst t)

/-- With `a = 1`, `rst = 0`, `bd_c2` computes `b ∨ q` (an OR storage loop). -/
theorem exc_or (b q : Bool) : exc INIT_c2 true b q false = (b || q) := by
  rw [c2_eq]; cases b <;> cases q <;> rfl

/-! ## 1. Pure-delay loop -/

/-- **The gate relations of one feedback-LUT cell, continuous time.** -/
structure LoopR (init : Nat) (a b rst O qp : Sig) (dlmin dlmax dwmin dwmax : ℝ) : Prop where
  /-- **H_LUT**: `O` is a FIFO bounded pure delay `[dlmin, dlmax]` of the
  excitation (prjxray-db LUT `I*->O` fast-min/slow-max; test: GLS of a lone
  LUT at SDF corners, board ring oscillator). -/
  H_LUT : Chan dlmin dlmax (excR init a b rst qp) O
  /-- **H_FB**: the routed feedback wire `O -> I2`, FIFO bounded delay
  `[dwmin, dwmax]` (SDF `INTERCONNECT` of net `q` in `cells/gls/`, >= 4 seeds). -/
  H_FB : Chan dwmin dwmax O qp
  /-- **H_LOOP_POS**: the loop has strictly positive minimum delay. -/
  H_LOOP_POS : 0 < dlmin + dwmin
  /-- **H_CAUSAL**: no channel answers before its input (non-negative lower
  bounds). In `ℕ` (5b) this was free; in `ℝ` it must be stated. -/
  H_CAUSAL : 0 ≤ dlmin ∧ 0 ≤ dwmin

section generic
variable {init : Nat} {a b rst O qp : Sig} {dlmin dlmax dwmin dwmax : ℝ}

/-- **Forced, then held** (any INIT). Half-open windows. Proof: induction
on `n` over the windows `[t0, t0 + Dmax + n·Dmin)`, then Archimedes. -/
theorem exc_held (L : LoopR init a b rst O qp dlmin dlmax dwmin dwmax) (v : Bool) (t0 t2 : ℝ)
    (hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, exc init (a s) (b s) q (rst s) = v)
    (hfix : ∀ s, t0 ≤ s → s < t2 → exc init (a s) (b s) v (rst s) = v) :
    ∀ s, t0 ≤ s → s < t2 → excR init a b rst qp s = v := by
  obtain ⟨r1, e1⟩ := L.H_LUT
  obtain ⟨r2, e2⟩ := L.H_FB
  have hpos := L.H_LOOP_POS
  have key : ∀ n : ℕ, ∀ s, t0 ≤ s → s < t2 →
      s < t0 + (dlmax + dwmax) + n * (dlmin + dwmin) → excR init a b rst qp s = v := by
    intro n
    induction n with
    | zero =>
      intro s h0 _ h
      exact hforce s h0 (by simpa using h) _
    | succ n ih =>
      intro s h0 h2 h
      by_cases hlt : s < t0 + (dlmax + dwmax)
      · exact hforce s h0 hlt _
      · have hq : qp s = v := by
          rw [e2 s, e1 (r2.σ s)]
          have g1 := r1.ge (r2.σ s); have l1 := r1.le (r2.σ s)
          have g2 := r2.ge s; have l2 := r2.le s
          push_cast at h
          exact ih _ (by linarith) (by linarith) (by linarith)
        show exc init (a s) (b s) (qp s) (rst s) = v
        rw [hq]; exact hfix s h0 h2
  intro s h0 h2
  have g1 := r1.ge s; have l1 := r1.le s
  have g2 := r2.ge s; have l2 := r2.le s
  obtain ⟨n, hn⟩ := exists_mul_gt hpos (s - t0)
  exact key n s h0 h2 (by linarith)

theorem O_held (L : LoopR init a b rst O qp dlmin dlmax dwmin dwmax) (v : Bool) (t0 t2 : ℝ)
    (hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, exc init (a s) (b s) q (rst s) = v)
    (hfix : ∀ s, t0 ≤ s → s < t2 → exc init (a s) (b s) v (rst s) = v) :
    ∀ t, t0 + dlmax ≤ t → t < t2 + dlmin → O t = v := by
  intro t h1 h2
  obtain ⟨r1, e1⟩ := L.H_LUT
  rw [e1 t]
  have := r1.ge t; have := r1.le t
  exact exc_held L v t0 t2 hforce hfix _ (by linarith) (by linarith)

theorem qp_held (L : LoopR init a b rst O qp dlmin dlmax dwmin dwmax) (v : Bool) (t0 t2 : ℝ)
    (hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, exc init (a s) (b s) q (rst s) = v)
    (hfix : ∀ s, t0 ≤ s → s < t2 → exc init (a s) (b s) v (rst s) = v) :
    ∀ t, t0 + (dlmax + dwmax) ≤ t → t < t2 + (dlmin + dwmin) → qp t = v := by
  intro t h1 h2
  obtain ⟨r2, e2⟩ := L.H_FB
  rw [e2 t]
  have := r2.ge t; have := r2.le t
  exact O_held L v t0 t2 hforce hfix _ (by linarith) (by linarith)

end generic

section c2
variable {a b rst O qp : Sig} {dlmin dlmax dwmin dwmax : ℝ}

/-- **(a) Follow-and-hold for `bd_c2`**, continuous time. `H_PULSE`: `a = b = v`,
`rst = 0` on `[t0, t0 + Dmax)`; `H_NORST`: `rst = 0` on `[t0, t2)`;
`H_NOT_BOTH`: on `[t0, t2)` one input is `v`. Then `O = v` on
`[t0 + dlmax, t2 + dlmin)` and `qp = v` on `[t0 + Dmax, t2 + Dmin)`. -/
theorem c2_follow_hold (L : LoopR INIT_c2 a b rst O qp dlmin dlmax dwmin dwmax)
    (v : Bool) (t0 t2 : ℝ)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → a s = v ∧ b s = v ∧ rst s = false)
    (H_NORST : ∀ s, t0 ≤ s → s < t2 → rst s = false)
    (H_NOT_BOTH : ∀ s, t0 ≤ s → s < t2 → a s = v ∨ b s = v) :
    (∀ t, t0 + dlmax ≤ t → t < t2 + dlmin → O t = v) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t < t2 + (dlmin + dwmin) → qp t = v) := by
  have hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
      ∀ q, exc INIT_c2 (a s) (b s) q (rst s) = v := by
    intro s h1 h2 q
    obtain ⟨ha, hb, hr⟩ := H_PULSE s h1 h2
    rw [c2_eq, ha, hb, hr]; cases v <;> cases q <;> rfl
  have hfix : ∀ s, t0 ≤ s → s < t2 → exc INIT_c2 (a s) (b s) v (rst s) = v := by
    intro s h1 h2
    rw [c2_eq, H_NORST s h1 h2]
    rcases H_NOT_BOTH s h1 h2 with h | h <;> rw [h] <;> cases v <;> cases a s <;> cases b s <;> rfl
  exact ⟨O_held L v t0 t2 hforce hfix, qp_held L v t0 t2 hforce hfix⟩

/-- **Reset of `bd_c2`**, continuous time. -/
theorem c2_reset (L : LoopR INIT_c2 a b rst O qp dlmin dlmax dwmin dwmax) (t0 t2 : ℝ)
    (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → rst s = true)
    (H_RELEASE : ∀ s, t0 ≤ s → s < t2 → a s = false ∨ b s = false) :
    (∀ t, t0 + dlmax ≤ t → t < t2 + dlmin → O t = false) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t < t2 + (dlmin + dwmin) → qp t = false) := by
  have hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
      ∀ q, exc INIT_c2 (a s) (b s) q (rst s) = false := by
    intro s h1 h2 q
    rw [c2_eq, H_RST_PULSE s h1 h2]; rfl
  have hfix : ∀ s, t0 ≤ s → s < t2 → exc INIT_c2 (a s) (b s) false (rst s) = false := by
    intro s h1 h2
    rw [c2_eq]
    rcases H_RELEASE s h1 h2 with h | h <;> rw [h] <;> cases a s <;> cases b s <;> cases rst s <;> rfl
  exact ⟨O_held L false t0 t2 hforce hfix, qp_held L false t0 t2 hforce hfix⟩

/-- **(c) Four-phase correctness of `bd_c2`**, continuous time; hypotheses as
in 5b (`CElemTiming.c2_four_phase`), with half-open windows. Conclusion: for
every phase `k`, `O = V k` on `[c k + dlmax, c (k+1) + dlmin)` and
`qp = V k` on `[c k + Dmax, c (k+1) + Dmin)`. -/
theorem c2_four_phase (L : LoopR INIT_c2 a b rst O qp dlmin dlmax dwmin dwmax)
    (V : ℕ → Bool) (c : ℕ → ℝ) (E : ℝ)
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_ORDER : ∀ k, c k < c (k + 1))
    (H_BOTH : ∀ k, a (c k) = V k ∧ b (c k) = V k)
    (H_NEXT : ∀ k s, c k ≤ s → s < c (k + 1) → a s = V k ∨ b s = V k)
    (H_NORST : ∀ s, c 0 ≤ s → rst s = false)
    (H_ACK : ∀ k s, c k ≤ s → (a s ≠ V k ∨ b s ≠ V k) →
        ∃ u, c k ≤ u ∧ u + E ≤ s ∧ O u = V k)
    (H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E)
    (H_RESET_DONE : ∀ u, c 0 ≤ u → u < c 0 + dlmin → O u = !V 0) :
    ∀ k, (∀ t, c k + dlmax ≤ t → t < c (k + 1) + dlmin → O t = V k) ∧
         (∀ t, c k + (dlmax + dwmax) ≤ t → t < c (k + 1) + (dlmin + dwmin) → qp t = V k) := by
  have hmono : ∀ k, c 0 ≤ c k := by
    intro k
    induction k with
    | zero => exact le_refl _
    | succ k ih => exact le_trans ih (le_of_lt (H_ORDER k))
  obtain ⟨hc1, hc2⟩ := L.H_CAUSAL
  have hb2 : dwmin ≤ dwmax := by
    obtain ⟨r2, _⟩ := L.H_FB
    have := r2.ge 0; have := r2.le 0
    linarith
  have step : ∀ k, (∀ u, c k ≤ u → u < c k + dlmin → O u = !V k) →
      (∀ t, c k + dlmax ≤ t → t < c (k + 1) + dlmin → O t = V k) ∧
      (∀ t, c k + (dlmax + dwmax) ≤ t → t < c (k + 1) + (dlmin + dwmin) → qp t = V k) ∧
      c k + (dlmax + dwmax) ≤ c (k + 1) := by
    intro k R
    have arrive : ∀ s, c k ≤ s → s < c k + (dlmax + dwmax) → a s = V k ∧ b s = V k := by
      intro s h1 h2
      by_cases hd : a s ≠ V k ∨ b s ≠ V k
      · obtain ⟨u, hu1, hu2, hu3⟩ := H_ACK k s h1 hd
        have := R u hu1 (by linarith)
        rw [hu3] at this
        cases hv : V k <;> simp [hv] at this
      · simp only [ne_eq, not_or, Decidable.not_not] at hd
        exact hd
    have hgap : c k + (dlmax + dwmax) ≤ c (k + 1) := by
      by_contra hlt
      push Not at hlt
      have h1 := arrive (c (k + 1)) (le_of_lt (H_ORDER k)) hlt
      have h2 := H_BOTH (k + 1)
      rw [H_ALT k, h1.1] at h2
      cases hv : V k <;> simp [hv] at h2
    have hnr : ∀ s, c k ≤ s → rst s = false := fun s hs => H_NORST s (le_trans (hmono k) hs)
    have res := c2_follow_hold L (V k) (c k) (c (k + 1))
      (fun s h1 h2 => ⟨(arrive s h1 h2).1, (arrive s h1 h2).2, hnr s h1⟩)
      (fun s h1 _ => hnr s h1)
      (fun s h1 h2 => H_NEXT k s h1 h2)
    exact ⟨res.1, res.2, hgap⟩
  have R : ∀ k, ∀ u, c k ≤ u → u < c k + dlmin → O u = !V k := by
    intro k
    induction k with
    | zero => exact H_RESET_DONE
    | succ k ih =>
      intro u h1 h2
      obtain ⟨hO, _, hgap⟩ := step k ih
      rw [H_ALT k, Bool.not_not]
      exact hO u (by linarith) (by linarith)
  intro k
  obtain ⟨h1, h2, _⟩ := step k (R k)
  exact ⟨h1, h2⟩

end c2

/-! ## 1(b). Runt counter-trace (fixed delays, FIFO channel)

`train t0 D w` is high exactly on `⋃ n, [t0 + nD, t0 + nD + w)`. Written with
an existential over `n` instead of `mod`, which in `ℝ` is SIMPLER than 5b's
`Nat.mod` closed form: the loop equation is the one-line recursion
`train_rec`. -/

open Classical in
/-- The periodic pulse train. -/
noncomputable def train (t0 D w : ℝ) : Sig := fun t =>
  if ∃ n : ℕ, t0 + n * D ≤ t ∧ t < t0 + n * D + w then true else false

/-- The `b` runt: high on `[t0, t0 + w)` (shard A's `pulse`). -/
noncomputable def bR (t0 w : ℝ) : Sig := DelayInertial.pulse false t0 w
def aR : Sig := fun _ => true
def rstR : Sig := fun _ => false

theorem train_rec (t0 D w t : ℝ) :
    train t0 D w t = (bR t0 w t || train t0 D w (t - D)) := by
  have iff : (∃ n : ℕ, t0 + n * D ≤ t ∧ t < t0 + n * D + w) ↔
      ((t0 ≤ t ∧ t < t0 + w) ∨ (∃ n : ℕ, t0 + n * D ≤ t - D ∧ t - D < t0 + n * D + w)) := by
    constructor
    · rintro ⟨n, h1, h2⟩
      cases n with
      | zero => left; simp at h1 h2; exact ⟨h1, h2⟩
      | succ m =>
        right
        refine ⟨m, ?_, ?_⟩ <;> push_cast at h1 h2 <;> linarith
    · rintro (⟨h1, h2⟩ | ⟨n, h1, h2⟩)
      · exact ⟨0, by simpa using h1, by simpa using h2⟩
      · exact ⟨n + 1, by push_cast; linarith, by push_cast; linarith⟩
  unfold train bR DelayInertial.pulse
  by_cases hq : (t0 ≤ t ∧ t < t0 + w) <;>
    by_cases hr : (∃ n : ℕ, t0 + n * D ≤ t - D ∧ t - D < t0 + n * D + w) <;>
    simp [hq, hr, iff]

theorem train_on {t0 D w : ℝ} (hw : 0 < w) (n : ℕ) : train t0 D w (t0 + n * D) = true := by
  unfold train; rw [ite_eq_left ⟨n, le_rfl, by linarith⟩]

theorem train_before {t0 D w v : ℝ} (hD : 0 ≤ D) (hv : v < t0) : train t0 D w v = false := by
  unfold train
  rw [ite_eq_right]
  rintro ⟨m, k1, _⟩
  have : (0 : ℝ) ≤ m * D := mul_nonneg (Nat.cast_nonneg m) hD
  linarith

/-- Inside period `n` the train is high exactly on the first `w`. -/
theorem train_period {t0 D w : ℝ} (hD : 0 < D) (hw : w < D) (n : ℕ) (v : ℝ)
    (h1 : t0 + n * D ≤ v) (h2 : v < t0 + (n + 1) * D) :
    train t0 D w v = (if v < t0 + n * D + w then true else false) := by
  unfold train
  by_cases hv : v < t0 + n * D + w
  · rw [ite_eq_left ⟨n, h1, hv⟩, ite_eq_left hv]
  · rw [ite_eq_right hv, ite_eq_right]
    rintro ⟨m, k1, k2⟩
    have a1 : (m : ℝ) * D < (n + 1) * D := by linarith
    have a2 : (n : ℝ) * D < (m + 1) * D := by linarith
    have b1 : (m : ℝ) < n + 1 := lt_of_mul_lt_mul_right a1 hD.le
    have b2 : (n : ℝ) < m + 1 := lt_of_mul_lt_mul_right a2 hD.le
    have c1 : m < n + 1 := by exact_mod_cast b1
    have c2 : n < m + 1 := by exact_mod_cast b2
    obtain rfl : m = n := by omega
    exact hv k2

theorem train_off {t0 D w : ℝ} (hD : 0 < D) (hw0 : 0 < w) (hw : w < D) (n : ℕ) :
    train t0 D w (t0 + n * D + w) = false := by
  rw [train_period hD hw n _ (by linarith) (by linarith), ite_eq_right (lt_irrefl _)]

/-- The runt loop's traces: `O` and `qp` are the train delayed by `dl`, `D`. -/
noncomputable def OR (t0 dl dw w : ℝ) : Sig := fun t => train t0 (dl + dw) w (t - dl)
noncomputable def qpR (t0 dl dw w : ℝ) : Sig := fun t => train t0 (dl + dw) w (t - (dl + dw))

/-- **The runt traces satisfy every gate relation** of `bd_c2` on A's FIFO
channels with `dlmin = dlmax = dl`, `dwmin = dwmax = dw`. -/
theorem runt_loopR {t0 dl dw w : ℝ} (hpos : 0 < dl + dw) (hdl : 0 ≤ dl) (hdw : 0 ≤ dw) :
    LoopR INIT_c2 aR (bR t0 w) rstR (OR t0 dl dw w) (qpR t0 dl dw w) dl dl dw dw where
  H_LUT := by
    apply DelayPure.chan_fixed_iff.mpr
    intro s
    simp only [OR, excR, aR, rstR, qpR]
    rw [exc_or, train_rec t0 (dl + dw) w (s - dl)]
  H_FB := by
    apply DelayPure.chan_fixed_iff.mpr
    intro s
    simp only [OR, qpR]
    congr 1; ring
  H_LOOP_POS := by linarith
  H_CAUSAL := ⟨hdl, hdw⟩

/-- **(b) Misbehaviour**, continuous time: after `t0 + w` the inputs are
constant (`a = 1, b = 0, rst = 0`, so a C-element must hold), yet `qp` is 1 at
`t0 + (n+1)D` and 0 at `t0 + (n+1)D + w` for every `n`, and `O` likewise:
perpetual oscillation, period `D`, high time `w`, for every `0 < w < D`. -/
theorem runt_oscillatesR {t0 dl dw w : ℝ} (hw0 : 0 < w) (hw : w < dl + dw) :
    (∀ t, t0 + w ≤ t → aR t = true ∧ bR t0 w t = false ∧ rstR t = false) ∧
    (∀ n : ℕ, qpR t0 dl dw w (t0 + ((n : ℝ) + 1) * (dl + dw)) = true ∧
              qpR t0 dl dw w (t0 + ((n : ℝ) + 1) * (dl + dw) + w) = false) ∧
    (∀ n : ℕ, OR t0 dl dw w (t0 + dl + n * (dl + dw)) = true ∧
              OR t0 dl dw w (t0 + dl + n * (dl + dw) + w) = false) := by
  have hD : 0 < dl + dw := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact ⟨rfl, DelayInertial.pulse_after ht, rfl⟩
  · intro n
    simp only [qpR]
    rw [show t0 + ((n : ℝ) + 1) * (dl + dw) - (dl + dw) = t0 + n * (dl + dw) by ring,
      show t0 + ((n : ℝ) + 1) * (dl + dw) + w - (dl + dw) = t0 + n * (dl + dw) + w by ring]
    exact ⟨train_on hw0 n, train_off hD hw0 hw n⟩
  · intro n
    simp only [OR]
    rw [show t0 + dl + n * (dl + dw) - dl = t0 + n * (dl + dw) by ring,
      show t0 + dl + n * (dl + dw) + w - dl = t0 + n * (dl + dw) + w by ring]
    exact ⟨train_on hw0 n, train_off hD hw0 hw n⟩

/-! ## 2. Inertial LUT in the loop: lost / circulates / latches -/

/-- Locality of A's rejection filter: its value at `u` depends only on the
input before `u + ρ`. -/
theorem filtAt_congr {ρ u : ℝ} {x x' : Sig} {v : Bool} (hρ : 0 < ρ)
    (h : ∀ s, s < u + ρ → x s = x' s) (hf : FiltAt ρ x v u) : FiltAt ρ x' v u := by
  obtain ⟨τ, hτu, hs, hb, hmax⟩ := hf
  have stab : ∀ τ', τ' ≤ u → (Stable x τ' ρ ↔ Stable x' τ' ρ) := by
    intro τ' hτ'
    constructor
    · intro hs' s h1 h2
      rw [← h s (by linarith), ← h τ' (by linarith)]
      exact hs' s h1 h2
    · intro hs' s h1 h2
      rw [h s (by linarith), h τ' (by linarith)]
      exact hs' s h1 h2
  refine ⟨τ, hτu, (stab τ hτu).1 hs, ?_, ?_⟩
  · rw [hb, h τ (by linarith)]
  · intro τ' h1 h2 hs'
    rw [← h τ' (by linarith), ← h τ (by linarith)]
    exact hmax τ' h1 h2 ((stab τ' h2).2 hs')

/-- **The inertial loop is deterministic** (any INIT, any inputs): two
solutions (inertial LUT with window `ρ` and delay `dl`, fixed wire `dw`)
whose feedback pins agree before `t0` agree everywhere. Needs
`H_CAUSAL_LOOP : ρ < dl + dw` (the filter looks `ρ` ahead; the loop must
not see its own future). -/
theorem inLoop_unique {init : Nat} {a b rst : Sig} {ρ dl dw t0 : ℝ} (hρ : 0 < ρ)
    (H_CAUSAL_LOOP : ρ < dl + dw) {O qp O' qp' : Sig}
    (h1 : InertialRD ρ dl (excR init a b rst qp) O) (hw : ∀ t, qp t = O (t - dw))
    (h1' : InertialRD ρ dl (excR init a b rst qp') O') (hw' : ∀ t, qp' t = O' (t - dw))
    (hinit : ∀ t, t < t0 → qp t = qp' t) : qp = qp' ∧ O = O' := by
  have key : ∀ n : ℕ, ∀ t, t < t0 + n * (dl + dw - ρ) → qp t = qp' t := by
    intro n
    induction n with
    | zero => intro t ht; exact hinit t (by simpa using ht)
    | succ n ih =>
      intro t ht
      push_cast at ht
      have hx : ∀ s, s < (t - (dl + dw)) + ρ →
          excR init a b rst qp s = excR init a b rst qp' s := by
        intro s hs
        simp only [excR]
        rw [ih s (by linarith)]
      have e : O (t - (dl + dw) + dl) = O' (t - (dl + dw) + dl) :=
        filtAt_unique (filtAt_congr hρ hx (h1 (t - (dl + dw)))) (h1' (t - (dl + dw)))
      rw [show t - (dl + dw) + dl = t - dw by ring] at e
      rw [hw t, hw' t]
      exact e
  have hqp : qp = qp' := by
    funext t
    obtain ⟨n, hn⟩ := exists_mul_gt (by linarith : 0 < dl + dw - ρ) (t - t0)
    exact key n t (by linarith)
  refine ⟨hqp, ?_⟩
  funext s
  have e : O (s - dl + dl) = O' (s - dl + dl) := by
    subst hqp
    exact filtAt_unique (h1 (s - dl)) (h1' (s - dl))
  simpa using e

/-- The runt-loop hypotheses with an inertial LUT. -/
structure InLoop (ρ dl dw t0 w : ℝ) (O qp : Sig) : Prop where
  /-- **H_LUT_INERTIAL**: the LUT is an inertial channel, rejection window `ρ`,
  delay `dl` (A's `InertialRD`; Verilog path delay with PATHPULSE limit `ρ`).
  A modelling alternative, not claimed faithful (A proves it solves bounded
  SPF, which silicon cannot). -/
  H_LUT_INERTIAL : InertialRD ρ dl (excR INIT_c2 aR (bR t0 w) rstR qp) O
  /-- **H_FB**: fixed wire delay `dw` (A's `Chan dw dw`, `chan_fixed_iff`). -/
  H_FB : ∀ t, qp t = O (t - dw)
  /-- **H_INIT**: the cell held 0 before the runt. -/
  H_INIT : ∀ t, t < t0 → qp t = false

/-- **Regime (i): a runt shorter than the inertial window is LOST.** -/
theorem inertial_lost {ρ dl dw t0 w : ℝ} (hρ : 0 < ρ) (hc : ρ < dl + dw) (hw : w < ρ)
    {O qp : Sig} (H : InLoop ρ dl dw t0 w O qp) :
    (∀ t, O t = false) ∧ (∀ t, qp t = false) := by
  have hx : excR INIT_c2 aR (bR t0 w) rstR (fun _ => false) = bR t0 w := by
    funext t; simp only [excR, aR, rstR]; rw [exc_or, Bool.or_false]
  have h1' : InertialRD ρ dl (excR INIT_c2 aR (bR t0 w) rstR (fun _ => false)) (fun _ => false) := by
    rw [hx]; exact inertialRD_pulse_short_exists dl hρ hw
  obtain ⟨e1, e2⟩ := inLoop_unique (t0 := t0) hρ hc H.H_LUT_INERTIAL H.H_FB h1' (fun _ => rfl)
    (fun t ht => H.H_INIT t ht)
  exact ⟨fun t => by rw [e2], fun t => by rw [e1]⟩

/-- `train` has no pulse or gap shorter than `ρ` when `ρ ≤ w ≤ D - ρ`. -/
theorem exists_period {t0 D : ℝ} (hD : 0 < D) {u : ℝ} (hu : t0 ≤ u) :
    ∃ n : ℕ, t0 + n * D ≤ u ∧ u < t0 + (n + 1) * D := by
  classical
  have hex : ∃ n : ℕ, u < t0 + (n + 1) * D := by
    obtain ⟨n, hn⟩ := exists_mul_gt hD (u - t0)
    exact ⟨n, by linarith⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  cases hk : Nat.find hex with
  | zero => simpa using hu
  | succ m =>
    have hm : ¬ (u < t0 + ((m : ℝ) + 1) * D) := Nat.find_min hex (by omega)
    push_cast
    linarith [not_lt.mp hm]

theorem train_noShort {t0 D w ρ : ℝ} (hρ : 0 < ρ) (hρw : ρ ≤ w) (hgap : ρ ≤ D - w) :
    NoShort ρ (train t0 D w) := by
  have hD : 0 < D := by linarith
  have hw : w < D := by linarith
  intro u
  rcases lt_or_ge u t0 with hu | hu
  · refine ⟨u - ρ, by linarith, ?_, ?_⟩
    · intro v _ h2
      rw [train_before hD.le (by linarith), train_before hD.le (by linarith)]
    · intro v _ h2
      rw [train_before hD.le (by linarith), train_before hD.le (by linarith)]
  · obtain ⟨n, hn1, hn2⟩ := exists_period hD hu
    have per : ∀ v, t0 + n * D ≤ v → v < t0 + (n + 1) * D →
        train t0 D w v = if v < t0 + n * D + w then true else false :=
      fun v h1 h2 => train_period hD hw n v h1 h2
    rcases lt_or_ge u (t0 + n * D + w) with hb | hb
    · refine ⟨t0 + n * D, hn1, ?_, ?_⟩
      · intro v h1 h2
        rw [per v h1 (by linarith), per (t0 + n * D) le_rfl (by linarith),
          ite_eq_left (by linarith), ite_eq_left (by linarith)]
      · intro v h1 h2
        rw [per v h1 (by linarith), per (t0 + n * D) le_rfl (by linarith),
          ite_eq_left (by linarith), ite_eq_left (by linarith)]
    · refine ⟨t0 + n * D + w, hb, ?_, ?_⟩
      · intro v h1 h2
        rw [per v (by linarith) (by linarith), per (t0 + n * D + w) (by linarith) (by linarith),
          ite_eq_right (not_lt.mpr (by linarith)), ite_eq_right (lt_irrefl _)]
      · intro v h1 h2
        rw [per v (by linarith) (by linarith), per (t0 + n * D + w) (by linarith) (by linarith),
          ite_eq_right (not_lt.mpr (by linarith)), ite_eq_right (lt_irrefl _)]

/-- **Regime (ii): `ρ ≤ w ≤ D - ρ` circulates forever.** Every solution is
the train: `qp` is 1 at `t0 + (n+1)D` and 0 at `t0 + (n+1)D + w` for all `n`. -/
theorem inertial_circulates {ρ dl dw t0 w : ℝ} (hρ : 0 < ρ) (hρw : ρ ≤ w)
    (hgap : ρ ≤ dl + dw - w) {O qp : Sig} (H : InLoop ρ dl dw t0 w O qp) :
    (∀ t, qp t = train t0 (dl + dw) w (t - (dl + dw))) ∧
    (∀ t, O t = train t0 (dl + dw) w (t - dl)) ∧
    (∀ n : ℕ, qp (t0 + ((n : ℝ) + 1) * (dl + dw)) = true ∧
              qp (t0 + ((n : ℝ) + 1) * (dl + dw) + w) = false) := by
  have hc : ρ < dl + dw := by linarith
  have hD : 0 < dl + dw := by linarith
  have hx : excR INIT_c2 aR (bR t0 w) rstR (qpR t0 dl dw w) = train t0 (dl + dw) w := by
    funext t
    simp only [excR, aR, rstR, qpR]
    rw [exc_or, train_rec t0 (dl + dw) w t]
  have h1' : InertialRD ρ dl (excR INIT_c2 aR (bR t0 w) rstR (qpR t0 dl dw w))
      (shift dl (train t0 (dl + dw) w)) := by
    rw [hx]; exact inertialRD_of_noShort dl (train_noShort hρ hρw hgap)
  have hw' : ∀ t, qpR t0 dl dw w t = shift dl (train t0 (dl + dw) w) (t - dw) := by
    intro t; simp only [qpR, shift]; congr 1; ring
  obtain ⟨e1, e2⟩ := inLoop_unique (t0 := t0) hρ hc H.H_LUT_INERTIAL H.H_FB h1' hw'
    (fun t ht => by
      rw [H.H_INIT t ht]
      exact (train_before hD.le (by linarith : t - (dl + dw) < t0)).symm)
  refine ⟨fun t => by rw [e1]; rfl, fun t => by rw [e2]; rfl, fun n => ?_⟩
  rw [e1]
  have hrun := (runt_oscillatesR (t0 := t0) (dl := dl) (dw := dw) (w := w)
    (by linarith) (by linarith)).2.1 n
  exact hrun

/-- The step at `t0`. -/
noncomputable def step (t0 : ℝ) : Sig := fun t => if t0 ≤ t then true else false

theorem step_of_le {t0 t : ℝ} (h : t0 ≤ t) : step t0 t = true := by
  unfold step; rw [ite_eq_left h]
theorem step_of_lt {t0 t : ℝ} (h : t < t0) : step t0 t = false := by
  unfold step; rw [ite_eq_right (not_le.mpr h)]

/-- The filter fills a gap shorter than `ρ` after a first pulse `≥ ρ`. -/
theorem filt_latch {ρ t0 w D : ℝ} (hρ : 0 < ρ) (hρw : ρ ≤ w) (hgap : D - w < ρ) (hD : 0 ≤ D) :
    Filt ρ (fun t => bR t0 w t || step t0 (t - D)) (step t0) := by
  set x : Sig := fun t => bR t0 w t || step t0 (t - D) with hx
  have xT : ∀ v, (t0 ≤ v ∧ v < t0 + w) ∨ t0 + D ≤ v → x v = true := by
    rintro v (⟨h1, h2⟩ | h)
    · simp [hx, bR, DelayInertial.pulse_in (b := false) h1 h2]
    · simp [hx, step_of_le (show t0 ≤ v - D by linarith)]
  have xF : ∀ v, v < t0 → x v = false := by
    intro v h
    simp [hx, bR, DelayInertial.pulse_before (b := false) (w := w) h,
      step_of_lt (show v - D < t0 by linarith)]
  intro u
  rcases lt_or_ge u t0 with hu | hu
  · have hm := min_le_right u (t0 - ρ)
    have hm' := min_le_left u (t0 - ρ)
    refine ⟨min u (t0 - ρ), hm', ?_, ?_, ?_⟩
    · intro v h1 h2
      rw [xF v (by linarith), xF (min u (t0 - ρ)) (by linarith)]
    · rw [step_of_lt hu, xF (min u (t0 - ρ)) (by linarith)]
    · intro τ' h1 h2 _
      rw [xF τ' (by linarith), xF (min u (t0 - ρ)) (by linarith)]
  · refine ⟨t0, hu, ?_, ?_, ?_⟩
    · intro v h1 h2
      rw [xT v (Or.inl ⟨h1, by linarith⟩), xT t0 (Or.inl ⟨le_rfl, by linarith⟩)]
    · rw [step_of_le hu, xT t0 (Or.inl ⟨le_rfl, by linarith⟩)]
    · intro τ' h1 h2 hs
      rw [xT t0 (Or.inl ⟨le_rfl, by linarith⟩)]
      by_cases ha : τ' < t0 + w
      · exact xT τ' (Or.inl ⟨h1.le, ha⟩)
      · by_cases hb : t0 + D ≤ τ'
        · exact xT τ' (Or.inr hb)
        · push Not at ha hb
          have := hs (t0 + D) (by linarith) (by linarith)
          rw [xT (t0 + D) (Or.inr le_rfl)] at this
          exact this.symm

/-- **Regime (iii): a gap `D - w` shorter than `ρ` LATCHES** (first pulse
`w ≥ ρ`). Every solution is the step: `O = 1` from `t0 + dl` on, forever. -/
theorem inertial_latches {ρ dl dw t0 w : ℝ} (hρ : 0 < ρ) (hρw : ρ ≤ w)
    (hgap : dl + dw - w < ρ) (hc : ρ < dl + dw) {O qp : Sig} (H : InLoop ρ dl dw t0 w O qp) :
    (∀ t, O t = step t0 (t - dl)) ∧ (∀ t, qp t = step t0 (t - (dl + dw))) := by
  have hD : 0 ≤ dl + dw := by linarith
  set qpC : Sig := fun t => step t0 (t - (dl + dw)) with hqpC
  have hx : excR INIT_c2 aR (bR t0 w) rstR qpC = fun t => bR t0 w t || step t0 (t - (dl + dw)) := by
    funext t; simp only [excR, aR, rstR, hqpC]; rw [exc_or]
  have h1' : InertialRD ρ dl (excR INIT_c2 aR (bR t0 w) rstR qpC) (shift dl (step t0)) := by
    rw [hx]; exact inertialRD_of_filt dl (filt_latch hρ hρw hgap hD)
  have hw' : ∀ t, qpC t = shift dl (step t0) (t - dw) := by
    intro t; simp only [hqpC, shift]; congr 1; ring
  obtain ⟨e1, e2⟩ := inLoop_unique (t0 := t0) hρ hc H.H_LUT_INERTIAL H.H_FB h1' hw'
    (fun t ht => by
      rw [H.H_INIT t ht]
      exact (step_of_lt (by linarith : t - (dl + dw) < t0)).symm)
  exact ⟨fun t => by rw [e2]; rfl, fun t => by rw [e1]⟩

/-- **Refutation of "`ρ ≤ w < D` circulates"**: with `ρ = 1`, `dl = dw = 1`
(`D = 2`), `w = 3/2` (`ρ ≤ w < D`), the loop latches: `qp = 1` from `D` on. -/
theorem runt_below_D_can_latch :
    ∃ (ρ dl dw w : ℝ) (O qp : Sig), 0 < ρ ∧ ρ ≤ w ∧ w < dl + dw ∧
      InLoop ρ dl dw 0 w O qp ∧ ∀ t, dl + dw ≤ t → qp t = true := by
  refine ⟨1, 1, 1, 3 / 2, shift 1 (step 0), fun t => step 0 (t - (1 + 1)),
    by norm_num, by norm_num, by norm_num, ⟨?_, ?_, ?_⟩, ?_⟩
  · have hx : excR INIT_c2 aR (bR 0 (3 / 2)) rstR (fun t => step 0 (t - (1 + 1))) =
        fun t => bR 0 (3 / 2) t || step 0 (t - (1 + 1)) := by
      funext t; simp only [excR, aR, rstR]; rw [exc_or]
    rw [hx]
    exact inertialRD_of_filt 1 (filt_latch (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · intro t; simp only [shift]; congr 1; ring
  · intro t ht; exact step_of_lt (by linarith)
  · intro t ht; exact step_of_le (by linarith)

/-! ## 3. Involution channel (Fuegger/Najvirt/Nowak/Schmid), minimal

A single-history channel: an input transition at `t`, with the previous
OUTPUT transition at `o`, produces an output transition at
`t + δ(t - o)` (`δ = dU` for rising, `dD` for falling), and two output
transitions that would be out of order cancel. Involution law:
`-dU(-dD T) = T` and `-dD(-dU T) = T`.

The `bd_c2` loop with `a = 1`, `rst = 0` is the OR loop `x = b ∨ qp`, the
zero-time LUT function followed by ONE involution channel (LUT + wire
lumped). A runt `b = [0, Δ0)` with `0 < Δ0 < dUinf` (the output's first rise
`o 0 = dUinf` = the delay for a transition after a long quiet history):
* `o 0 = dUinf` (rise), `o 1 = Δ0 + dD(Δ0 - o 0)` (fall, from `b`'s fall);
* afterwards `x = qp`, so each output transition `o n` is fed back as input
  transition at the same instant, whose previous output transition is
  `o (n+1)`: `o (n+2) = o n + δ_n (o n - o (n+1))`, `δ_n = dU` for even `n`.
This derivation from the channel rule is in the docs, not proved from a
signal-level channel relation (see notes). The first `n` with
`o (n+1) ≤ o n` is a cancellation: `n` even = the rise is cancelled, the
output stays 0 (LOST); `n` odd = the fall is cancelled, it stays 1
(LATCHED). `Osc` = no cancellation ever. -/

/-- Involution channel data. Every field is a named hypothesis. -/
structure InvCh where
  dU : ℝ → ℝ
  dD : ℝ → ℝ
  /-- Rising delay after a long quiet history (`δ↑(∞)`). -/
  dUinf : ℝ
  /-- **H_CONT**: delay functions are continuous (paper: they are). -/
  H_CONT_U : Continuous dU
  H_CONT_D : Continuous dD
  /-- **H_MONO**: delay grows with the time since the last output transition. -/
  H_MONO_U : Monotone dU
  H_MONO_D : Monotone dD
  /-- **H_INV**: the involution law. -/
  H_INV_UD : ∀ T, -dU (-dD T) = T
  H_INV_DU : ∀ T, -dD (-dU T) = T
  /-- **H_POS**: positive delay at `T = 0`. -/
  H_POS_U : 0 < dU 0
  H_POS_D : 0 < dD 0
  /-- **H_INF**: `δ↑(0) < δ↑(∞)`. -/
  H_INF : dU 0 < dUinf

namespace InvCh

def dly (C : InvCh) (n : ℕ) : ℝ → ℝ := if n % 2 = 0 then C.dU else C.dD

theorem dly_even (C : InvCh) {n : ℕ} (h : n % 2 = 0) : C.dly n = C.dU := by
  unfold dly; rw [ite_eq_left h]
theorem dly_odd (C : InvCh) {n : ℕ} (h : n % 2 = 1) : C.dly n = C.dD := by
  unfold dly; rw [ite_eq_right (by omega)]

theorem dly_cont (C : InvCh) (n : ℕ) : Continuous (C.dly n) := by
  unfold dly; split
  · exact C.H_CONT_U
  · exact C.H_CONT_D

theorem dly_mono (C : InvCh) (n : ℕ) : Monotone (C.dly n) := by
  unfold dly; split
  · exact C.H_MONO_U
  · exact C.H_MONO_D

/-- Output transition times of the OR loop for a runt of width `Δ0`. -/
noncomputable def orb (C : InvCh) (Δ0 : ℝ) : ℕ → ℝ
  | 0 => C.dUinf
  | 1 => Δ0 + C.dD (Δ0 - C.dUinf)
  | n + 2 => orb C Δ0 n + C.dly n (orb C Δ0 n - orb C Δ0 (n + 1))

theorem orb_succ_succ (C : InvCh) (Δ0 : ℝ) (n : ℕ) :
    C.orb Δ0 (n + 2) = C.orb Δ0 n + C.dly n (C.orb Δ0 n - C.orb Δ0 (n + 1)) := rfl

theorem orb_cont (C : InvCh) :
    ∀ n, Continuous (fun Δ0 => C.orb Δ0 n) ∧ Continuous (fun Δ0 => C.orb Δ0 (n + 1)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨continuous_const, ?_⟩
    show Continuous (fun Δ0 => Δ0 + C.dD (Δ0 - C.dUinf))
    exact continuous_id.add (C.H_CONT_D.comp (continuous_id.sub continuous_const))
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show Continuous (fun Δ0 => C.orb Δ0 n + C.dly n (C.orb Δ0 n - C.orb Δ0 (n + 1)))
    exact ih.1.add ((C.dly_cont n).comp (ih.1.sub ih.2))

def Osc (C : InvCh) (Δ0 : ℝ) : Prop := ∀ n, C.orb Δ0 n < C.orb Δ0 (n + 1)

def chainS (C : InvCh) (n : ℕ) : Set ℝ := {Δ0 | ∀ j < n, C.orb Δ0 j < C.orb Δ0 (j + 1)}
def U (C : InvCh) (n : ℕ) : Set ℝ := C.chainS n ∩ {Δ0 | C.orb Δ0 (n + 1) < C.orb Δ0 n}
def W (C : InvCh) (n : ℕ) : Set ℝ :=
  C.chainS n ∩ ({Δ0 | C.orb Δ0 (n + 1) < C.orb Δ0 (n + 2)} ∩
    {Δ0 | C.orb Δ0 (n + 3) < C.orb Δ0 (n + 2)})
/-- Runt widths that are lost (first cancellation at an even index). -/
def Lset (C : InvCh) : Set ℝ := ⋃ k : ℕ, (C.U (2 * k) ∪ C.W (2 * k))
/-- Runt widths that latch (first cancellation at an odd index). -/
def Hset (C : InvCh) : Set ℝ := ⋃ k : ℕ, (C.U (2 * k + 1) ∪ C.W (2 * k + 1))

theorem isOpen_chainS (C : InvCh) (n : ℕ) : IsOpen (C.chainS n) := by
  induction n with
  | zero =>
    have : C.chainS 0 = Set.univ := by
      ext Δ0; simp [chainS]
    rw [this]; exact isOpen_univ
  | succ n ih =>
    have : C.chainS (n + 1) = C.chainS n ∩ {Δ0 | C.orb Δ0 n < C.orb Δ0 (n + 1)} := by
      ext Δ0
      simp only [chainS, Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
      · rintro ⟨h1, h2⟩ j hj
        by_cases hjn : j < n
        · exact h1 j hjn
        · have : j = n := by omega
          subst this; exact h2
    rw [this]
    exact ih.inter (isOpen_lt (C.orb_cont n).1 (C.orb_cont n).2)

theorem isOpen_U (C : InvCh) (n : ℕ) : IsOpen (C.U n) :=
  (C.isOpen_chainS n).inter (isOpen_lt (C.orb_cont n).2 (C.orb_cont n).1)

theorem isOpen_W (C : InvCh) (n : ℕ) : IsOpen (C.W n) :=
  (C.isOpen_chainS n).inter ((isOpen_lt (C.orb_cont n).2 (C.orb_cont (n + 1)).2).inter
    (isOpen_lt (C.orb_cont (n + 2)).2 (C.orb_cont (n + 2)).1))

theorem isOpen_L (C : InvCh) : IsOpen C.Lset :=
  isOpen_iUnion fun _ => (C.isOpen_U _).union (C.isOpen_W _)

theorem isOpen_H (C : InvCh) : IsOpen C.Hset :=
  isOpen_iUnion fun _ => (C.isOpen_U _).union (C.isOpen_W _)

theorem first_of_UW (C : InvCh) {Δ0 : ℝ} {n : ℕ} (h : Δ0 ∈ C.U n ∪ C.W n) :
    ∃ m, m % 2 = n % 2 ∧ Δ0 ∈ C.chainS m ∧ C.orb Δ0 (m + 1) ≤ C.orb Δ0 m := by
  rcases h with ⟨hc, hl⟩ | ⟨hc, h1, h2⟩
  · exact ⟨n, rfl, hc, le_of_lt hl⟩
  · by_cases hn : C.orb Δ0 (n + 1) ≤ C.orb Δ0 n
    · exact ⟨n, rfl, hc, hn⟩
    · refine ⟨n + 2, by omega, ?_, le_of_lt h2⟩
      intro j hj
      by_cases ha : j < n
      · exact hc j ha
      · by_cases hb : j = n
        · subst hb; exact not_le.mp hn
        · have : j = n + 1 := by omega
          subst this; exact h1

theorem first_unique (C : InvCh) {Δ0 : ℝ} {m m' : ℕ} (h1 : Δ0 ∈ C.chainS m)
    (f1 : C.orb Δ0 (m + 1) ≤ C.orb Δ0 m) (h2 : Δ0 ∈ C.chainS m')
    (f2 : C.orb Δ0 (m' + 1) ≤ C.orb Δ0 m') : m = m' := by
  rcases lt_trichotomy m m' with h | h | h
  · exact absurd (h2 m h) (not_lt.mpr f1)
  · exact h
  · exact absurd (h1 m' h) (not_lt.mpr f2)

theorem LH_disjoint (C : InvCh) {Δ0 : ℝ} (hL : Δ0 ∈ C.Lset) (hH : Δ0 ∈ C.Hset) : False := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k', hk'⟩ := Set.mem_iUnion.mp hH
  obtain ⟨m, pm, cm, fm⟩ := C.first_of_UW hk
  obtain ⟨m', pm', cm', fm'⟩ := C.first_of_UW hk'
  have := C.first_unique cm fm cm' fm'
  omega

/-- Every non-oscillating width is lost or latched (a tie `o (n+1) = o n`
resolves two transitions later, by the involution law at `T = 0`). -/
theorem cover (C : InvCh) (Δ0 : ℝ) (h : ¬ C.Osc Δ0) : Δ0 ∈ C.Lset ∪ C.Hset := by
  classical
  have hex : ∃ m, C.orb Δ0 (m + 1) ≤ C.orb Δ0 m := by
    unfold Osc at h; push Not at h; exact h
  obtain ⟨m, hfail, hmin⟩ : ∃ m, C.orb Δ0 (m + 1) ≤ C.orb Δ0 m ∧
      ∀ j < m, ¬ C.orb Δ0 (j + 1) ≤ C.orb Δ0 j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hch : Δ0 ∈ C.chainS m := fun j hj => not_le.mp (hmin j hj)
  have hUW : Δ0 ∈ C.U m ∪ C.W m := by
    rcases lt_or_eq_of_le hfail with hlt | heq
    · exact Or.inl ⟨hch, hlt⟩
    · right
      have h2 : C.orb Δ0 (m + 2) = C.orb Δ0 m + C.dly m 0 := by
        rw [orb_succ_succ, heq, sub_self]
      have h3 : C.orb Δ0 (m + 3) =
          C.orb Δ0 (m + 1) + C.dly (m + 1) (C.orb Δ0 (m + 1) - C.orb Δ0 (m + 2)) :=
        C.orb_succ_succ Δ0 (m + 1)
      have hpos : 0 < C.dly m 0 := by
        rcases Nat.mod_two_eq_zero_or_one m with hp | hp
        · rw [C.dly_even hp]; exact C.H_POS_U
        · rw [C.dly_odd hp]; exact C.H_POS_D
      have hzero : C.dly (m + 1) (-(C.dly m 0)) = 0 := by
        rcases Nat.mod_two_eq_zero_or_one m with hp | hp
        · rw [C.dly_even hp, C.dly_odd (by omega)]
          have := C.H_INV_DU 0; linarith
        · rw [C.dly_odd hp, C.dly_even (by omega)]
          have := C.H_INV_UD 0; linarith
      have e : C.orb Δ0 (m + 1) - C.orb Δ0 (m + 2) = -(C.dly m 0) := by
        rw [h2, heq]; ring
      refine ⟨hch, ?_, ?_⟩
      · show C.orb Δ0 (m + 1) < C.orb Δ0 (m + 2)
        rw [h2, heq]; linarith
      · show C.orb Δ0 (m + 3) < C.orb Δ0 (m + 2)
        rw [h3, e, hzero]
        linarith [h2, heq, hpos]
  rcases Nat.mod_two_eq_zero_or_one m with hp | hp
  · left
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
    exact Set.mem_iUnion.mpr ⟨k, hUW⟩
  · right
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
    exact Set.mem_iUnion.mpr ⟨k, hUW⟩

theorem left_in_L (C : InvCh) : C.dUinf - C.dU 0 ∈ C.Lset := by
  refine Set.mem_iUnion.mpr ⟨0, Or.inl ⟨fun j hj => by omega, ?_⟩⟩
  show (C.dUinf - C.dU 0) + C.dD ((C.dUinf - C.dU 0) - C.dUinf) < C.dUinf
  rw [show C.dUinf - C.dU 0 - C.dUinf = -C.dU 0 by ring]
  have h := C.H_INV_DU 0
  have := C.H_POS_U
  linarith

theorem orb_right1 (C : InvCh) : C.orb C.dUinf 1 = C.dUinf + C.dD 0 := by
  show C.dUinf + C.dD (C.dUinf - C.dUinf) = _
  rw [sub_self]

theorem right_in_H (C : InvCh) : C.dUinf ∈ C.Hset := by
  have h2 : C.orb C.dUinf 2 = C.dUinf := by
    rw [show (2 : ℕ) = 0 + 2 from rfl, orb_succ_succ, orb_right1, C.dly_even (by rfl)]
    show C.dUinf + C.dU (C.dUinf - (C.dUinf + C.dD 0)) = C.dUinf
    rw [show C.dUinf - (C.dUinf + C.dD 0) = -C.dD 0 by ring]
    have := C.H_INV_UD 0
    linarith
  refine Set.mem_iUnion.mpr ⟨0, Or.inl ⟨?_, ?_⟩⟩
  · intro j hj
    have : j = 0 := by omega
    subst this
    show C.orb C.dUinf 0 < C.orb C.dUinf 1
    rw [orb_right1]
    show C.dUinf < C.dUinf + C.dD 0
    linarith [C.H_POS_D]
  · show C.orb C.dUinf 2 < C.orb C.dUinf 1
    rw [h2, orb_right1]; linarith [C.H_POS_D]

/-- **Eternal oscillation.** For every involution channel there is a runt
width `Δ0` with `dUinf - dU 0 < Δ0 < dUinf` for which the `bd_c2` loop
(`a = 1`, `rst = 0`) never cancels a transition: it oscillates forever.
Proof: `[dUinf - dU 0, dUinf]` is connected, the lost and latched sets are
open, disjoint, and contain the two endpoints. -/
theorem inv_eternal (C : InvCh) :
    ∃ Δ0, C.dUinf - C.dU 0 < Δ0 ∧ Δ0 < C.dUinf ∧ C.Osc Δ0 := by
  by_contra hno
  push Not at hno
  have hle : C.dUinf - C.dU 0 ≤ C.dUinf := by linarith [C.H_POS_U]
  have hcov : Set.Icc (C.dUinf - C.dU 0) C.dUinf ⊆ C.Lset ∪ C.Hset := by
    intro Δ0 hΔ
    by_cases hosc : C.Osc Δ0
    · exfalso
      rcases eq_or_lt_of_le hΔ.1 with h | h
      · subst h
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp C.left_in_L
        obtain ⟨m, _, cm, fm⟩ := C.first_of_UW hk
        exact absurd (hosc m) (not_lt.mpr fm)
      rcases eq_or_lt_of_le hΔ.2 with h' | h'
      · rw [h'] at hosc
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp C.right_in_H
        obtain ⟨m, _, cm, fm⟩ := C.first_of_UW hk
        exact absurd (hosc m) (not_lt.mpr fm)
      exact hno Δ0 h h' hosc
    · exact C.cover Δ0 hosc
  obtain ⟨z, _, hzL, hzH⟩ := isPreconnected_Icc (C.Lset) (C.Hset) C.isOpen_L C.isOpen_H hcov
    ⟨_, ⟨le_refl _, hle⟩, C.left_in_L⟩ ⟨_, ⟨hle, le_refl _⟩, C.right_in_H⟩
  exact C.LH_disjoint hzL hzH

theorem exists_c (C : InvCh) : ∃ c > 0, 0 < C.dU (-c) ∧ 0 < C.dD (-c) := by
  have ho : IsOpen {c : ℝ | 0 < C.dU (-c) ∧ 0 < C.dD (-c)} :=
    (isOpen_lt continuous_const (C.H_CONT_U.comp continuous_neg)).inter
      (isOpen_lt continuous_const (C.H_CONT_D.comp continuous_neg))
  have h0 : (0 : ℝ) ∈ {c : ℝ | 0 < C.dU (-c) ∧ 0 < C.dD (-c)} := by
    simp only [Set.mem_ofPred_eq, neg_zero]; exact ⟨C.H_POS_U, C.H_POS_D⟩
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp ho 0 h0
  have hm : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  exact ⟨ε / 2, by linarith, hb hm⟩

/-- **Unbounded resolution time.** On an oscillating orbit the output keeps
switching after every time bound (no Zeno: each two transitions advance
time by a fixed `p > 0`). -/
theorem osc_unbounded (C : InvCh) {Δ0 : ℝ} (h : C.Osc Δ0) : ∀ B : ℝ, ∃ n, B < C.orb Δ0 n := by
  obtain ⟨c, hc, hU, hD⟩ := C.exists_c
  have hp0 : 0 < min c (min (C.dU (-c)) (C.dD (-c))) := lt_min hc (lt_min hU hD)
  set p := min c (min (C.dU (-c)) (C.dD (-c))) with hp
  have step2 : ∀ n, C.orb Δ0 n + p ≤ C.orb Δ0 (n + 2) := by
    intro n
    have e := C.orb_succ_succ Δ0 n
    have h1 := h n
    have h2 := h (n + 1)
    by_cases hw : C.orb Δ0 (n + 1) - C.orb Δ0 n ≤ c
    · have hmono : C.dly n (-c) ≤ C.dly n (C.orb Δ0 n - C.orb Δ0 (n + 1)) :=
        C.dly_mono n (by linarith)
      have hlow : p ≤ C.dly n (-c) := by
        rcases Nat.mod_two_eq_zero_or_one n with hq | hq
        · rw [C.dly_even hq]; exact le_trans (min_le_right _ _) (min_le_left _ _)
        · rw [C.dly_odd hq]; exact le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
    · have : p ≤ c := min_le_left _ _
      push Not at hw
      linarith
  have lin : ∀ k : ℕ, C.orb Δ0 0 + k * p ≤ C.orb Δ0 (2 * k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := step2 (2 * k)
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]
      push_cast
      linarith
  intro B
  obtain ⟨k, hk⟩ := exists_mul_gt hp0 (B - C.orb Δ0 0)
  exact ⟨2 * k, by linarith [lin k]⟩

end InvCh

end Formal.Cells.CElemCore
