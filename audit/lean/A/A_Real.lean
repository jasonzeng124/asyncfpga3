import Formal.Core.Delay.Pure
import Formal.Core.Delay.Inertial
import Formal.Core.Delay.Involution
import Formal.Core.Delay.Corner
import Mathlib.Algebra.Order.Field.Basic

/-!
# Audit shard A: real-time delay channels (Pure, Inertial, Involution, Corner)

Non-vacuity witnesses (concrete traces/delays satisfying all hypotheses at
once), hypothesis-dropping checks, a counterexample for rule A as the code
implements it, and axiom prints.
-/

noncomputable section

namespace Audit.A

open Formal.Core

/-! ## Pure: bundle_two_wires, all hypotheses at once, and without `hbundle` -/

section Pure
open Formal.Core.DelayPure

/-- Data source: true on [1, 10], false elsewhere. -/
def src : Sig := fun t => if 1 ≤ t ∧ t ≤ 10 then true else false
/-- Request: rises at 0. -/
def reqIn : Sig := fun t => if 0 ≤ t then true else false

theorem src_stable : StableOn src (0 + 1) 10 true := by
  intro t h1 h2; simp only [src]; rw [if_pos ⟨by linarith, h2⟩]

theorem req_before : StableBefore reqIn 0 false := by
  intro t ht; simp only [reqIn]; rw [if_neg (by linarith)]

/-- Data wire fixed delay 2 in band [1,2]; request wire fixed delay 5 in band
[5,6]; ts + hiD = 1 + 2 ≤ 5 = loR; s = 5. -/
theorem bundle_witness : (fun s => src (s - 2)) 5 = true :=
  bundle_two_wires (loD := 1) (hiD := 2) (loR := 5) (hiR := 6) (t0 := 0) (ts := 1) (t1 := 10)
    (s := 5) (b := false) (v := true) (reqIn := reqIn) (reqOut := fun s => reqIn (s - 5))
    src_stable (chan_shift (by norm_num) (by norm_num) src)
    (chan_shift (by norm_num) (by norm_num) reqIn) req_before (by norm_num)
    (by simp [reqIn]) (by norm_num)

/-- Dropping `hbundle` (request wire delay 2 < ts + hiD = 3): the receiver
sees the request at s = 2 while the data is still the old value. -/
theorem bundle_fails_without_hbundle :
    Chan 1 2 src (fun s => src (s - 2)) ∧ Chan 2 2 reqIn (fun s => reqIn (s - 2)) ∧
    (fun s => reqIn (s - 2)) 2 ≠ false ∧ (fun s => src (s - 2)) 2 ≠ true := by
  refine ⟨chan_shift (by norm_num) (by norm_num) _, chan_shift le_rfl le_rfl _, ?_, ?_⟩
  · simp [reqIn]
  · simp [src]

/-- chan_comp_iff / pulse_vanish_iff instances. -/
example : Chan 0 1 (pulse (1/2)) (fun _ => false) :=
  (pulse_vanish_iff (lo := 0) (hi := 1) (w := 1/2) (by norm_num)).mpr (by norm_num)
example : ¬ Chan 0 1 (pulse 2) (fun _ => false) := fun h =>
  absurd ((pulse_vanish_iff (lo := 0) (hi := 1) (w := 2) (by norm_num)).mp h) (by norm_num)

end Pure

/-! ## Inertial -/

section Inertial
open Formal.Core.DelayInertial

example : InertialRD 1 3 (pulse false 0 2) (shift 3 (pulse false 0 2)) :=
  inertialRD_of_noShort 3 (noShort_pulse (by norm_num) (by norm_num))

end Inertial

/-! ## Involution: a concrete `InvolutionPair` (none exists in the claimed build
except through the abstract `ExpLog`, which has no instance there). -/

section Inv
open Formal.Core.DelayInvolution

/-- `δ(T) = 2 - 1/(T+2)`, `δ∞ = 2`: a hyperbolic involution channel. -/
def f (T : ℝ) : ℝ := 2 - 1 / (T + 2)

theorem f_lt (T : ℝ) (hT : -2 < T) : f T < 2 := by
  have h : 0 < 1 / (T + 2) := one_div_pos.mpr (by linarith)
  unfold f; linarith

theorem f_mono (a b : ℝ) (ha : -2 < a) (hab : a < b) : f a < f b := by
  have h := one_div_lt_one_div_of_lt (show 0 < a + 2 by linarith) (show a + 2 < b + 2 by linarith)
  unfold f; linarith

theorem f_inv (T : ℝ) (hT : -2 < T) : -f (-f T) = T := by
  unfold f
  rw [show -(2 - 1 / (T + 2)) + 2 = 1 / (T + 2) by ring, one_div_one_div]
  ring

def P : InvolutionPair where
  up := f
  down := f
  infUp := 2
  infDown := 2
  infUp_pos := by norm_num
  infDown_pos := by norm_num
  up_lt := f_lt
  down_lt := f_lt
  up_strictMono := f_mono
  down_strictMono := f_mono
  inv_up := f_inv
  inv_down := f_inv
  up_causal := by unfold f; norm_num
  down_causal := by unfold f; norm_num

theorem P_dmin : P.IsDMin 1 where
  mem := by show -(2:ℝ) < -1; norm_num
  fix := by show f (-1) = 1; unfold f; norm_num

/-- cancel_iff on a concrete increasing input sequence `t n = n/2`. -/
def tt (n : ℕ) : ℝ := (n : ℝ) / 2
theorem tt_inc : ∀ n, tt n < tt (n + 1) := by
  intro n; unfold tt; push_cast; linarith

example : P.tent tt 1 ≤ P.tent tt 0 ↔ tt 1 - P.tent tt 0 ≤ -1 :=
  InvolutionPair.cancel_iff P_dmin tt tt_inc 0

/-- ... and here the second transition really cancels (pulse of width 1/2 <
δ∞ - δmin = 1). -/
example : P.tent tt 1 ≤ P.tent tt 0 := by
  rw [InvolutionPair.cancel_iff P_dmin tt tt_inc 0]
  show tt 1 - (tt 0 + 2) ≤ -1
  unfold tt; norm_num

example : ∃ η > 0, ∀ Δ, P.infUp - 1 < Δ → Δ < P.infUp - 1 + η →
    0 < P.pulseWidth Δ ∧ P.pulseWidth Δ < 1/1000 :=
  InvolutionPair.pulseWidth_small P_dmin (by norm_num)

end Inv

/-! ## Corner: witnesses, and rule A as tighten.py actually computes it -/

section Corner
open Formal.Core.Corner

/-- ruleE_sound at κ = kappaE exactly, with a passing design. -/
example : (0:ℝ) + (1 + kappaE) * (1 * 1000) < 0 + (1 - kappaE) * (1 * 2000) :=
  ruleE_sound (κ := kappaE) (s := 1) (C := 0) (Pr := 2000) (Ps := 1000) one_pos le_rfl
    (by norm_num) ⟨le_rfl, by unfold kappaE; nlinarith⟩ ⟨by unfold kappaE; nlinarith, le_rfl⟩
    (by unfold guardLo guardHi; norm_num)

/-- ruleA_sound_rel at κ = 1/11, Pd = 1000, Pr = 1200 (boundary, equality). -/
example : (1 + 1/11 : ℝ) * 1000 ≤ (1 - 1/11) * 1200 :=
  by
    have := ruleA_sound_rel (κ := 1/11) (s := 1) (Pd := 1000) (Pr := 1200)
      (ad := (1 + 1/11) * 1000) (ar := (1 - 1/11) * 1200) one_pos (by norm_num) le_rfl
      (by norm_num) (by norm_num [max_def]) (by norm_num) (by norm_num)
    exact this

/-- **Rule A as tighten.py implements it is NOT sound at κ = 1/11.**
tighten.py:1106 `req_guard = max(int(0.2*t), 200)` (integer ps, truncated);
the check passes iff `t_close - t_data - guard ≥ 0` (tighten.py:1940,1964).
With t_data = 1004 ps, int(0.2·1004) = 200, so t_req = 1204 passes; yet with
κ = 1/11 (s = 1) the data can arrive at (12/11)·1004 ≈ 1095.3 and the request
at (10/11)·1204 ≈ 1094.5. The Lean hypothesis `Pd + max (Pd/5) 200 ≤ Pr`
(real division) rejects this design, so `ruleA_sound_rel` does not cover
the code's rule. The code's exact tolerance is κ ≤ 25/276 ≈ 0.09058. -/
theorem ruleA_code_unsound_at_1_11 :
    (1004 + max (1004 / 5) 200 ≤ (1204 : ℕ)) ∧
    ¬ ((1004 : ℝ) + max (1004 / 5) 200 ≤ 1204) ∧
    ¬ ((1 + 1/11 : ℝ) * 1004 ≤ (1 - 1/11) * 1204) := by
  refine ⟨by decide, ?_, by norm_num⟩
  rw [max_def]; norm_num

/-- With the code's truncated guard, κ = 25/276 is the exact boundary at
t_data = 1004 (equality), so nothing above 25/276 is sound for the code. -/
example : (1 + 25/276 : ℝ) * 1004 = (1 - 25/276) * 1204 := by norm_num

end Corner

/-! ## Axioms -/

#print axioms Formal.Core.DelayPure.chan_comp_iff
#print axioms Formal.Core.DelayPure.pulse_vanish_iff
#print axioms Formal.Core.DelayPure.bundle_two_wires
#print axioms Formal.Core.DelayInertial.inertial_comp_1_2_not_inertialRD
#print axioms Formal.Core.DelayInertial.inertialRD_of_noShort
#print axioms Formal.Core.DelayInvolution.InvolutionPair.cancel_iff
#print axioms Formal.Core.DelayInvolution.InvolutionPair.pulseWidth_small
#print axioms Formal.Core.DelayInvolution.InvolutionPair.up_bounds
#print axioms Formal.Core.DelayInvolution.ExpLog.exp_pulse_cancel_iff
#print axioms Formal.Core.Corner.bundle_ratio_affine_iff
#print axioms Formal.Core.Corner.monotone_not_enough
#print axioms Formal.Core.Corner.ruleE_sound
#print axioms Formal.Core.Corner.ruleE_tight
#print axioms Formal.Core.Corner.ruleA_sound_rel
#print axioms Formal.Core.Corner.ruleA_tight
#print axioms Formal.Core.Corner.ring_kappa_lower
#print axioms Formal.Core.Corner.bundle_corner
#print axioms P
#print axioms bundle_witness
#print axioms ruleA_code_unsound_at_1_11

end Audit.A
