import Formal.Core.Delay.GLSPass
open Formal.Core.GLSPass Formal.Core.TraceDiscrete
#check @skew_fval
#check @ce_skew
#print axioms run_unique
#print axioms gls_pass_of_saf_silicon
#print axioms gls_pass_transport_of_faithful
#print axioms gls_in_envelope
#print axioms ce_skew
#print axioms ce_skew_inertial_hides
#print axioms ce_skew_124
#print axioms ce_skew_kappa
#print axioms ce_capture
#print axioms ce_capture_124
#print axioms ce_c2
#print axioms ce_c2_124
#print axioms annotated_ne_baked
#print axioms gls_unique_time
#print axioms mono_saf_is_transport
#print axioms band_bracket_hi
#print axioms band_bracket_lo
#print axioms gls_mono_settle_band
#print axioms gls_mono_bundle

/-- Auditor: the GLS-run conjuncts of ce_skew are not vacuous: a GLS run exists (any d, w, p). -/
theorem audit_gls_run_exists (d w p : Nat) :
    ∃ s, GLSRun (lut2 xor) (skewA d w) (skewIn p) s := by
  refine ⟨fun k => if k < 2 then skewIn p k else if k = 2 then
      Sem.saf.ch d (fun t => xor (delay ((skewA d w).w 2 0) (skewIn p 0) t)
        (delay ((skewA d w).w 2 1) (skewIn p 1) t)) else fun _ => false, ?_, ?_, ?_⟩
  · intro k hk; simp only [lut2] at hk; simp [hk]
  · intro k h1 h2
    simp only [lut2] at h1 h2
    have hk : k = 2 := by omega
    subst hk
    simp only [show ¬ (2:Nat) < 2 by omega, ↓reduceIte]
    first | rfl | (congr 1; funext t; simp [fval, pins, wired, lut2, skewA, skewIn])
  · intro k hk; simp only [lut2] at hk
    simp [show ¬ k < 2 by omega, show k ≠ 2 by omega]
#print axioms audit_gls_run_exists
