import Formal.Core.Delay.GLSPass
open Formal.Core.GLSPass Formal.Core.TraceDiscrete
-- MUTANT (must FAIL): the GLS at d = w = 100 hides the glitch (it does not: ce_skew_124.2.1).
theorem mut1 : ∀ s, GLSRun (lut2 xor) (skewA 100 100) (skewIn 1000) s → ∀ t, s 2 t = false :=
  ce_skew (d := 100) (d' := 1) (lo := 0) (by omega) (by omega) (by omega) (by omega) (by omega) |>.1
-- MUTANT (must FAIL): skew_fval with an unbound d (the original defect) under autoImplicit=false
theorem mut2 {p w : Nat} (hp : 1 ≤ p) :
    (fun t => xor (delay ((skewA d w).w 2 0) (skewIn p 0) t)
      (delay ((skewA d w).w 2 1) (skewIn p 1) t)) = pulse false p w := skew_fval hp
