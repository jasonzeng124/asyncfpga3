import Formal.Cells.RaceCertPS
open Formal.Cells.RaceCertPS Formal.Target
-- statements as stated
#check @target_ack_holds
#check @race_margin
#print axioms target_ack_holds
#print axioms race_margin
#print axioms rows_ok
#print axioms kb_view
#print axioms kb_src
-- the two sides at c = 0 for kappa 0.41 / 0.417 / 0.42 / 0.44 (B: fails above 632/1514 ~ 0.4174 real-valued)
#eval [(41:ℚ)/100, 417/1000, 42/100, 44/100].map fun k =>
  (kb.hi ⟨1, k⟩ 0 0, k1.lo ⟨1, k⟩ 0 4 + k2.lo ⟨1, k⟩ 0 4 + k3.lo ⟨1, k⟩ 0 3 + k4.lo ⟨1, k⟩ 0 3 + k5.lo ⟨1, k⟩ 0 4 + kb.lo ⟨1, k⟩ 0 4)
-- mutation: the margin does NOT hold at kappa = 0.42, c = 0 (kernel-checked)
set_option maxRecDepth 100000 in
example : ¬ (kb.hi ⟨1, 42/100⟩ 0 0 ≤ k1.lo ⟨1, 42/100⟩ 0 4 + k2.lo ⟨1, 42/100⟩ 0 4 + k3.lo ⟨1, 42/100⟩ 0 3 +
    k4.lo ⟨1, 42/100⟩ 0 3 + k5.lo ⟨1, 42/100⟩ 0 4 + kb.lo ⟨1, 42/100⟩ 0 4) := by decide +kernel
