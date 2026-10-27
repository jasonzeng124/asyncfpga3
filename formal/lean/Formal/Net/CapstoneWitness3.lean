import Formal.Net.CapstoneWitness
import Formal.Net.CapstoneWalk

/-!
# Probe C-8t: the witness run also shows `gcd_hw_circuit_safe3` (8s) is not vacuous

`gcd_hw_circuit_safe3` keeps only H_CELLS, H_BUNDLE and H_START_ONCE (H_WALK proved by 8s for
`a, b < 2^31`). The run `chW` of `CapstoneWitness` (a = 12, b = 18) meets those three and
latches a token on out0; `gcd_hw_witness3_consistent` applies the theorem to it.
-/

namespace Formal.Net.CapNet.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

theorem gcd_hw_joint_witness3 :
    ∃ ch : Fin NC → Chan,
      (∀ o : Fin NO, Cell ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6) :=
  ⟨chW, w_cells, w_held, w_start_once, ⟨0, out0Close, w_out0⟩⟩

theorem gcd_hw_witness3_consistent :
    (∀ k e, TokAt (chW out0) k e → (chW out0).dat e = 6) ∧ TokAt (chW out0) 0 out0Close := by
  have h := gcd_hw_circuit_safe3 12 18 (by decide) (by decide) chW w_cells w_held w_start_once
  rw [gcd_12_18] at h
  exact ⟨h.1, w_out0.1⟩

end Formal.Net.CapNet.Wit
