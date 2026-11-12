import Formal.Net.GenWitCells2
import Formal.Net.CellBindGcd
import Formal.Net.CapstoneWitness

/-!
# Probe C-witgen (4/4): an ACTIVE joint witness for the generated-cell gcd_hw capstones

O4's `gcd_hw_circuit_safe_gen` (H_GEN = `GenCell` on all 367 operators, H_BUNDLE,
H_START_ONCE), O4b's `gcd_hw_circuit_safe_genK` (`GenCellK`) and the PersistK instance
`gcd_hw_circuit_safe_genP` (`GenCellKP`) had only the quiet witness (8t's run frozen at tick
0, which latches nothing). `gch` is a unit-delay run of the concrete network at the
generated-netlist level (formal/tools/capwit3/simgen.py; bdc's chain shapes: every compute
unit's `uor` + bd_delay_gated N = 12 (13 nodes), bd_mux udly N = 12, muxN `uor` +
bd_delay_gated N = 12, amerge `uor` + bd_delay_gated N = 4, bd_link rdly N = 3 + route,
uack FASTRISE N = 6 + route; bd_ctree internal nodes for fork N = 5, 6), a = 12, b = 18.

* **`gcd_hw_gen_joint_witness`**: `gch` satisfies every hypothesis of
  `gcd_hw_circuit_safe_gen` (all internal nodes, H_CHAIN_SETTLED on every side-tapped
  chain, end-only persistence on every buffer chain, H_LEAF_PERSIST, H_WIRE_DI with one
  tick, every LUT on its yosys INIT) AND out0 closes a token carrying 6.
* **`gcd_hw_genK_joint_witness`**, **`gcd_hw_genP_joint_witness`**: the same run for O4b's
  `GenCellK` and the PersistK `GenCellKP` hypotheses.
* `gcd_hw_gen_witness_consistent`: the three theorems applied to the run give 6 again.

6 = gcd 12 18 is decided (`gcd_12_18`), not read from the run.
-/

namespace Formal.Net.CellBind.GenWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Wit
open Formal.Net.CapNet.Gcd Formal.Net.CellBind.Ops

/-- **Active witness, O4.** -/
theorem gcd_hw_gen_joint_witness :
    ∃ ch : Fin NC → Chan,
      (∀ o : Fin NO, GenCell ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6) :=
  ⟨gch, g_gen, g_held, g_start_once, ⟨0, gOut0Close, g_out0⟩⟩

/-- **Active witness, O4b (`GenCellK`).** -/
theorem gcd_hw_genK_joint_witness :
    ∃ ch : Fin NC → Chan,
      (∀ o : Fin NO, KOps.GenCellK ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6) :=
  ⟨gch, fun o => genK_of_gen gch _ _ (g_gen o), g_held, g_start_once, ⟨0, gOut0Close, g_out0⟩⟩

/-- **Active witness, O4b PersistK (`GenCellKP`).** -/
theorem gcd_hw_genP_joint_witness :
    ∃ ch : Fin NC → Chan,
      (∀ o : Fin NO, PersistK.GenCellKP ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6) :=
  ⟨gch, fun o => genKP_of_gen gch _ _ (g_gen o), g_held, g_start_once, ⟨0, gOut0Close, g_out0⟩⟩

/-- **All four together** (one run): O4's and O4b's hypotheses jointly, and the latch of 6. -/
theorem gcd_hw_gen_all_witness :
    ∃ ch : Fin NC → Chan,
      (∀ o : Fin NO, GenCell ch (srcV 12 18) (opAt o)) ∧
      (∀ o : Fin NO, KOps.GenCellK ch (srcV 12 18) (opAt o)) ∧
      (∀ o : Fin NO, PersistK.GenCellKP ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6) :=
  ⟨gch, g_gen, fun o => genK_of_gen gch _ _ (g_gen o), fun o => genKP_of_gen gch _ _ (g_gen o),
    g_held, g_start_once, ⟨0, gOut0Close, g_out0⟩⟩

/-- The three capstones applied to the run. -/
theorem gcd_hw_gen_witness_consistent :
    (∀ k e, TokAt (gch out0) k e → (gch out0).dat e = 6) ∧ TokAt (gch out0) 0 gOut0Close := by
  have h1 := Gcd.gcd_hw_circuit_safe_gen 12 18 (by decide) (by decide) gch g_gen g_held g_start_once
  have h2 := K.gcd_hw_circuit_safe_genK 12 18 (by decide) (by decide) gch
    (fun o => genK_of_gen gch _ _ (g_gen o)) g_held g_start_once
  have h3 := PersistK.gcd_hw_circuit_safe_genP 12 18 (by decide) (by decide) gch
    (fun o => genKP_of_gen gch _ _ (g_gen o)) g_held g_start_once
  rw [gcd_12_18] at h1 h2 h3
  exact ⟨h1.1, g_out0.1⟩

end Formal.Net.CellBind.GenWit
