import Formal.Target.SpecRunt
/-! Audit T26: the corrected H_RUNT (5a9f9237). For a gate that is NOT a LUT gate (every pip, hop, MUXF, CARRY4,
constant of the decoded target), `GateOKRunt` is exactly `GateOK`: H_RUNT puts no constraint on its reads, so the
T9 effect (a zero-arc reader forbidding a pulse on its input node) cannot arise there. -/
namespace Audit.T26
open Formal.Target
theorem runt_nonlut_iff {w : Nat} {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hL : lutGate g = false) :
    GateOKRunt w p c g x ↔ GateOK p c g x := by
  refine ⟨gateOK_of_runt, fun ⟨f, hm, ht⟩ => ⟨f, hm, fun t h0 => ⟨fun i hi => ⟨((ht t h0).1 i hi).1,
    ((ht t h0).1 i hi).2, fun h => by simp [hL] at h⟩, (ht t h0).2⟩⟩⟩
end Audit.T26
#print axioms Audit.T26.runt_nonlut_iff
