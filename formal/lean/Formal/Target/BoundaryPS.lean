import Formal.Target.NetPS.All

/-!
# Formal.Target.BoundaryPS — THE target's boundary is consistent (`Spec.Boundary.OK`)

Shard A, 2026-11-06. Spec part II asks for `B.OK N` next to `N.WF`. **Plainly:** in the decoded gcd_ps netlist,
the environment's node list contains the reset, the (shared) input request, the two output acknowledges and every
operand bit, and nothing else; every operand bit is an environment node (the AXI slave's data registers are flip-flops,
outside the Spec's circuit); both operand buses and the result bus have 32 nodes. Not shown: that the names are the
right ones (H_DECODE and the boundary script `tools-A/target/boundary_ps.py`, untrusted; audit T10 re-derived them).
-/

namespace Formal.Target.DecodedPS
open Formal.Target

theorem data_env : ∀ v ∈ boundary.a.data ++ boundary.b.data, v ∈ boundary.env := by decide

theorem boundary_ok : boundary.OK net := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, by decide, by decide, by decide⟩
  · intro v hv
    have : v = boundary.rst ∨ v = boundary.a.req ∨ v = boundary.b.req ∨ v = boundary.start.req ∨
        v = boundary.out0.ack ∨ v = boundary.pend.ack ∨ v ∈ boundary.a.data ∨ v ∈ boundary.b.data := by
      revert v; decide
    exact this
  · intro v hv hn
    exact absurd (data_env v hv) hn

end Formal.Target.DecodedPS
