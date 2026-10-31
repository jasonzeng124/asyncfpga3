import Formal.Cells.SelfAuditB6
-- MUTANTS (Bsa3) of the rig-env witness checks in SelfAuditB6. Each must FAIL.
namespace Formal.Cells.SelfAuditB6.Mut
open Formal.Cells.SelfAuditB6
-- (1) in_ack first rise moved one tick later: uenv1 b half fails (mut_k); H_C3 alone still holds (mut_k2 PASSES: a weak mutant, kept as a finding).
theorem mut_k : envOK [100, 199] = true := by decide +kernel
theorem mut_k2 : srcOK RA RB [100, 199] = true := by decide +kernel
-- (2) wrong source value (a = 13): H_DAT fails.
theorem mut_a : srcOK 13 RB kL = true := by decide +kernel
-- (3) out0 latches 6 at 474, not at 473.
theorem mut_t : Formal.Net.Handshake.TokAt (chS Formal.Net.CapNet.Gcd.out0) 0 473 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel
end Formal.Cells.SelfAuditB6.Mut
