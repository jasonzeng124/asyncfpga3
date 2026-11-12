import Formal.Net.FasmLink.LinkArb
import Wip.C11c.MutInit
open Formal.Net.FasmLink
/-- negative control (CLBLM_R_X29Y95.SLICEM_X0.ALUT INIT bit 36 flipped): the defect in the bits is caught -/
theorem caught : ¬ (LinkArb.design Wip.C11c.MutInit.net Wip.C11c.MutInit.ports Wip.C11c.MutInit.rho).Correct :=
  Design.not_correct _ (by decide)
