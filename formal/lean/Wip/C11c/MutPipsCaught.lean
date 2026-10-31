import Formal.Net.FasmLink.LinkArb
import Wip.C11c.MutPips
open Formal.Net.FasmLink
/-- negative control (pin A1 (was {'k': 'port', 'name': 'r1', 'site': 'IOB_X0Y91'}): INT_R_X29Y95.IMUX7.NW2END_S0_0 -> INT_R_X29Y95.IMUX7.FAN_): the defect in the bits is caught -/
theorem caught : ¬ (LinkArb.design Wip.C11c.MutPips.net Wip.C11c.MutPips.ports Wip.C11c.MutPips.rho).Correct :=
  Design.not_correct _ (by decide)
