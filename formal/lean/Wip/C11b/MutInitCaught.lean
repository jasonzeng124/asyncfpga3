import Formal.Net.Fasm.CePair
import Wip.C11b.MutInit
open Formal.Net.Fasm.CePair
/-- the defect is caught -/
theorem caught : ¬ Spec Wip.C11b.MutInit.net Wip.C11b.MutInit.ports := by decide
