import Formal.Net.Fasm.CePair
import Wip.C11b.MutPips
open Formal.Net.Fasm.CePair
/-- the defect is caught -/
theorem caught : ¬ Spec Wip.C11b.MutPips.net Wip.C11b.MutPips.ports := by decide
