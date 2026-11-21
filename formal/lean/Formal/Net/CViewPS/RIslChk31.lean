import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 31 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb31_ok : rb31.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
