import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 9 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb9_ok : rb9.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
