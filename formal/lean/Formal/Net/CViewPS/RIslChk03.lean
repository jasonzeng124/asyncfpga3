import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 3 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb3_ok : rb3.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
