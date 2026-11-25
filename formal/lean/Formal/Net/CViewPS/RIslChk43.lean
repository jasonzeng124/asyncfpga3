import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 43 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb43_ok : rb43.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
