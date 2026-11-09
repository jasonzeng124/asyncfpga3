import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 24 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb24_ok : rb24.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
