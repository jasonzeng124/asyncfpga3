import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 39 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb39_ok : rb39.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
