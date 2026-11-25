import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 26 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb26_ok : rb26.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
