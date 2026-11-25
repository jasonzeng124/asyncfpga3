import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 0 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb0_ok : rb0.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
