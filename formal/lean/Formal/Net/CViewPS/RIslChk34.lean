import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 34 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb34_ok : rb34.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
