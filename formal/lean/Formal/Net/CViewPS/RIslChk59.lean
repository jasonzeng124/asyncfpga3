import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 59 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb59_ok : rb59.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
