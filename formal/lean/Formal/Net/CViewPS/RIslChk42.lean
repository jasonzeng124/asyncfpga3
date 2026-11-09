import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 42 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb42_ok : rb42.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
