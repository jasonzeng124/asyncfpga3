import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 48 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb48_ok : rb48.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
