import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 55 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb55_ok : rb55.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
