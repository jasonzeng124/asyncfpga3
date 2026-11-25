import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 5 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb5_ok : rb5.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
