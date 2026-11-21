import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 27 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb27_ok : rb27.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
