import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 51 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb51_ok : rb51.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
