import Formal.Net.CViewPS.RIslDefs

/-! Shard C: kernel check of reset-island block 56 (generated). -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem rb56_ok : rb56.all rEntryOK = true := by decide +kernel

end Formal.Net.CViewPS
