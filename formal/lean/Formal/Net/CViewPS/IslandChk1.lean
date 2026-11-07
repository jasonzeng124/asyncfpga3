import Formal.Net.CViewPS.IslandDefs

/-! Shard C: kernel check of island chunk 1. -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem isl1_ok : isl1.all entryOK = true := by decide +kernel

end Formal.Net.CViewPS
