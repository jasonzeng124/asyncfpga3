import Formal.Net.CViewPS.IslandDefs

/-! Shard C: kernel check of island chunk 5. -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem isl5_ok : isl5.all entryOK = true := by decide +kernel

end Formal.Net.CViewPS
