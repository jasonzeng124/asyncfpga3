import Formal.Net.CViewPS.IslandDefs

/-! Shard C: kernel check of island chunk 7. -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem isl7_ok : isl7.all entryOK = true := by decide +kernel

end Formal.Net.CViewPS
