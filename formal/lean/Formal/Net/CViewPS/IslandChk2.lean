import Formal.Net.CViewPS.IslandDefs

/-! Shard C: kernel check of island chunk 2. -/

namespace Formal.Net.CViewPS

set_option maxRecDepth 100000 in
theorem isl2_ok : isl2.all entryOK = true := by decide +kernel

end Formal.Net.CViewPS
